open Ensembles.ZF

let zf = zf_dehornoy;;

let x,y,x',y' =
  Metavar("x"),
  Metavar("y"),
  Metavar("x'"),
  Metavar("y'")

let vx,vy,vx',vy'=V x,V y, V x',V y'

let couple = Ensembles.ZF.of_string "C"
let singleton = Ensembles.ZF.of_string "S"
let parties = Ensembles.ZF.of_string "P"
(*
let prop_couple =
  formula_from_string "\\forall(x, \\forall(y, \\forall(x', \\forall(y', (x,y)=(x',y') <=> (x=x' \\land y=y')))))"
*)
(*        
        (?@(x, ?@(y, ?@(x', ?@(y',
                         (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy'])) <=>
                         ((vx)^=(vx') && (vy)^=(vy'))  
                        ))))) 
*)
(*let suffisant =
  (?@(x, ?@(y, ?@(x', ?@(y', 
                         ((vx)^=(vx') && (vy)^=(vy')) => 
                         (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                        )))))

let necessaire =
  TPFormule (?@(x, ?@(y, ?@(x', ?@(y', 
                                   ((vx)^=(vx') && (vy)^=(vy')) <= 
                                   (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                                  )))))	
let preuve_necessaire = 
  [
    (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']));

    (vx^=vy); (*hypothèse*)
    Operation(couple,[vx;vy]) ^= Operation(singleton,[Operation(singleton,[vx])]);
    ?&(z, Operation(couple,[vx';vy']) ^= Operation(singleton,[vz]));
    Operation(couple,[vx';vy']) ^= Operation(singleton,[vx']);
    vx'^=vy';
    Operation(singleton,[Operation(singleton,[vx])])^=  Operation(singleton,[Operation(singleton,[vx'])]);
    Operation(singleton,[vx])^=  Operation(singleton,[vx']);
    vx^=vx';
    vy^=vx && vx^=vx' && vx'^=vy';
    vy^=vy';

    vx ^!= vy;(*deuxieme hypothèse*)
    neg ( ?&(z, Operation(couple,[vx;vy]) ^= Operation(singleton, [vz]) ));
    neg ( ?&(z, Operation(couple,[vx';vy']) ^= Operation(singleton, [vz]) )); (*par argument précédent*)
    vx' ^!= vy';
    Operation(singleton,[vx]) &= Operation(couple,[vx;vy]);
    Operation(singleton,[vx]) &= Operation(couple,[vx';vy']);
    Operation(singleton,[vx]) ^= Operation(parties, [vx';vy']) || Operation(singleton,[vx]) ^=Operation(singleton,[vx']);
    neg (Operation(singleton,[vx]) ^= Operation(parties, [vx';vy'])); (*Card {x',y'} = 2*)
    Operation(singleton,[vx]) ^=Operation(singleton,[vx']);
    vx^=vx';
    Operation(parties, [vx;vy]) ^= Operation(parties, [vx';vy']) ;
    Operation(parties, [vx';vy']) ^= Operation(parties, [vx;vy']) ;
    vy &= Operation(parties,[vx;vy']);
    vy ^=vy';
    (*on rassemble*)
    vx^=vx' && vy^=vy';
    ((vx)^=(vx') && (vy)^=(vy')) <= 
    (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']));
    ?@(y', 
       ((vx)^=(vx') && (vy)^=(vy')) <= 
       (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
      );
    ?@(x', ?@(y', 
              ((vx)^=(vx') && (vy)^=(vy')) <= 
              (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
             ));
    ?@(y, ?@(x', ?@(y', 
                    ((vx)^=(vx') && (vy)^=(vy')) <= 
                    (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                   )));
    ?@(x, ?@(y, ?@(x', ?@(y', 
                          ((vx)^=(vx') && (vy)^=(vy')) <= 
                          (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                         ))));
  ]	
let preuve_suffisant = [((vx)^=(vx') && (vy)^=(vy')) =>
                        (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']));
                        ?@(y', 
                           ((vx)^=(vx') && (vy)^=(vy')) => 
                           (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                          );
                        ?@(x', ?@(y', 
                                  ((vx)^=(vx') && (vy)^=(vy')) => 
                                  (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                                 ));
                        ?@(y, ?@(x', ?@(y', 
                                        ((vx)^=(vx') && (vy)^=(vy')) => 
                                        (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                                       )));
                        (?@(x, ?@(y, ?@(x', ?@(y', 
                                               ((vx)^=(vx') && (vy)^=(vy')) => 
                                               (Operation(couple,[vx;vy]) ^= Operation(couple,[vx';vy']))
                                              )))))	
                       ]

let test =	
  verification_preuve ~theorie:zf ~hypotheses:[] ~theoreme:necessaire
    ~proof:(List.map (fun f -> TPFormule f) preuve_necessaire);;



let test1 =
  let x1 = Var 1
  in
  let vx = V x1
  in
  verification_preuve ~theorie:zf ~hypotheses:[] ~theoreme: (TPFormule(vy ^= vy))
    ~proof:[TPFormule((V x1) ^= (V x1)); 
            TPFormule((?@)(x1, vx ^= vx));
            TPFormule(((?@)(x1, vx ^= vx)) => (vy ^= vy));
            TPFormule(vy ^= vy) 
           ];;

let proposition1 =
  verification_preuve ~theorie:zf ~hypotheses:[]
    ~theoreme:(TPFormule(Formule_atomique(Relation(of_string("\\subset") ,[vx;vx])))) 
    ~proof:[TPFormule(Formule_atomique(Relation(of_string("\\subset") ,[vx;vx]))); ]
*)
