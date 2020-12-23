%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:55 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    3 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,axiom,
    ( sP0(X0,X1)
    | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )).

cnf(u21,axiom,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X5),u1_struct_0(X0)) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X3),u1_struct_0(X0))
    | sP0(X0,X1) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK3(X1,X2,X0),u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2),u1_struct_0(X1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (2109)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.45  % (2109)# SZS output start Saturation.
% 0.20/0.45  cnf(u23,axiom,
% 0.20/0.45      sP0(X0,X1) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))).
% 0.20/0.45  
% 0.20/0.45  cnf(u21,axiom,
% 0.20/0.45      ~sP0(X0,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X5),u1_struct_0(X0))).
% 0.20/0.45  
% 0.20/0.45  cnf(u24,axiom,
% 0.20/0.45      ~m1_subset_1(X3,u1_struct_0(X0)) | m1_subset_1(sK2(X0,X1,X3),u1_struct_0(X0)) | sP0(X0,X1)).
% 0.20/0.45  
% 0.20/0.45  cnf(u29,axiom,
% 0.20/0.45      ~m1_subset_1(X0,u1_struct_0(X1)) | m1_subset_1(sK3(X1,X2,X0),u1_struct_0(X1)) | m1_subset_1(sK1(X1,X2),u1_struct_0(X1))).
% 0.20/0.45  
% 0.20/0.45  % (2109)# SZS output end Saturation.
% 0.20/0.45  % (2109)------------------------------
% 0.20/0.45  % (2109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (2109)Termination reason: Satisfiable
% 0.20/0.45  
% 0.20/0.45  % (2109)Memory used [KB]: 5373
% 0.20/0.45  % (2109)Time elapsed: 0.004 s
% 0.20/0.45  % (2109)------------------------------
% 0.20/0.45  % (2109)------------------------------
% 0.20/0.45  % (2087)Success in time 0.091 s
%------------------------------------------------------------------------------
