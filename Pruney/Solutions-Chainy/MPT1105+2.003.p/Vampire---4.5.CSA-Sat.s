%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u9,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u12,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )).

cnf(u11,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u10,negated_conjecture,
    ( k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:56 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.42  % (20676)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (20676)# SZS output start Saturation.
% 0.21/0.42  cnf(u9,negated_conjecture,
% 0.21/0.42      l1_struct_0(sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u12,axiom,
% 0.21/0.42      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)).
% 0.21/0.42  
% 0.21/0.42  cnf(u11,axiom,
% 0.21/0.42      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.42  
% 0.21/0.42  cnf(u10,negated_conjecture,
% 0.21/0.42      k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  % (20676)# SZS output end Saturation.
% 0.21/0.42  % (20676)------------------------------
% 0.21/0.42  % (20676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (20676)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (20676)Memory used [KB]: 6012
% 0.21/0.42  % (20676)Time elapsed: 0.003 s
% 0.21/0.42  % (20676)------------------------------
% 0.21/0.42  % (20676)------------------------------
% 0.21/0.42  % (20671)Success in time 0.06 s
%------------------------------------------------------------------------------
