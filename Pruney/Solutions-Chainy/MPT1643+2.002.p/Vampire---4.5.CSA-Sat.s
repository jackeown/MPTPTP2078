%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:03 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u32,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,sK1)
    | m1_subset_1(sK2(u1_struct_0(sK0),X0,sK1),u1_struct_0(sK0)) )).

cnf(u34,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | m1_subset_1(sK2(X0,X1,X2),X0)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u27,axiom,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X0,X1) )).

cnf(u25,axiom,
    ( ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u26,axiom,
    ( ~ r2_hidden(X3,X0)
    | r2_hidden(X3,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u28,axiom,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | r1_tarski(X0,X1) )).

cnf(u30,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u31,axiom,
    ( ~ r1_tarski(X0,X2)
    | r2_hidden(sK3(X0,X1),X2)
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:36:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (15127)WARNING: option uwaf not known.
% 0.19/0.46  % (15129)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.19/0.46  % (15137)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.19/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.46  % (15137)# SZS output start Saturation.
% 0.19/0.46  cnf(u20,negated_conjecture,
% 0.19/0.46      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.19/0.46  
% 0.19/0.46  cnf(u32,negated_conjecture,
% 0.19/0.46      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,sK1) | m1_subset_1(sK2(u1_struct_0(sK0),X0,sK1),u1_struct_0(sK0))).
% 0.19/0.46  
% 0.19/0.46  cnf(u34,negated_conjecture,
% 0.19/0.46      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,sK1) | r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0)).
% 0.19/0.46  
% 0.19/0.46  cnf(u23,axiom,
% 0.19/0.46      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1,X2),X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.19/0.46  
% 0.19/0.46  cnf(u24,axiom,
% 0.19/0.46      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.19/0.46  
% 0.19/0.46  cnf(u27,axiom,
% 0.19/0.46      r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u25,axiom,
% 0.19/0.46      ~r2_hidden(sK2(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.19/0.46  
% 0.19/0.46  cnf(u26,axiom,
% 0.19/0.46      ~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u28,axiom,
% 0.19/0.46      ~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u30,axiom,
% 0.19/0.46      r1_tarski(X0,X0)).
% 0.19/0.46  
% 0.19/0.46  cnf(u31,axiom,
% 0.19/0.46      ~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)).
% 0.19/0.46  
% 0.19/0.46  % (15137)# SZS output end Saturation.
% 0.19/0.46  % (15137)------------------------------
% 0.19/0.46  % (15137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (15137)Termination reason: Satisfiable
% 0.19/0.46  
% 0.19/0.46  % (15137)Memory used [KB]: 5373
% 0.19/0.46  % (15137)Time elapsed: 0.058 s
% 0.19/0.46  % (15137)------------------------------
% 0.19/0.46  % (15137)------------------------------
% 0.19/0.46  % (15116)Success in time 0.124 s
%------------------------------------------------------------------------------
