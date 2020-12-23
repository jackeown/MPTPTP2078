%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:13 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u29,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u28,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X0),X1)
    | k1_xboole_0 = X0 )).

cnf(u18,axiom,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u19,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u16,axiom,
    ( ~ r2_hidden(X2,X0)
    | k1_xboole_0 = X0
    | k3_mcart_1(X2,X3,X4) != sK2(X0) )).

cnf(u17,axiom,
    ( ~ r2_hidden(X3,X0)
    | k1_xboole_0 = X0
    | k3_mcart_1(X2,X3,X4) != sK2(X0) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u30,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

cnf(u24,axiom,
    ( sK2(X0) != k3_mcart_1(X1,sK2(X0),X2)
    | k1_xboole_0 = X0 )).

cnf(u22,axiom,
    ( sK2(X0) != k3_mcart_1(sK2(X0),X1,X2)
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (23780)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (23784)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (23784)Refutation not found, incomplete strategy% (23784)------------------------------
% 0.21/0.47  % (23784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23792)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (23784)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.48  % (23784)Memory used [KB]: 10618
% 0.21/0.48  % (23784)Time elapsed: 0.060 s
% 0.21/0.48  % (23784)------------------------------
% 0.21/0.48  % (23784)------------------------------
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (23792)# SZS output start Saturation.
% 0.21/0.48  cnf(u29,negated_conjecture,
% 0.21/0.48      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.48  
% 0.21/0.48  cnf(u28,negated_conjecture,
% 0.21/0.48      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u20,axiom,
% 0.21/0.48      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0),X1) | k1_xboole_0 = X0).
% 0.21/0.48  
% 0.21/0.48  cnf(u18,axiom,
% 0.21/0.48      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 0.21/0.48  
% 0.21/0.48  cnf(u19,axiom,
% 0.21/0.48      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u16,axiom,
% 0.21/0.48      ~r2_hidden(X2,X0) | k1_xboole_0 = X0 | k3_mcart_1(X2,X3,X4) != sK2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u17,axiom,
% 0.21/0.48      ~r2_hidden(X3,X0) | k1_xboole_0 = X0 | k3_mcart_1(X2,X3,X4) != sK2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u27,negated_conjecture,
% 0.21/0.48      k1_xboole_0 = sK1).
% 0.21/0.48  
% 0.21/0.48  cnf(u30,negated_conjecture,
% 0.21/0.48      k1_xboole_0 != k1_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u24,axiom,
% 0.21/0.48      sK2(X0) != k3_mcart_1(X1,sK2(X0),X2) | k1_xboole_0 = X0).
% 0.21/0.48  
% 0.21/0.48  cnf(u22,axiom,
% 0.21/0.48      sK2(X0) != k3_mcart_1(sK2(X0),X1,X2) | k1_xboole_0 = X0).
% 0.21/0.48  
% 0.21/0.48  % (23792)# SZS output end Saturation.
% 0.21/0.48  % (23792)------------------------------
% 0.21/0.48  % (23792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23792)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (23792)Memory used [KB]: 1663
% 0.21/0.48  % (23792)Time elapsed: 0.062 s
% 0.21/0.48  % (23792)------------------------------
% 0.21/0.48  % (23792)------------------------------
% 0.21/0.48  % (23774)Success in time 0.121 s
%------------------------------------------------------------------------------
