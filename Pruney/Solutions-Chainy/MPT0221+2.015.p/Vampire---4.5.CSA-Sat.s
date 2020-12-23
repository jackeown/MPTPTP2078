%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:47 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u38,axiom,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 )).

cnf(u28,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u36,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )).

cnf(u37,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u53,axiom,
    ( r2_hidden(sK3(X1,X1),X1)
    | r1_xboole_0(X1,X1) )).

cnf(u35,axiom,
    ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u32,axiom,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u46,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u47,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u31,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X2,X0) )).

cnf(u33,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u65,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

cnf(u29,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u56,axiom,
    ( k1_xboole_0 != X2
    | ~ r2_hidden(X3,X2) )).

cnf(u51,axiom,
    ( k1_xboole_0 != k3_xboole_0(X2,X3)
    | ~ r2_hidden(X4,k3_xboole_0(X2,X3)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:56:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (3062)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.43  % (3062)Refutation not found, incomplete strategy% (3062)------------------------------
% 0.20/0.43  % (3062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (3062)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (3062)Memory used [KB]: 10618
% 0.20/0.43  % (3062)Time elapsed: 0.036 s
% 0.20/0.44  % (3062)------------------------------
% 0.20/0.44  % (3062)------------------------------
% 0.20/0.46  % (3063)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (3055)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (3058)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (3052)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (3056)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (3055)Refutation not found, incomplete strategy% (3055)------------------------------
% 0.20/0.46  % (3055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3055)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (3055)Memory used [KB]: 6140
% 0.20/0.46  % (3055)Time elapsed: 0.052 s
% 0.20/0.46  % (3055)------------------------------
% 0.20/0.46  % (3055)------------------------------
% 0.20/0.46  % (3053)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (3052)# SZS output start Saturation.
% 0.20/0.46  cnf(u38,axiom,
% 0.20/0.46      r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0).
% 0.20/0.46  
% 0.20/0.46  cnf(u28,axiom,
% 0.20/0.46      r1_xboole_0(X0,k1_xboole_0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u36,axiom,
% 0.20/0.46      ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))).
% 0.20/0.46  
% 0.20/0.46  cnf(u37,axiom,
% 0.20/0.46      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.46  
% 0.20/0.46  cnf(u53,axiom,
% 0.20/0.46      r2_hidden(sK3(X1,X1),X1) | r1_xboole_0(X1,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u35,axiom,
% 0.20/0.46      r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u32,axiom,
% 0.20/0.46      r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u46,axiom,
% 0.20/0.46      ~r2_hidden(X0,k1_xboole_0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u47,axiom,
% 0.20/0.46      v1_xboole_0(k1_xboole_0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u31,axiom,
% 0.20/0.46      ~v1_xboole_0(X0) | ~r2_hidden(X2,X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u33,axiom,
% 0.20/0.46      k3_xboole_0(X0,X0) = X0).
% 0.20/0.46  
% 0.20/0.46  cnf(u65,negated_conjecture,
% 0.20/0.46      k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u29,axiom,
% 0.20/0.46      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u56,axiom,
% 0.20/0.46      k1_xboole_0 != X2 | ~r2_hidden(X3,X2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u51,axiom,
% 0.20/0.46      k1_xboole_0 != k3_xboole_0(X2,X3) | ~r2_hidden(X4,k3_xboole_0(X2,X3))).
% 0.20/0.46  
% 0.20/0.46  % (3052)# SZS output end Saturation.
% 0.20/0.46  % (3052)------------------------------
% 0.20/0.46  % (3052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3052)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (3052)Memory used [KB]: 1663
% 0.20/0.46  % (3052)Time elapsed: 0.063 s
% 0.20/0.46  % (3052)------------------------------
% 0.20/0.46  % (3052)------------------------------
% 0.20/0.46  % (3050)Success in time 0.111 s
%------------------------------------------------------------------------------
