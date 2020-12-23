%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :    2 (   2 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    2 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u17,negated_conjecture,(
    k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) )).

tff(u16,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (12245)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (12247)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (12247)# SZS output start Saturation.
% 0.20/0.47  tff(u17,negated_conjecture,
% 0.20/0.47      (k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u16,axiom,
% 0.20/0.47      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.20/0.47  
% 0.20/0.47  % (12247)# SZS output end Saturation.
% 0.20/0.47  % (12247)------------------------------
% 0.20/0.47  % (12247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12247)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (12247)Memory used [KB]: 6012
% 0.20/0.47  % (12247)Time elapsed: 0.031 s
% 0.20/0.47  % (12247)------------------------------
% 0.20/0.47  % (12247)------------------------------
% 0.20/0.47  % (12249)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (12250)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (12250)Refutation not found, incomplete strategy% (12250)------------------------------
% 0.20/0.47  % (12250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12250)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (12250)Memory used [KB]: 6012
% 0.20/0.47  % (12250)Time elapsed: 0.060 s
% 0.20/0.47  % (12250)------------------------------
% 0.20/0.47  % (12250)------------------------------
% 0.20/0.47  % (12244)Success in time 0.112 s
%------------------------------------------------------------------------------
