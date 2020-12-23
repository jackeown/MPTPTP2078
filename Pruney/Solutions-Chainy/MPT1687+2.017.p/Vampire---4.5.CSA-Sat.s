%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:21 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (6934)Termination reason: Refutation not found, incomplete strategy

tff(u77,axiom,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 )).

tff(u76,axiom,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 )).

tff(u75,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u74,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u73,negated_conjecture,
    ( ~ ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

tff(u72,negated_conjecture,(
    v1_funct_1(sK2) )).

tff(u71,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

tff(u70,negated_conjecture,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

tff(u69,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u68,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u67,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u66,negated_conjecture,(
    l1_struct_0(sK1) )).

tff(u65,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u64,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u63,negated_conjecture,(
    l1_orders_2(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:20:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (6939)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (6933)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (6932)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (6932)Refutation not found, incomplete strategy% (6932)------------------------------
% 0.22/0.47  % (6932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (6932)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (6932)Memory used [KB]: 1535
% 0.22/0.47  % (6932)Time elapsed: 0.051 s
% 0.22/0.47  % (6933)Refutation not found, incomplete strategy% (6933)------------------------------
% 0.22/0.47  % (6933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (6932)------------------------------
% 0.22/0.47  % (6932)------------------------------
% 0.22/0.47  % (6933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (6933)Memory used [KB]: 6140
% 0.22/0.47  % (6933)Time elapsed: 0.051 s
% 0.22/0.47  % (6933)------------------------------
% 0.22/0.47  % (6933)------------------------------
% 0.22/0.47  % (6934)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (6931)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (6938)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (6934)Refutation not found, incomplete strategy% (6934)------------------------------
% 0.22/0.48  % (6934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (6931)# SZS output start Saturation.
% 0.22/0.48  % (6934)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  tff(u77,axiom,
% 0.22/0.48      (![X0] : ((k2_relat_1(k6_partfun1(X0)) = X0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u76,axiom,
% 0.22/0.48      (![X0] : ((k1_relat_1(k6_partfun1(X0)) = X0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u75,axiom,
% 0.22/0.48      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u74,axiom,
% 0.22/0.48      v1_xboole_0(k1_xboole_0)).
% 0.22/0.48  
% 0.22/0.48  tff(u73,negated_conjecture,
% 0.22/0.48      ((~~v1_funct_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)))).
% 0.22/0.48  
% 0.22/0.48  tff(u72,negated_conjecture,
% 0.22/0.48      v1_funct_1(sK2)).
% 0.22/0.48  
% 0.22/0.48  tff(u71,negated_conjecture,
% 0.22/0.48      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u70,negated_conjecture,
% 0.22/0.48      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.22/0.48  
% 0.22/0.48  tff(u69,negated_conjecture,
% 0.22/0.48      ~v2_struct_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u68,negated_conjecture,
% 0.22/0.48      ~v2_struct_0(sK1)).
% 0.22/0.48  
% 0.22/0.48  tff(u67,negated_conjecture,
% 0.22/0.48      l1_struct_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u66,negated_conjecture,
% 0.22/0.48      l1_struct_0(sK1)).
% 0.22/0.48  
% 0.22/0.48  tff(u65,axiom,
% 0.22/0.48      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u64,negated_conjecture,
% 0.22/0.48      l1_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u63,negated_conjecture,
% 0.22/0.48      l1_orders_2(sK1)).
% 0.22/0.48  
% 0.22/0.48  % (6931)# SZS output end Saturation.
% 0.22/0.48  % (6931)------------------------------
% 0.22/0.48  % (6931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (6931)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (6931)Memory used [KB]: 6140
% 0.22/0.48  % (6931)Time elapsed: 0.061 s
% 0.22/0.48  % (6931)------------------------------
% 0.22/0.48  % (6931)------------------------------
% 0.22/0.48  % (6934)Memory used [KB]: 6140
% 0.22/0.48  % (6934)Time elapsed: 0.061 s
% 0.22/0.48  % (6934)------------------------------
% 0.22/0.48  % (6934)------------------------------
% 0.22/0.48  % (6942)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (6941)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (6928)Success in time 0.116 s
%------------------------------------------------------------------------------
