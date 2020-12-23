%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:25 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   45 (  45 expanded)
%              Depth                    :    0
%              Number of atoms          :   87 (  87 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u244,negated_conjecture,(
    k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK2,sK3) )).

tff(u243,axiom,(
    ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

tff(u242,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3) )).

tff(u241,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3) )).

tff(u240,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK3,sK2) = k7_domain_1(u1_struct_0(sK0),sK3,sK2) )).

tff(u239,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK2,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK2) )).

tff(u238,negated_conjecture,(
    sK2 = sK4 )).

tff(u237,negated_conjecture,(
    sK3 = sK5 )).

tff(u236,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2) ) )).

tff(u235,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3) ) )).

tff(u234,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_tarski(X1,sK2) = k7_domain_1(u1_struct_0(sK0),X1,sK2) ) )).

tff(u233,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0) ) )).

tff(u232,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),sK2,X1) = k2_tarski(sK2,X1) ) )).

tff(u231,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0) ) )).

tff(u230,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u229,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u228,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK0)) )).

tff(u227,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u226,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u225,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u224,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u223,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u222,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u221,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u220,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u219,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u218,axiom,(
    ! [X1,X0,X2] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) )).

tff(u217,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

tff(u216,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) )).

tff(u215,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u214,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u213,axiom,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u212,negated_conjecture,
    ( ~ ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK1) )).

tff(u211,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u210,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u209,negated_conjecture,
    ( ~ ~ l1_struct_0(sK1)
    | ~ l1_orders_2(sK1) )).

tff(u208,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u207,axiom,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u206,negated_conjecture,(
    v2_lattice3(sK0) )).

tff(u205,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u204,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u203,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u202,negated_conjecture,(
    v4_yellow_0(sK1,sK0) )).

tff(u201,negated_conjecture,(
    v5_yellow_0(sK1,sK0) )).

tff(u200,negated_conjecture,(
    m1_yellow_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (13455)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % (13447)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (13447)Refutation not found, incomplete strategy% (13447)------------------------------
% 0.20/0.45  % (13447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (13447)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (13447)Memory used [KB]: 6396
% 0.20/0.45  % (13447)Time elapsed: 0.068 s
% 0.20/0.45  % (13447)------------------------------
% 0.20/0.45  % (13447)------------------------------
% 0.20/0.45  % (13454)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (13442)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (13453)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (13449)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (13452)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (13456)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (13453)Refutation not found, incomplete strategy% (13453)------------------------------
% 0.20/0.47  % (13453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (13453)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (13453)Memory used [KB]: 10746
% 0.20/0.47  % (13453)Time elapsed: 0.065 s
% 0.20/0.47  % (13453)------------------------------
% 0.20/0.47  % (13453)------------------------------
% 0.20/0.47  % (13446)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (13448)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (13457)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (13446)Refutation not found, incomplete strategy% (13446)------------------------------
% 0.20/0.47  % (13446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (13446)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (13446)Memory used [KB]: 6140
% 0.20/0.47  % (13446)Time elapsed: 0.062 s
% 0.20/0.47  % (13446)------------------------------
% 0.20/0.47  % (13446)------------------------------
% 0.20/0.47  % (13445)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (13445)Refutation not found, incomplete strategy% (13445)------------------------------
% 0.20/0.48  % (13445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13445)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (13445)Memory used [KB]: 1663
% 0.20/0.48  % (13445)Time elapsed: 0.071 s
% 0.20/0.48  % (13445)------------------------------
% 0.20/0.48  % (13445)------------------------------
% 0.20/0.49  % (13450)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (13451)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (13443)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (13458)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (13458)# SZS output start Saturation.
% 0.20/0.50  tff(u244,negated_conjecture,
% 0.20/0.50      (k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK2,sK3))).
% 0.20/0.50  
% 0.20/0.50  tff(u243,axiom,
% 0.20/0.50      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u242,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3)))).
% 0.20/0.50  
% 0.20/0.50  tff(u241,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3)))).
% 0.20/0.50  
% 0.20/0.50  tff(u240,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k2_tarski(sK3,sK2) = k7_domain_1(u1_struct_0(sK0),sK3,sK2)))).
% 0.20/0.50  
% 0.20/0.50  tff(u239,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k2_tarski(sK2,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK2)))).
% 0.20/0.50  
% 0.20/0.50  tff(u238,negated_conjecture,
% 0.20/0.50      (sK2 = sK4)).
% 0.20/0.50  
% 0.20/0.50  tff(u237,negated_conjecture,
% 0.20/0.50      (sK3 = sK5)).
% 0.20/0.50  
% 0.20/0.50  tff(u236,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X3, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u235,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u234,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k2_tarski(X1,sK2) = k7_domain_1(u1_struct_0(sK0),X1,sK2))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u233,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u232,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK2,X1) = k2_tarski(sK2,X1))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u231,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u230,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.50  
% 0.20/0.50  tff(u229,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.20/0.50  
% 0.20/0.50  tff(u228,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u227,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u226,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u225,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u224,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u223,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u222,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u221,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u220,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u219,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u218,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u217,negated_conjecture,
% 0.20/0.50      ((~v1_xboole_0(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u216,axiom,
% 0.20/0.50      (![X1, X0] : ((r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u215,negated_conjecture,
% 0.20/0.50      ~v2_struct_0(sK1)).
% 0.20/0.50  
% 0.20/0.50  tff(u214,negated_conjecture,
% 0.20/0.50      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u213,axiom,
% 0.20/0.50      (![X0] : ((v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u212,negated_conjecture,
% 0.20/0.50      ((~~l1_struct_0(sK1)) | ~l1_struct_0(sK1))).
% 0.20/0.50  
% 0.20/0.50  tff(u211,axiom,
% 0.20/0.50      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u210,negated_conjecture,
% 0.20/0.50      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u209,negated_conjecture,
% 0.20/0.50      ((~~l1_struct_0(sK1)) | ~l1_orders_2(sK1))).
% 0.20/0.50  
% 0.20/0.50  tff(u208,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u207,axiom,
% 0.20/0.50      (![X0] : ((~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u206,negated_conjecture,
% 0.20/0.50      v2_lattice3(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u205,negated_conjecture,
% 0.20/0.50      v3_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u204,negated_conjecture,
% 0.20/0.50      v4_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u203,negated_conjecture,
% 0.20/0.50      v5_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u202,negated_conjecture,
% 0.20/0.50      v4_yellow_0(sK1,sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u201,negated_conjecture,
% 0.20/0.50      v5_yellow_0(sK1,sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u200,negated_conjecture,
% 0.20/0.50      m1_yellow_0(sK1,sK0)).
% 0.20/0.50  
% 0.20/0.50  % (13458)# SZS output end Saturation.
% 0.20/0.50  % (13458)------------------------------
% 0.20/0.50  % (13458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13458)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (13458)Memory used [KB]: 6268
% 0.20/0.50  % (13458)Time elapsed: 0.103 s
% 0.20/0.50  % (13458)------------------------------
% 0.20/0.50  % (13458)------------------------------
% 0.20/0.50  % (13441)Success in time 0.146 s
%------------------------------------------------------------------------------
