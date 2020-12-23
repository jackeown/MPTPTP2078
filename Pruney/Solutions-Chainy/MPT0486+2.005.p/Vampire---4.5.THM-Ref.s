%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  40 expanded)
%              Number of equality atoms :   25 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f25])).

fof(f25,plain,(
    spl0_1 ),
    inference(avatar_contradiction_clause,[],[f24])).

fof(f24,plain,
    ( $false
    | spl0_1 ),
    inference(subsumption_resolution,[],[f23,f18])).

fof(f18,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | spl0_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl0_1
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).

fof(f23,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k6_relat_1(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f20,f11])).

fof(f11,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f13,f10])).

fof(f10,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f19,plain,(
    ~ spl0_1 ),
    inference(avatar_split_clause,[],[f9,f16])).

fof(f9,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f5])).

fof(f5,negated_conjecture,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (10741)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.41  % (10741)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f19,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    spl0_1),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f24])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    $false | spl0_1),
% 0.21/0.41    inference(subsumption_resolution,[],[f23,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    k1_xboole_0 != k6_relat_1(k1_xboole_0) | spl0_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    spl0_1 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.41    inference(equality_resolution,[],[f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 != X0 | k6_relat_1(X0) = k1_xboole_0) )),
% 0.21/0.41    inference(superposition,[],[f20,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k1_xboole_0) )),
% 0.21/0.41    inference(resolution,[],[f13,f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(flattening,[],[f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ~spl0_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f9,f16])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 0.21/0.41    inference(flattening,[],[f5])).
% 0.21/0.41  fof(f5,negated_conjecture,(
% 0.21/0.41    ~k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.41    inference(negated_conjecture,[],[f4])).
% 0.21/0.41  fof(f4,conjecture,(
% 0.21/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (10741)------------------------------
% 0.21/0.41  % (10741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (10741)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (10741)Memory used [KB]: 10490
% 0.21/0.42  % (10741)Time elapsed: 0.005 s
% 0.21/0.42  % (10741)------------------------------
% 0.21/0.42  % (10741)------------------------------
% 0.21/0.42  % (10736)Success in time 0.062 s
%------------------------------------------------------------------------------
