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
% DateTime   : Thu Dec  3 12:43:54 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 171 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  129 ( 304 expanded)
%              Number of equality atoms :   46 ( 131 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f112,f248,f432])).

fof(f432,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | spl2_5 ),
    inference(trivial_inequality_removal,[],[f422])).

fof(f422,plain,
    ( sK0 != sK0
    | spl2_5 ),
    inference(superposition,[],[f247,f386])).

fof(f386,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f385,f44])).

fof(f44,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f385,plain,(
    k3_subset_1(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f381,f384])).

fof(f384,plain,(
    k1_xboole_0 = k3_subset_1(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f382,f34])).

% (31284)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f382,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f369,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f369,plain,(
    m1_subset_1(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f368,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f368,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
      | m1_subset_1(k2_xboole_0(X10,sK1),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f241,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f40,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f381,plain,(
    k2_xboole_0(sK0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f369,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f247,plain,
    ( sK0 != k2_xboole_0(sK0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl2_5
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f248,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f243,f245,f107,f103])).

fof(f103,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f107,plain,
    ( spl2_2
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f243,plain,
    ( sK0 != k2_xboole_0(sK0,sK1)
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f242,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f242,plain,
    ( sK0 != k2_xboole_0(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f239,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f239,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f100,f41])).

fof(f100,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f46,f97])).

fof(f97,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f37,f27])).

fof(f46,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f43,f44])).

fof(f43,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f28,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f112,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f105,f27])).

fof(f105,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f110,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f101,f107,f103])).

fof(f101,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f36,f97])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_vampire %s %d
% 0.16/0.37  % Computer   : n018.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % WCLimit    : 600
% 0.16/0.37  % DateTime   : Tue Dec  1 17:19:57 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.24/0.51  % (31292)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.24/0.51  % (31276)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.24/0.52  % (31276)Refutation found. Thanks to Tanya!
% 0.24/0.52  % SZS status Theorem for theBenchmark
% 0.24/0.54  % (31272)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.24/0.54  % SZS output start Proof for theBenchmark
% 0.24/0.54  fof(f435,plain,(
% 0.24/0.54    $false),
% 0.24/0.54    inference(avatar_sat_refutation,[],[f110,f112,f248,f432])).
% 0.24/0.54  fof(f432,plain,(
% 0.24/0.54    spl2_5),
% 0.24/0.54    inference(avatar_contradiction_clause,[],[f431])).
% 0.24/0.54  fof(f431,plain,(
% 0.24/0.54    $false | spl2_5),
% 0.24/0.54    inference(trivial_inequality_removal,[],[f422])).
% 0.24/0.54  fof(f422,plain,(
% 0.24/0.54    sK0 != sK0 | spl2_5),
% 0.24/0.54    inference(superposition,[],[f247,f386])).
% 0.24/0.54  fof(f386,plain,(
% 0.24/0.54    sK0 = k2_xboole_0(sK0,sK1)),
% 0.24/0.54    inference(forward_demodulation,[],[f385,f44])).
% 0.24/0.54  fof(f44,plain,(
% 0.24/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.24/0.54    inference(definition_unfolding,[],[f30,f42])).
% 0.24/0.54  fof(f42,plain,(
% 0.24/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.24/0.54    inference(definition_unfolding,[],[f32,f29])).
% 0.24/0.54  fof(f29,plain,(
% 0.24/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f5])).
% 0.24/0.54  fof(f5,axiom,(
% 0.24/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.24/0.54  fof(f32,plain,(
% 0.24/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.24/0.54    inference(cnf_transformation,[],[f13])).
% 0.24/0.54  fof(f13,axiom,(
% 0.24/0.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.24/0.54  fof(f30,plain,(
% 0.24/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.24/0.54    inference(cnf_transformation,[],[f6])).
% 0.24/0.54  fof(f6,axiom,(
% 0.24/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.24/0.54  fof(f385,plain,(
% 0.24/0.54    k3_subset_1(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK1)),
% 0.24/0.54    inference(backward_demodulation,[],[f381,f384])).
% 0.24/0.54  fof(f384,plain,(
% 0.24/0.54    k1_xboole_0 = k3_subset_1(sK0,k2_xboole_0(sK0,sK1))),
% 0.24/0.54    inference(forward_demodulation,[],[f382,f34])).
% 0.24/0.54  % (31284)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.24/0.54  fof(f34,plain,(
% 0.24/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.24/0.54    inference(cnf_transformation,[],[f3])).
% 0.24/0.54  fof(f3,axiom,(
% 0.24/0.54    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.24/0.54  fof(f382,plain,(
% 0.24/0.54    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k2_xboole_0(sK0,sK1))),
% 0.24/0.54    inference(resolution,[],[f369,f37])).
% 0.24/0.54  fof(f37,plain,(
% 0.24/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f18])).
% 0.24/0.54  fof(f18,plain,(
% 0.24/0.54    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.54    inference(ennf_transformation,[],[f7])).
% 0.24/0.54  fof(f7,axiom,(
% 0.24/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.24/0.54  fof(f369,plain,(
% 0.24/0.54    m1_subset_1(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.24/0.54    inference(resolution,[],[f368,f47])).
% 0.24/0.54  fof(f47,plain,(
% 0.24/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(forward_demodulation,[],[f45,f44])).
% 0.24/0.54  fof(f45,plain,(
% 0.24/0.54    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(definition_unfolding,[],[f31,f42])).
% 0.24/0.54  fof(f31,plain,(
% 0.24/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(cnf_transformation,[],[f8])).
% 0.24/0.54  fof(f8,axiom,(
% 0.24/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.24/0.54  fof(f368,plain,(
% 0.24/0.54    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(sK0)) | m1_subset_1(k2_xboole_0(X10,sK1),k1_zfmisc_1(sK0))) )),
% 0.24/0.54    inference(resolution,[],[f241,f27])).
% 0.24/0.54  fof(f27,plain,(
% 0.24/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.24/0.54    inference(cnf_transformation,[],[f26])).
% 0.24/0.54  fof(f26,plain,(
% 0.24/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f25])).
% 0.24/0.54  fof(f25,plain,(
% 0.24/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.24/0.54    introduced(choice_axiom,[])).
% 0.24/0.54  fof(f16,plain,(
% 0.24/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.54    inference(ennf_transformation,[],[f15])).
% 0.24/0.54  fof(f15,negated_conjecture,(
% 0.24/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.24/0.54    inference(negated_conjecture,[],[f14])).
% 0.24/0.54  fof(f14,conjecture,(
% 0.24/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.24/0.54  fof(f241,plain,(
% 0.24/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(duplicate_literal_removal,[],[f240])).
% 0.24/0.54  fof(f240,plain,(
% 0.24/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(superposition,[],[f40,f41])).
% 0.24/0.54  fof(f41,plain,(
% 0.24/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(cnf_transformation,[],[f24])).
% 0.24/0.54  fof(f24,plain,(
% 0.24/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.54    inference(flattening,[],[f23])).
% 0.24/0.54  fof(f23,plain,(
% 0.24/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.24/0.54    inference(ennf_transformation,[],[f12])).
% 0.24/0.54  fof(f12,axiom,(
% 0.24/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.24/0.54  fof(f40,plain,(
% 0.24/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(cnf_transformation,[],[f22])).
% 0.24/0.54  fof(f22,plain,(
% 0.24/0.54    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.54    inference(flattening,[],[f21])).
% 0.24/0.54  fof(f21,plain,(
% 0.24/0.54    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.24/0.54    inference(ennf_transformation,[],[f10])).
% 0.24/0.54  fof(f10,axiom,(
% 0.24/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.24/0.54  fof(f381,plain,(
% 0.24/0.54    k2_xboole_0(sK0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK0,sK1)))),
% 0.24/0.54    inference(resolution,[],[f369,f38])).
% 0.24/0.54  fof(f38,plain,(
% 0.24/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.24/0.54    inference(cnf_transformation,[],[f19])).
% 0.24/0.54  fof(f19,plain,(
% 0.24/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.54    inference(ennf_transformation,[],[f11])).
% 0.24/0.54  fof(f11,axiom,(
% 0.24/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.24/0.54  fof(f247,plain,(
% 0.24/0.54    sK0 != k2_xboole_0(sK0,sK1) | spl2_5),
% 0.24/0.54    inference(avatar_component_clause,[],[f245])).
% 0.24/0.54  fof(f245,plain,(
% 0.24/0.54    spl2_5 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.24/0.54  fof(f248,plain,(
% 0.24/0.54    ~spl2_1 | ~spl2_2 | ~spl2_5),
% 0.24/0.54    inference(avatar_split_clause,[],[f243,f245,f107,f103])).
% 0.24/0.54  fof(f103,plain,(
% 0.24/0.54    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.24/0.54  fof(f107,plain,(
% 0.24/0.54    spl2_2 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.24/0.54  fof(f243,plain,(
% 0.24/0.54    sK0 != k2_xboole_0(sK0,sK1) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.24/0.54    inference(forward_demodulation,[],[f242,f33])).
% 0.24/0.54  fof(f33,plain,(
% 0.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f1])).
% 0.24/0.54  fof(f1,axiom,(
% 0.24/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.24/0.54  fof(f242,plain,(
% 0.24/0.54    sK0 != k2_xboole_0(sK1,sK0) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.24/0.54    inference(forward_demodulation,[],[f239,f35])).
% 0.24/0.54  fof(f35,plain,(
% 0.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.24/0.54    inference(cnf_transformation,[],[f2])).
% 0.24/0.54  fof(f2,axiom,(
% 0.24/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.24/0.54  fof(f239,plain,(
% 0.24/0.54    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.24/0.54    inference(superposition,[],[f100,f41])).
% 0.24/0.54  fof(f100,plain,(
% 0.24/0.54    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 0.24/0.54    inference(backward_demodulation,[],[f46,f97])).
% 0.24/0.54  fof(f97,plain,(
% 0.24/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.24/0.54    inference(resolution,[],[f37,f27])).
% 0.24/0.54  fof(f46,plain,(
% 0.24/0.54    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.24/0.54    inference(backward_demodulation,[],[f43,f44])).
% 0.24/0.54  fof(f43,plain,(
% 0.24/0.54    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0)),
% 0.24/0.54    inference(definition_unfolding,[],[f28,f42])).
% 0.24/0.54  fof(f28,plain,(
% 0.24/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.24/0.54    inference(cnf_transformation,[],[f26])).
% 0.24/0.54  fof(f112,plain,(
% 0.24/0.54    spl2_1),
% 0.24/0.54    inference(avatar_contradiction_clause,[],[f111])).
% 0.24/0.54  fof(f111,plain,(
% 0.24/0.54    $false | spl2_1),
% 0.24/0.54    inference(resolution,[],[f105,f27])).
% 0.24/0.54  fof(f105,plain,(
% 0.24/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl2_1),
% 0.24/0.54    inference(avatar_component_clause,[],[f103])).
% 0.24/0.54  fof(f110,plain,(
% 0.24/0.54    ~spl2_1 | spl2_2),
% 0.24/0.54    inference(avatar_split_clause,[],[f101,f107,f103])).
% 0.24/0.54  fof(f101,plain,(
% 0.24/0.54    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.24/0.54    inference(superposition,[],[f36,f97])).
% 0.24/0.54  fof(f36,plain,(
% 0.24/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.54    inference(cnf_transformation,[],[f17])).
% 0.24/0.54  fof(f17,plain,(
% 0.24/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.54    inference(ennf_transformation,[],[f9])).
% 0.24/0.54  fof(f9,axiom,(
% 0.24/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.24/0.54  % SZS output end Proof for theBenchmark
% 0.24/0.54  % (31276)------------------------------
% 0.24/0.54  % (31276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.54  % (31276)Termination reason: Refutation
% 0.24/0.54  
% 0.24/0.54  % (31276)Memory used [KB]: 6524
% 0.24/0.54  % (31276)Time elapsed: 0.087 s
% 0.24/0.54  % (31276)------------------------------
% 0.24/0.54  % (31276)------------------------------
% 0.24/0.54  % (31263)Success in time 0.158 s
%------------------------------------------------------------------------------
