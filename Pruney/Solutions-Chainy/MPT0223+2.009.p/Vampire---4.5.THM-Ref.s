%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:51 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 102 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f85,f99,f103,f109])).

fof(f109,plain,(
    ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f48,f98,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f98,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_7
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f48,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f103,plain,
    ( spl2_1
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl2_1
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f52,f94,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f94,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_6
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f52,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f99,plain,
    ( ~ spl2_6
    | spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f90,f81,f96,f92])).

fof(f81,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f90,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f83,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f83,plain,
    ( r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f85,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f69,f55,f81])).

fof(f55,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f69,plain,
    ( r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f36,f57])).

fof(f57,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f44,f55])).

fof(f44,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f53,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:41:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (12928)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (12938)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (12949)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (12931)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (12940)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (12932)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (12949)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f110,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(avatar_sat_refutation,[],[f53,f58,f85,f99,f103,f109])).
% 1.29/0.54  fof(f109,plain,(
% 1.29/0.54    ~spl2_7),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f105])).
% 1.29/0.54  fof(f105,plain,(
% 1.29/0.54    $false | ~spl2_7),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f48,f98,f35])).
% 1.29/0.54  fof(f35,plain,(
% 1.29/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f20])).
% 1.29/0.54  fof(f20,plain,(
% 1.29/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.29/0.54    inference(ennf_transformation,[],[f4])).
% 1.29/0.54  fof(f4,axiom,(
% 1.29/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.29/0.54  fof(f98,plain,(
% 1.29/0.54    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | ~spl2_7),
% 1.29/0.54    inference(avatar_component_clause,[],[f96])).
% 1.29/0.54  fof(f96,plain,(
% 1.29/0.54    spl2_7 <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.29/0.54  fof(f48,plain,(
% 1.29/0.54    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.29/0.54    inference(equality_resolution,[],[f38])).
% 1.29/0.54  fof(f38,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 1.29/0.54    inference(cnf_transformation,[],[f21])).
% 1.29/0.54  fof(f21,plain,(
% 1.29/0.54    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.29/0.54    inference(ennf_transformation,[],[f13])).
% 1.29/0.54  fof(f13,axiom,(
% 1.29/0.54    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 1.29/0.54  fof(f103,plain,(
% 1.29/0.54    spl2_1 | spl2_6),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f100])).
% 1.29/0.54  fof(f100,plain,(
% 1.29/0.54    $false | (spl2_1 | spl2_6)),
% 1.29/0.54    inference(unit_resulting_resolution,[],[f52,f94,f34])).
% 1.29/0.54  fof(f34,plain,(
% 1.29/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.29/0.54    inference(cnf_transformation,[],[f19])).
% 1.29/0.54  fof(f19,plain,(
% 1.29/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.29/0.54    inference(ennf_transformation,[],[f14])).
% 1.29/0.54  fof(f14,axiom,(
% 1.29/0.54    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.29/0.54  fof(f94,plain,(
% 1.29/0.54    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_6),
% 1.29/0.54    inference(avatar_component_clause,[],[f92])).
% 1.29/0.54  fof(f92,plain,(
% 1.29/0.54    spl2_6 <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.29/0.54  fof(f52,plain,(
% 1.29/0.54    sK0 != sK1 | spl2_1),
% 1.29/0.54    inference(avatar_component_clause,[],[f50])).
% 1.29/0.54  fof(f50,plain,(
% 1.29/0.54    spl2_1 <=> sK0 = sK1),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.29/0.54  fof(f99,plain,(
% 1.29/0.54    ~spl2_6 | spl2_7 | ~spl2_5),
% 1.29/0.54    inference(avatar_split_clause,[],[f90,f81,f96,f92])).
% 1.29/0.54  fof(f81,plain,(
% 1.29/0.54    spl2_5 <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.29/0.54  fof(f90,plain,(
% 1.29/0.54    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl2_5),
% 1.29/0.54    inference(superposition,[],[f83,f37])).
% 1.29/0.54  fof(f37,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  fof(f12,axiom,(
% 1.29/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.29/0.54  fof(f83,plain,(
% 1.29/0.54    r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~spl2_5),
% 1.29/0.54    inference(avatar_component_clause,[],[f81])).
% 1.29/0.54  fof(f85,plain,(
% 1.29/0.54    spl2_5 | ~spl2_2),
% 1.29/0.54    inference(avatar_split_clause,[],[f69,f55,f81])).
% 1.29/0.54  fof(f55,plain,(
% 1.29/0.54    spl2_2 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.29/0.54  fof(f69,plain,(
% 1.29/0.54    r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~spl2_2),
% 1.29/0.54    inference(trivial_inequality_removal,[],[f65])).
% 1.29/0.54  fof(f65,plain,(
% 1.29/0.54    k1_tarski(sK0) != k1_tarski(sK0) | r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~spl2_2),
% 1.29/0.54    inference(superposition,[],[f36,f57])).
% 1.29/0.54  fof(f57,plain,(
% 1.29/0.54    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~spl2_2),
% 1.29/0.54    inference(avatar_component_clause,[],[f55])).
% 1.29/0.54  fof(f36,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  fof(f58,plain,(
% 1.29/0.54    spl2_2),
% 1.29/0.54    inference(avatar_split_clause,[],[f44,f55])).
% 1.29/0.54  fof(f44,plain,(
% 1.29/0.54    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.29/0.54    inference(definition_unfolding,[],[f24,f33])).
% 1.29/0.54  fof(f33,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f8])).
% 1.29/0.54  fof(f8,axiom,(
% 1.29/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.29/0.54  fof(f24,plain,(
% 1.29/0.54    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.29/0.54    inference(cnf_transformation,[],[f18])).
% 1.29/0.54  fof(f18,plain,(
% 1.29/0.54    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.29/0.54    inference(ennf_transformation,[],[f16])).
% 1.29/0.54  fof(f16,negated_conjecture,(
% 1.29/0.54    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.29/0.54    inference(negated_conjecture,[],[f15])).
% 1.29/0.54  fof(f15,conjecture,(
% 1.29/0.54    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.29/0.54  fof(f53,plain,(
% 1.29/0.54    ~spl2_1),
% 1.29/0.54    inference(avatar_split_clause,[],[f25,f50])).
% 1.29/0.54  fof(f25,plain,(
% 1.29/0.54    sK0 != sK1),
% 1.29/0.54    inference(cnf_transformation,[],[f18])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (12949)------------------------------
% 1.29/0.54  % (12949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (12949)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (12949)Memory used [KB]: 10746
% 1.29/0.54  % (12949)Time elapsed: 0.079 s
% 1.29/0.54  % (12949)------------------------------
% 1.29/0.54  % (12949)------------------------------
% 1.29/0.54  % (12957)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (12927)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (12925)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (12919)Success in time 0.171 s
%------------------------------------------------------------------------------
