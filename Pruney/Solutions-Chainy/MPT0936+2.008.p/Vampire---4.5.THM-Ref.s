%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 183 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 263 expanded)
%              Number of equality atoms :   66 ( 184 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f59,f70,f82,f92,f96,f99,f101])).

fof(f101,plain,
    ( ~ spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f100,f67,f89])).

fof(f89,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f67,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f100,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f34,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f34,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f18,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f99,plain,
    ( ~ spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f98,f63,f89])).

fof(f63,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f34,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f96,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f16,f91])).

fof(f91,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f92,plain,
    ( ~ spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f86,f52,f89])).

fof(f52,plain,
    ( spl3_3
  <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f86,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(superposition,[],[f34,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f82,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f48,f67,f63])).

fof(f48,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

% (3821)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f75,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f20,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f70,plain,
    ( spl3_5
    | spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f61,f56,f67,f63])).

fof(f56,plain,
    ( spl3_4
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f61,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(superposition,[],[f58,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f58,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f59,plain,
    ( spl3_2
    | spl3_3
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f46,f42,f56,f52,f48])).

fof(f42,plain,
    ( spl3_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl3_1 ),
    inference(superposition,[],[f44,f23])).

fof(f44,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f42])).

fof(f40,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f39,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f28,f31,f32,f31])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f31])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f39,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k3_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f33,f35])).

fof(f33,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f15,f32,f32,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f15,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (3840)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (3824)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (3832)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (3822)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (3823)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (3818)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (3818)Refutation not found, incomplete strategy% (3818)------------------------------
% 0.22/0.53  % (3818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3818)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3818)Memory used [KB]: 1663
% 0.22/0.53  % (3818)Time elapsed: 0.113 s
% 0.22/0.53  % (3818)------------------------------
% 0.22/0.53  % (3818)------------------------------
% 0.22/0.53  % (3840)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (3819)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (3820)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f45,f59,f70,f82,f92,f96,f99,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~spl3_8 | ~spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f100,f67,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl3_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl3_6 <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl3_6),
% 0.22/0.53    inference(superposition,[],[f34,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f67])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f19,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f26,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~spl3_8 | ~spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f98,f63,f89])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl3_5 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.22/0.53    inference(superposition,[],[f34,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl3_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    $false | spl3_8),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f16,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ~spl3_8 | ~spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f86,f52,f89])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl3_3 <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.22/0.53    inference(superposition,[],[f34,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl3_5 | spl3_6 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f75,f48,f67,f63])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    spl3_2 <=> k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  % (3821)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl3_2),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl3_2),
% 0.22/0.53    inference(superposition,[],[f20,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f48])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    spl3_5 | spl3_6 | spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f61,f56,f67,f63])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl3_4 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl3_4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl3_4),
% 0.22/0.53    inference(superposition,[],[f58,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f56])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl3_2 | spl3_3 | ~spl3_4 | spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f42,f56,f52,f48])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    spl3_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl3_1),
% 0.22/0.53    inference(superposition,[],[f44,f23])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f42])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f42])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 0.22/0.53    inference(forward_demodulation,[],[f39,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f28,f31,f32,f31])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f17,f31])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k3_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 0.22/0.53    inference(forward_demodulation,[],[f33,f35])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 0.22/0.53    inference(definition_unfolding,[],[f15,f32,f32,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (3840)------------------------------
% 0.22/0.53  % (3840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3840)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (3840)Memory used [KB]: 10746
% 0.22/0.53  % (3840)Time elapsed: 0.116 s
% 0.22/0.53  % (3840)------------------------------
% 0.22/0.53  % (3840)------------------------------
% 0.22/0.54  % (3817)Success in time 0.173 s
%------------------------------------------------------------------------------
