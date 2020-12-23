%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:08 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  133 ( 219 expanded)
%              Number of equality atoms :   51 (  87 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f59,f65,f71,f77,f91,f131,f249])).

fof(f249,plain,
    ( spl4_1
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl4_1
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f247])).

fof(f247,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | spl4_1
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f246,f87])).

fof(f87,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_8
  <=> sK2 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f246,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k3_xboole_0(sK2,sK3))
    | spl4_1
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f238,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f238,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK2))
    | spl4_1
    | ~ spl4_12 ),
    inference(superposition,[],[f42,f140])).

fof(f140,plain,
    ( ! [X2,X3] : k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3)) = k2_zfmisc_1(sK0,k3_xboole_0(X2,X3))
    | ~ spl4_12 ),
    inference(superposition,[],[f35,f127])).

fof(f127,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_12
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f42,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_1
  <=> k2_zfmisc_1(sK0,sK2) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f131,plain,
    ( spl4_12
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f130,f74,f125])).

fof(f74,plain,
    ( spl4_7
  <=> k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f130,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f129,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f129,plain,
    ( k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f119,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f119,plain,
    ( k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl4_7 ),
    inference(superposition,[],[f33,f76])).

fof(f76,plain,
    ( k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f91,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f90,f68,f85])).

fof(f68,plain,
    ( spl4_6
  <=> k3_xboole_0(sK2,sK3) = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f90,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f89,f26])).

fof(f89,plain,
    ( k3_xboole_0(sK2,sK3) = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f79,f25])).

fof(f79,plain,
    ( k3_xboole_0(sK2,sK3) = k5_xboole_0(sK2,k5_xboole_0(sK3,sK3))
    | ~ spl4_6 ),
    inference(superposition,[],[f33,f70])).

fof(f70,plain,
    ( k3_xboole_0(sK2,sK3) = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f77,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f72,f62,f74])).

fof(f62,plain,
    ( spl4_5
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f72,plain,
    ( k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f30,f64])).

fof(f64,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f71,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f66,f56,f68])).

fof(f56,plain,
    ( spl4_4
  <=> sK3 = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f66,plain,
    ( k3_xboole_0(sK2,sK3) = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3)
    | ~ spl4_4 ),
    inference(superposition,[],[f30,f58])).

fof(f58,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f65,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f60,f50,f62])).

fof(f50,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f60,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f52,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f52,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f54,f45,f56])).

fof(f45,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:05:10 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.43  % (21028)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.47  % (21030)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.48  % (21024)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.48  % (21029)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.49  % (21032)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.50  % (21034)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.50  % (21026)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.50  % (21023)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (21020)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.50  % (21025)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.51  % (21037)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.51  % (21027)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.51  % (21036)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.52  % (21021)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.52  % (21033)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.52  % (21022)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.53  % (21031)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.53  % (21035)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.53  % (21031)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f251,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(avatar_sat_refutation,[],[f43,f48,f53,f59,f65,f71,f77,f91,f131,f249])).
% 0.23/0.53  fof(f249,plain,(
% 0.23/0.53    spl4_1 | ~spl4_8 | ~spl4_12),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f248])).
% 0.23/0.53  fof(f248,plain,(
% 0.23/0.53    $false | (spl4_1 | ~spl4_8 | ~spl4_12)),
% 0.23/0.53    inference(trivial_inequality_removal,[],[f247])).
% 0.23/0.53  fof(f247,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | (spl4_1 | ~spl4_8 | ~spl4_12)),
% 0.23/0.53    inference(forward_demodulation,[],[f246,f87])).
% 0.23/0.53  fof(f87,plain,(
% 0.23/0.53    sK2 = k3_xboole_0(sK2,sK3) | ~spl4_8),
% 0.23/0.53    inference(avatar_component_clause,[],[f85])).
% 0.23/0.53  fof(f85,plain,(
% 0.23/0.53    spl4_8 <=> sK2 = k3_xboole_0(sK2,sK3)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.23/0.53  fof(f246,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k3_xboole_0(sK2,sK3)) | (spl4_1 | ~spl4_12)),
% 0.23/0.53    inference(forward_demodulation,[],[f238,f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.53  fof(f238,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK2)) | (spl4_1 | ~spl4_12)),
% 0.23/0.53    inference(superposition,[],[f42,f140])).
% 0.23/0.53  fof(f140,plain,(
% 0.23/0.53    ( ! [X2,X3] : (k3_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3)) = k2_zfmisc_1(sK0,k3_xboole_0(X2,X3))) ) | ~spl4_12),
% 0.23/0.53    inference(superposition,[],[f35,f127])).
% 0.23/0.53  fof(f127,plain,(
% 0.23/0.53    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_12),
% 0.23/0.53    inference(avatar_component_clause,[],[f125])).
% 0.23/0.53  fof(f125,plain,(
% 0.23/0.53    spl4_12 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) | spl4_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    spl4_1 <=> k2_zfmisc_1(sK0,sK2) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.53  fof(f131,plain,(
% 0.23/0.53    spl4_12 | ~spl4_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f130,f74,f125])).
% 0.23/0.53  fof(f74,plain,(
% 0.23/0.53    spl4_7 <=> k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.53  fof(f130,plain,(
% 0.23/0.53    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_7),
% 0.23/0.53    inference(forward_demodulation,[],[f129,f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.23/0.53  fof(f129,plain,(
% 0.23/0.53    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) | ~spl4_7),
% 0.23/0.53    inference(forward_demodulation,[],[f119,f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.23/0.53  fof(f119,plain,(
% 0.23/0.53    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | ~spl4_7),
% 0.23/0.53    inference(superposition,[],[f33,f76])).
% 0.23/0.53  fof(f76,plain,(
% 0.23/0.53    k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl4_7),
% 0.23/0.53    inference(avatar_component_clause,[],[f74])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.23/0.53  fof(f91,plain,(
% 0.23/0.53    spl4_8 | ~spl4_6),
% 0.23/0.53    inference(avatar_split_clause,[],[f90,f68,f85])).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    spl4_6 <=> k3_xboole_0(sK2,sK3) = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.53  fof(f90,plain,(
% 0.23/0.53    sK2 = k3_xboole_0(sK2,sK3) | ~spl4_6),
% 0.23/0.53    inference(forward_demodulation,[],[f89,f26])).
% 0.23/0.53  fof(f89,plain,(
% 0.23/0.53    k3_xboole_0(sK2,sK3) = k5_xboole_0(sK2,k1_xboole_0) | ~spl4_6),
% 0.23/0.53    inference(forward_demodulation,[],[f79,f25])).
% 0.23/0.53  fof(f79,plain,(
% 0.23/0.53    k3_xboole_0(sK2,sK3) = k5_xboole_0(sK2,k5_xboole_0(sK3,sK3)) | ~spl4_6),
% 0.23/0.53    inference(superposition,[],[f33,f70])).
% 0.23/0.53  fof(f70,plain,(
% 0.23/0.53    k3_xboole_0(sK2,sK3) = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3) | ~spl4_6),
% 0.23/0.53    inference(avatar_component_clause,[],[f68])).
% 0.23/0.53  fof(f77,plain,(
% 0.23/0.53    spl4_7 | ~spl4_5),
% 0.23/0.53    inference(avatar_split_clause,[],[f72,f62,f74])).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    spl4_5 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl4_5),
% 0.23/0.53    inference(superposition,[],[f30,f64])).
% 0.23/0.53  fof(f64,plain,(
% 0.23/0.53    sK1 = k2_xboole_0(sK0,sK1) | ~spl4_5),
% 0.23/0.53    inference(avatar_component_clause,[],[f62])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.23/0.53  fof(f71,plain,(
% 0.23/0.53    spl4_6 | ~spl4_4),
% 0.23/0.53    inference(avatar_split_clause,[],[f66,f56,f68])).
% 0.23/0.53  fof(f56,plain,(
% 0.23/0.53    spl4_4 <=> sK3 = k2_xboole_0(sK2,sK3)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    k3_xboole_0(sK2,sK3) = k5_xboole_0(k5_xboole_0(sK2,sK3),sK3) | ~spl4_4),
% 0.23/0.53    inference(superposition,[],[f30,f58])).
% 0.23/0.53  fof(f58,plain,(
% 0.23/0.53    sK3 = k2_xboole_0(sK2,sK3) | ~spl4_4),
% 0.23/0.53    inference(avatar_component_clause,[],[f56])).
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    spl4_5 | ~spl4_3),
% 0.23/0.53    inference(avatar_split_clause,[],[f60,f50,f62])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.53  fof(f60,plain,(
% 0.23/0.53    sK1 = k2_xboole_0(sK0,sK1) | ~spl4_3),
% 0.23/0.53    inference(resolution,[],[f52,f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.23/0.53    inference(avatar_component_clause,[],[f50])).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    spl4_4 | ~spl4_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f54,f45,f56])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    sK3 = k2_xboole_0(sK2,sK3) | ~spl4_2),
% 0.23/0.53    inference(resolution,[],[f47,f31])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f45])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    spl4_3),
% 0.23/0.53    inference(avatar_split_clause,[],[f22,f50])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    r1_tarski(sK0,sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.23/0.53    inference(flattening,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.23/0.53    inference(ennf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.23/0.53    inference(negated_conjecture,[],[f15])).
% 0.23/0.53  fof(f15,conjecture,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    spl4_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f23,f45])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    r1_tarski(sK2,sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f21])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ~spl4_1),
% 0.23/0.53    inference(avatar_split_clause,[],[f24,f40])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.23/0.53    inference(cnf_transformation,[],[f21])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (21031)------------------------------
% 0.23/0.53  % (21031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (21031)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (21031)Memory used [KB]: 10746
% 0.23/0.53  % (21031)Time elapsed: 0.099 s
% 0.23/0.53  % (21031)------------------------------
% 0.23/0.53  % (21031)------------------------------
% 0.23/0.53  % (21019)Success in time 0.16 s
%------------------------------------------------------------------------------
