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
% DateTime   : Thu Dec  3 12:45:52 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 243 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 479 expanded)
%              Number of equality atoms :   38 ( 210 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f756,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f388,f393,f430,f753])).

fof(f753,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f706,f715,f715,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f715,plain,
    ( ! [X0] : ~ r2_hidden(sK0,X0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f708,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f708,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f706,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f706,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f705,f434])).

fof(f434,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(k1_setfam_1(k1_xboole_0)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f77,f387])).

fof(f387,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl5_2
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f77,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_setfam_1(k1_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f20,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f20,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f705,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_tarski(k1_setfam_1(k1_xboole_0))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f698,f387])).

fof(f698,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_setfam_1(k1_xboole_0))))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f54,f436,f64])).

fof(f436,plain,
    ( ~ r2_hidden(sK0,k1_tarski(k1_setfam_1(k1_xboole_0)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f87,f387])).

fof(f87,plain,(
    ~ r2_hidden(sK0,k1_tarski(k1_setfam_1(k1_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f20,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f54,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f430,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f56,f421])).

fof(f421,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f383,f410])).

fof(f410,plain,
    ( sK0 = sK1(k1_tarski(sK0),sK0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f392,f52])).

fof(f392,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl5_3
  <=> r2_hidden(sK1(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f383,plain,
    ( ~ r1_tarski(sK0,sK1(k1_tarski(sK0),sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1(k1_tarski(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f393,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f378,f385,f390])).

fof(f378,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | r2_hidden(sK1(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    inference(resolution,[],[f376,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f376,plain,(
    ~ r1_tarski(sK0,k1_setfam_1(k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f20,f357,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f357,plain,(
    r1_tarski(k1_setfam_1(k1_tarski(sK0)),sK0) ),
    inference(forward_demodulation,[],[f354,f77])).

fof(f354,plain,(
    r1_tarski(k1_setfam_1(k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_setfam_1(k1_tarski(sK0))))),sK0) ),
    inference(superposition,[],[f254,f88])).

fof(f88,plain,(
    k1_tarski(k1_setfam_1(k1_tarski(sK0))) = k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f24])).

fof(f254,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),X0))),sK0) ),
    inference(unit_resulting_resolution,[],[f126,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f126,plain,(
    ! [X0] : r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),X0))) ),
    inference(unit_resulting_resolution,[],[f54,f97,f64])).

fof(f97,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),X0)) ),
    inference(unit_resulting_resolution,[],[f87,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f388,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f379,f385,f381])).

fof(f379,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r1_tarski(sK0,sK1(k1_tarski(sK0),sK0)) ),
    inference(resolution,[],[f376,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:58:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.52  % (2954)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (2953)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (2971)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (2952)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (2963)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (2980)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (2980)Refutation not found, incomplete strategy% (2980)------------------------------
% 0.22/0.54  % (2980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2978)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.54  % (2956)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.54  % (2951)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.29/0.55  % (2975)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.29/0.55  % (2960)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.55  % (2955)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.55  % (2966)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.55  % (2966)Refutation not found, incomplete strategy% (2966)------------------------------
% 1.29/0.55  % (2966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2974)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.55  % (2952)Refutation not found, incomplete strategy% (2952)------------------------------
% 1.29/0.55  % (2952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (2952)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2952)Memory used [KB]: 1663
% 1.29/0.55  % (2952)Time elapsed: 0.115 s
% 1.29/0.55  % (2952)------------------------------
% 1.29/0.55  % (2952)------------------------------
% 1.29/0.55  % (2965)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.29/0.55  % (2966)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2966)Memory used [KB]: 1663
% 1.29/0.55  % (2966)Time elapsed: 0.063 s
% 1.29/0.55  % (2966)------------------------------
% 1.29/0.55  % (2966)------------------------------
% 1.29/0.55  % (2961)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.55  % (2957)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.55  % (2959)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.29/0.55  % (2980)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (2980)Memory used [KB]: 6140
% 1.29/0.55  % (2980)Time elapsed: 0.127 s
% 1.29/0.55  % (2980)------------------------------
% 1.29/0.55  % (2980)------------------------------
% 1.29/0.56  % (2981)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.29/0.56  % (2970)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.29/0.56  % (2968)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.29/0.56  % (2970)Refutation not found, incomplete strategy% (2970)------------------------------
% 1.29/0.56  % (2970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (2970)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (2970)Memory used [KB]: 1663
% 1.29/0.56  % (2970)Time elapsed: 0.131 s
% 1.29/0.56  % (2970)------------------------------
% 1.29/0.56  % (2970)------------------------------
% 1.29/0.56  % (2982)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.56  % (2968)Refutation not found, incomplete strategy% (2968)------------------------------
% 1.29/0.56  % (2968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (2968)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (2968)Memory used [KB]: 10618
% 1.29/0.56  % (2968)Time elapsed: 0.130 s
% 1.29/0.56  % (2968)------------------------------
% 1.29/0.56  % (2968)------------------------------
% 1.29/0.56  % (2982)Refutation not found, incomplete strategy% (2982)------------------------------
% 1.29/0.56  % (2982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (2982)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (2982)Memory used [KB]: 1663
% 1.29/0.56  % (2982)Time elapsed: 0.130 s
% 1.29/0.56  % (2982)------------------------------
% 1.29/0.56  % (2982)------------------------------
% 1.29/0.56  % (2958)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.56  % (2973)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.56  % (2976)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.29/0.56  % (2969)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.56  % (2969)Refutation not found, incomplete strategy% (2969)------------------------------
% 1.49/0.56  % (2969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (2972)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.56  % (2967)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.49/0.57  % (2976)Refutation not found, incomplete strategy% (2976)------------------------------
% 1.49/0.57  % (2976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (2976)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (2976)Memory used [KB]: 10618
% 1.49/0.57  % (2976)Time elapsed: 0.142 s
% 1.49/0.57  % (2976)------------------------------
% 1.49/0.57  % (2976)------------------------------
% 1.49/0.57  % (2969)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (2969)Memory used [KB]: 1663
% 1.49/0.57  % (2969)Time elapsed: 0.141 s
% 1.49/0.57  % (2969)------------------------------
% 1.49/0.57  % (2969)------------------------------
% 1.49/0.57  % (2964)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.57  % (2964)Refutation not found, incomplete strategy% (2964)------------------------------
% 1.49/0.57  % (2964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (2964)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (2964)Memory used [KB]: 10618
% 1.49/0.57  % (2964)Time elapsed: 0.141 s
% 1.49/0.57  % (2964)------------------------------
% 1.49/0.57  % (2964)------------------------------
% 1.49/0.58  % (2979)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.58  % (2979)Refutation not found, incomplete strategy% (2979)------------------------------
% 1.49/0.58  % (2979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (2979)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (2979)Memory used [KB]: 6140
% 1.49/0.58  % (2979)Time elapsed: 0.152 s
% 1.49/0.58  % (2979)------------------------------
% 1.49/0.58  % (2979)------------------------------
% 1.49/0.58  % (2978)Refutation found. Thanks to Tanya!
% 1.49/0.58  % SZS status Theorem for theBenchmark
% 1.49/0.58  % SZS output start Proof for theBenchmark
% 1.49/0.58  fof(f756,plain,(
% 1.49/0.58    $false),
% 1.49/0.58    inference(avatar_sat_refutation,[],[f388,f393,f430,f753])).
% 1.49/0.58  fof(f753,plain,(
% 1.49/0.58    ~spl5_2),
% 1.49/0.58    inference(avatar_contradiction_clause,[],[f736])).
% 1.49/0.58  fof(f736,plain,(
% 1.49/0.58    $false | ~spl5_2),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f706,f715,f715,f64])).
% 1.49/0.58  fof(f64,plain,(
% 1.49/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.49/0.58    inference(equality_resolution,[],[f49])).
% 1.49/0.58  fof(f49,plain,(
% 1.49/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.49/0.58    inference(cnf_transformation,[],[f1])).
% 1.49/0.58  fof(f1,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.49/0.58  fof(f715,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(sK0,X0)) ) | ~spl5_2),
% 1.49/0.58    inference(forward_demodulation,[],[f708,f32])).
% 1.49/0.58  fof(f32,plain,(
% 1.49/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f3])).
% 1.49/0.58  fof(f3,axiom,(
% 1.49/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.49/0.58  fof(f708,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,k1_xboole_0))) ) | ~spl5_2),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f706,f65])).
% 1.49/0.58  fof(f65,plain,(
% 1.49/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.49/0.58    inference(equality_resolution,[],[f48])).
% 1.49/0.58  fof(f48,plain,(
% 1.49/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.49/0.58    inference(cnf_transformation,[],[f1])).
% 1.49/0.58  fof(f706,plain,(
% 1.49/0.58    r2_hidden(sK0,k1_xboole_0) | ~spl5_2),
% 1.49/0.58    inference(forward_demodulation,[],[f705,f434])).
% 1.49/0.58  fof(f434,plain,(
% 1.49/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(k1_setfam_1(k1_xboole_0))) | ~spl5_2),
% 1.49/0.58    inference(backward_demodulation,[],[f77,f387])).
% 1.49/0.58  fof(f387,plain,(
% 1.49/0.58    k1_xboole_0 = k1_tarski(sK0) | ~spl5_2),
% 1.49/0.58    inference(avatar_component_clause,[],[f385])).
% 1.49/0.58  fof(f385,plain,(
% 1.49/0.58    spl5_2 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.49/0.58  fof(f77,plain,(
% 1.49/0.58    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_setfam_1(k1_tarski(sK0))))),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f20,f24])).
% 1.49/0.58  fof(f24,plain,(
% 1.49/0.58    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f9])).
% 1.49/0.58  fof(f9,axiom,(
% 1.49/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.49/0.58  fof(f20,plain,(
% 1.49/0.58    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.49/0.58    inference(cnf_transformation,[],[f15])).
% 1.49/0.58  fof(f15,plain,(
% 1.49/0.58    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.49/0.58    inference(ennf_transformation,[],[f14])).
% 1.49/0.58  fof(f14,negated_conjecture,(
% 1.49/0.58    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.49/0.58    inference(negated_conjecture,[],[f13])).
% 1.49/0.58  fof(f13,conjecture,(
% 1.49/0.58    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.49/0.58  fof(f705,plain,(
% 1.49/0.58    r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_tarski(k1_setfam_1(k1_xboole_0)))) | ~spl5_2),
% 1.49/0.58    inference(forward_demodulation,[],[f698,f387])).
% 1.49/0.58  fof(f698,plain,(
% 1.49/0.58    r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_setfam_1(k1_xboole_0)))) | ~spl5_2),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f54,f436,f64])).
% 1.49/0.58  fof(f436,plain,(
% 1.49/0.58    ~r2_hidden(sK0,k1_tarski(k1_setfam_1(k1_xboole_0))) | ~spl5_2),
% 1.49/0.58    inference(backward_demodulation,[],[f87,f387])).
% 1.49/0.58  fof(f87,plain,(
% 1.49/0.58    ~r2_hidden(sK0,k1_tarski(k1_setfam_1(k1_tarski(sK0))))),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f20,f52])).
% 1.49/0.58  fof(f52,plain,(
% 1.49/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.49/0.58    inference(equality_resolution,[],[f29])).
% 1.49/0.58  fof(f29,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f5])).
% 1.49/0.58  fof(f5,axiom,(
% 1.49/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.49/0.58  fof(f54,plain,(
% 1.49/0.58    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.49/0.58    inference(equality_resolution,[],[f53])).
% 1.49/0.58  fof(f53,plain,(
% 1.49/0.58    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.49/0.58    inference(equality_resolution,[],[f28])).
% 1.49/0.58  fof(f28,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f5])).
% 1.49/0.58  fof(f430,plain,(
% 1.49/0.58    spl5_1 | ~spl5_3),
% 1.49/0.58    inference(avatar_contradiction_clause,[],[f425])).
% 1.49/0.58  fof(f425,plain,(
% 1.49/0.58    $false | (spl5_1 | ~spl5_3)),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f56,f421])).
% 1.49/0.58  fof(f421,plain,(
% 1.49/0.58    ~r1_tarski(sK0,sK0) | (spl5_1 | ~spl5_3)),
% 1.49/0.58    inference(backward_demodulation,[],[f383,f410])).
% 1.49/0.58  fof(f410,plain,(
% 1.49/0.58    sK0 = sK1(k1_tarski(sK0),sK0) | ~spl5_3),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f392,f52])).
% 1.49/0.58  fof(f392,plain,(
% 1.49/0.58    r2_hidden(sK1(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~spl5_3),
% 1.49/0.58    inference(avatar_component_clause,[],[f390])).
% 1.49/0.58  fof(f390,plain,(
% 1.49/0.58    spl5_3 <=> r2_hidden(sK1(k1_tarski(sK0),sK0),k1_tarski(sK0))),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.49/0.58  fof(f383,plain,(
% 1.49/0.58    ~r1_tarski(sK0,sK1(k1_tarski(sK0),sK0)) | spl5_1),
% 1.49/0.58    inference(avatar_component_clause,[],[f381])).
% 1.49/0.58  fof(f381,plain,(
% 1.49/0.58    spl5_1 <=> r1_tarski(sK0,sK1(k1_tarski(sK0),sK0))),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.49/0.58  fof(f56,plain,(
% 1.49/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.58    inference(equality_resolution,[],[f33])).
% 1.49/0.58  fof(f33,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f2])).
% 1.49/0.58  fof(f2,axiom,(
% 1.49/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.58  fof(f393,plain,(
% 1.49/0.58    spl5_3 | spl5_2),
% 1.49/0.58    inference(avatar_split_clause,[],[f378,f385,f390])).
% 1.49/0.58  fof(f378,plain,(
% 1.49/0.58    k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK1(k1_tarski(sK0),sK0),k1_tarski(sK0))),
% 1.49/0.58    inference(resolution,[],[f376,f21])).
% 1.49/0.58  fof(f21,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK1(X0,X1),X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f17])).
% 1.49/0.58  fof(f17,plain,(
% 1.49/0.58    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.49/0.58    inference(flattening,[],[f16])).
% 1.49/0.58  fof(f16,plain,(
% 1.49/0.58    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.49/0.58    inference(ennf_transformation,[],[f12])).
% 1.49/0.58  fof(f12,axiom,(
% 1.49/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.49/0.58  fof(f376,plain,(
% 1.49/0.58    ~r1_tarski(sK0,k1_setfam_1(k1_tarski(sK0)))),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f20,f357,f35])).
% 1.49/0.58  fof(f35,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f2])).
% 1.49/0.58  fof(f357,plain,(
% 1.49/0.58    r1_tarski(k1_setfam_1(k1_tarski(sK0)),sK0)),
% 1.49/0.58    inference(forward_demodulation,[],[f354,f77])).
% 1.49/0.58  fof(f354,plain,(
% 1.49/0.58    r1_tarski(k1_setfam_1(k4_xboole_0(k1_tarski(sK0),k1_tarski(k1_setfam_1(k1_tarski(sK0))))),sK0)),
% 1.49/0.58    inference(superposition,[],[f254,f88])).
% 1.49/0.58  fof(f88,plain,(
% 1.49/0.58    k1_tarski(k1_setfam_1(k1_tarski(sK0))) = k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),k1_tarski(sK0))),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f20,f24])).
% 1.49/0.58  fof(f254,plain,(
% 1.49/0.58    ( ! [X0] : (r1_tarski(k1_setfam_1(k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),X0))),sK0)) )),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f126,f23])).
% 1.49/0.58  fof(f23,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f18])).
% 1.49/0.58  fof(f18,plain,(
% 1.49/0.58    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.49/0.58    inference(ennf_transformation,[],[f11])).
% 1.49/0.58  fof(f11,axiom,(
% 1.49/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.49/0.58  fof(f126,plain,(
% 1.49/0.58    ( ! [X0] : (r2_hidden(sK0,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),X0)))) )),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f54,f97,f64])).
% 1.49/0.58  fof(f97,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(k1_tarski(k1_setfam_1(k1_tarski(sK0))),X0))) )),
% 1.49/0.58    inference(unit_resulting_resolution,[],[f87,f66])).
% 1.49/0.58  fof(f66,plain,(
% 1.49/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.49/0.58    inference(equality_resolution,[],[f47])).
% 1.49/0.58  fof(f47,plain,(
% 1.49/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.49/0.58    inference(cnf_transformation,[],[f1])).
% 1.49/0.58  fof(f388,plain,(
% 1.49/0.58    ~spl5_1 | spl5_2),
% 1.49/0.58    inference(avatar_split_clause,[],[f379,f385,f381])).
% 1.49/0.58  fof(f379,plain,(
% 1.49/0.58    k1_xboole_0 = k1_tarski(sK0) | ~r1_tarski(sK0,sK1(k1_tarski(sK0),sK0))),
% 1.49/0.58    inference(resolution,[],[f376,f22])).
% 1.49/0.58  fof(f22,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK1(X0,X1))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f17])).
% 1.49/0.58  % SZS output end Proof for theBenchmark
% 1.49/0.58  % (2978)------------------------------
% 1.49/0.58  % (2978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (2978)Termination reason: Refutation
% 1.49/0.58  
% 1.49/0.58  % (2978)Memory used [KB]: 6652
% 1.49/0.58  % (2978)Time elapsed: 0.158 s
% 1.49/0.58  % (2978)------------------------------
% 1.49/0.58  % (2978)------------------------------
% 1.49/0.58  % (2948)Success in time 0.2 s
%------------------------------------------------------------------------------
