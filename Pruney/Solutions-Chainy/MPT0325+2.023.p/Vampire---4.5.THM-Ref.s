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
% DateTime   : Thu Dec  3 12:42:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 156 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 ( 501 expanded)
%              Number of equality atoms :   93 ( 258 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f634,f652,f697,f748,f1457])).

fof(f1457,plain,
    ( spl4_2
    | spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f1456])).

fof(f1456,plain,
    ( $false
    | spl4_2
    | spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f1450,f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1450,plain,
    ( r1_tarski(sK1,sK3)
    | spl4_4
    | spl4_5 ),
    inference(superposition,[],[f41,f1160])).

fof(f1160,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f632,f628,f45,f99])).

fof(f99,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( k3_xboole_0(k2_zfmisc_1(X6,X8),k2_zfmisc_1(X7,X9)) != k2_zfmisc_1(X10,X11)
      | k1_xboole_0 = X11
      | k1_xboole_0 = X10
      | k3_xboole_0(X8,X9) = X11 ) ),
    inference(superposition,[],[f22,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f45,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f18,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k2_zfmisc_1(X0,X1) != k1_xboole_0
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f628,plain,
    ( k1_xboole_0 != sK0
    | spl4_4 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f632,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f631])).

fof(f631,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f748,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f746,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f746,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f19,f633])).

fof(f633,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f631])).

fof(f19,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f697,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f695,f30])).

fof(f695,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f670,f31])).

fof(f31,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f670,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1))),k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f123,f629])).

fof(f629,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f627])).

fof(f123,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f63,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f19,f50,f23])).

fof(f50,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f19,f23])).

fof(f652,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f645,f35])).

fof(f35,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f645,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_3 ),
    inference(superposition,[],[f41,f625])).

fof(f625,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl4_3
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f634,plain,
    ( spl4_3
    | spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f621,f631,f627,f623])).

fof(f621,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK0 = k3_xboole_0(sK0,sK2) ),
    inference(equality_resolution,[],[f360])).

fof(f360,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_xboole_0(sK0,sK2) = X0 ) ),
    inference(superposition,[],[f78,f45])).

fof(f78,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( k3_xboole_0(k2_zfmisc_1(X6,X8),k2_zfmisc_1(X7,X9)) != k2_zfmisc_1(X10,X11)
      | k1_xboole_0 = X11
      | k1_xboole_0 = X10
      | k3_xboole_0(X6,X7) = X10 ) ),
    inference(superposition,[],[f21,f28])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f20,f37,f33])).

fof(f20,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (18015)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (18025)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (18030)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (18016)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (18011)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (18013)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (18026)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (18014)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (18017)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (18032)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (18036)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (18018)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (18022)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (18034)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (18029)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (18033)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (18023)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (18021)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (18024)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (18028)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (18019)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (18037)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (18012)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (18027)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (18035)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (18031)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.58  % (18011)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f1458,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f40,f634,f652,f697,f748,f1457])).
% 0.21/0.58  fof(f1457,plain,(
% 0.21/0.58    spl4_2 | spl4_4 | spl4_5),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1456])).
% 0.21/0.58  fof(f1456,plain,(
% 0.21/0.58    $false | (spl4_2 | spl4_4 | spl4_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f1450,f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ~r1_tarski(sK1,sK3) | spl4_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    spl4_2 <=> r1_tarski(sK1,sK3)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.58  fof(f1450,plain,(
% 0.21/0.58    r1_tarski(sK1,sK3) | (spl4_4 | spl4_5)),
% 0.21/0.58    inference(superposition,[],[f41,f1160])).
% 0.21/0.58  fof(f1160,plain,(
% 0.21/0.58    sK1 = k3_xboole_0(sK1,sK3) | (spl4_4 | spl4_5)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f632,f628,f45,f99])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    ( ! [X6,X10,X8,X7,X11,X9] : (k3_xboole_0(k2_zfmisc_1(X6,X8),k2_zfmisc_1(X7,X9)) != k2_zfmisc_1(X10,X11) | k1_xboole_0 = X11 | k1_xboole_0 = X10 | k3_xboole_0(X8,X9) = X11) )),
% 0.21/0.58    inference(superposition,[],[f22,f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.58    inference(flattening,[],[f11])).
% 0.21/0.58  fof(f11,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f18,f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0 & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f10,plain,(
% 0.21/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0 & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.58    inference(flattening,[],[f9])).
% 0.21/0.58  fof(f9,plain,(
% 0.21/0.58    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.21/0.58    inference(negated_conjecture,[],[f7])).
% 0.21/0.58  fof(f7,conjecture,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.21/0.58  fof(f628,plain,(
% 0.21/0.58    k1_xboole_0 != sK0 | spl4_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f627])).
% 0.21/0.58  fof(f627,plain,(
% 0.21/0.58    spl4_4 <=> k1_xboole_0 = sK0),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.58  fof(f632,plain,(
% 0.21/0.58    k1_xboole_0 != sK1 | spl4_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f631])).
% 0.21/0.58  fof(f631,plain,(
% 0.21/0.58    spl4_5 <=> k1_xboole_0 = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.21/0.58    inference(superposition,[],[f27,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.58  fof(f748,plain,(
% 0.21/0.58    ~spl4_5),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f747])).
% 0.21/0.58  fof(f747,plain,(
% 0.21/0.58    $false | ~spl4_5),
% 0.21/0.58    inference(subsumption_resolution,[],[f746,f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.58    inference(flattening,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.58    inference(nnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.58  fof(f746,plain,(
% 0.21/0.58    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | ~spl4_5),
% 0.21/0.58    inference(backward_demodulation,[],[f19,f633])).
% 0.21/0.58  fof(f633,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | ~spl4_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f631])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f697,plain,(
% 0.21/0.58    ~spl4_4),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f696])).
% 0.21/0.58  fof(f696,plain,(
% 0.21/0.58    $false | ~spl4_4),
% 0.21/0.58    inference(subsumption_resolution,[],[f695,f30])).
% 0.21/0.58  fof(f695,plain,(
% 0.21/0.58    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl4_4),
% 0.21/0.58    inference(forward_demodulation,[],[f670,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f670,plain,(
% 0.21/0.58    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1))),k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_4),
% 0.21/0.58    inference(backward_demodulation,[],[f123,f629])).
% 0.21/0.58  fof(f629,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | ~spl4_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f627])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),k2_zfmisc_1(sK0,sK1))),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f19,f63,f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f19,f50,f23])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f19,f19,f23])).
% 0.21/0.58  fof(f652,plain,(
% 0.21/0.58    spl4_1 | ~spl4_3),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f651])).
% 0.21/0.58  fof(f651,plain,(
% 0.21/0.58    $false | (spl4_1 | ~spl4_3)),
% 0.21/0.58    inference(subsumption_resolution,[],[f645,f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ~r1_tarski(sK0,sK2) | spl4_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    spl4_1 <=> r1_tarski(sK0,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.58  fof(f645,plain,(
% 0.21/0.58    r1_tarski(sK0,sK2) | ~spl4_3),
% 0.21/0.58    inference(superposition,[],[f41,f625])).
% 0.21/0.58  fof(f625,plain,(
% 0.21/0.58    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f623])).
% 0.21/0.58  fof(f623,plain,(
% 0.21/0.58    spl4_3 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.58  fof(f634,plain,(
% 0.21/0.58    spl4_3 | spl4_4 | spl4_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f621,f631,f627,f623])).
% 0.21/0.58  fof(f621,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.58    inference(equality_resolution,[],[f360])).
% 0.21/0.58  fof(f360,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_xboole_0(sK0,sK2) = X0) )),
% 0.21/0.58    inference(superposition,[],[f78,f45])).
% 0.21/0.58  fof(f78,plain,(
% 0.21/0.58    ( ! [X6,X10,X8,X7,X11,X9] : (k3_xboole_0(k2_zfmisc_1(X6,X8),k2_zfmisc_1(X7,X9)) != k2_zfmisc_1(X10,X11) | k1_xboole_0 = X11 | k1_xboole_0 = X10 | k3_xboole_0(X6,X7) = X10) )),
% 0.21/0.58    inference(superposition,[],[f21,f28])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ~spl4_1 | ~spl4_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f20,f37,f33])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (18011)------------------------------
% 0.21/0.58  % (18011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (18011)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (18011)Memory used [KB]: 11257
% 0.21/0.58  % (18011)Time elapsed: 0.174 s
% 0.21/0.58  % (18011)------------------------------
% 0.21/0.58  % (18011)------------------------------
% 0.21/0.58  % (18007)Success in time 0.224 s
%------------------------------------------------------------------------------
