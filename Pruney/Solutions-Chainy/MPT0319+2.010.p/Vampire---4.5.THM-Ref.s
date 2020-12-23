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
% DateTime   : Thu Dec  3 12:42:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  74 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 189 expanded)
%              Number of equality atoms :   46 (  90 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f146,f324])).

fof(f324,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f322,f18])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
      | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) )
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
        & X0 != X1 )
   => ( ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) )
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( X0 != X1
       => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(f322,plain,
    ( sK0 = sK1
    | spl4_2 ),
    inference(resolution,[],[f302,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f302,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl4_2 ),
    inference(resolution,[],[f130,f40])).

fof(f40,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_2
  <=> r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f130,plain,(
    ! [X19,X17,X18,X16] :
      ( r1_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(X18,X19))
      | ~ r1_xboole_0(X17,X19) ) ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,(
    ! [X19,X17,X18,X16] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(X18,X19))
      | ~ r1_xboole_0(X17,X19) ) ),
    inference(superposition,[],[f25,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f55,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f146,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f144,f18])).

fof(f144,plain,
    ( sK0 = sK1
    | spl4_1 ),
    inference(resolution,[],[f136,f22])).

fof(f136,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl4_1 ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,(
    ! [X14,X12,X15,X13] :
      ( r1_xboole_0(k2_zfmisc_1(X12,X13),k2_zfmisc_1(X14,X15))
      | ~ r1_xboole_0(X12,X14) ) ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,(
    ! [X14,X12,X15,X13] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(X12,X13),k2_zfmisc_1(X14,X15))
      | ~ r1_xboole_0(X12,X14) ) ),
    inference(superposition,[],[f25,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f54,f32])).

fof(f32,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f29,f24])).

fof(f41,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f19,f38,f34])).

fof(f19,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (14644)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14631)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (14632)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (14637)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (14636)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (14651)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (14636)Refutation not found, incomplete strategy% (14636)------------------------------
% 0.21/0.51  % (14636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14636)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14636)Memory used [KB]: 6012
% 0.21/0.51  % (14636)Time elapsed: 0.099 s
% 0.21/0.51  % (14636)------------------------------
% 0.21/0.51  % (14636)------------------------------
% 0.21/0.51  % (14640)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (14632)Refutation not found, incomplete strategy% (14632)------------------------------
% 0.21/0.52  % (14632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14632)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14632)Memory used [KB]: 10490
% 0.21/0.52  % (14632)Time elapsed: 0.099 s
% 0.21/0.52  % (14632)------------------------------
% 0.21/0.52  % (14632)------------------------------
% 0.21/0.52  % (14633)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (14635)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (14634)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (14639)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (14649)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (14649)Refutation not found, incomplete strategy% (14649)------------------------------
% 0.21/0.53  % (14649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14648)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (14649)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14649)Memory used [KB]: 1663
% 0.21/0.53  % (14649)Time elapsed: 0.110 s
% 0.21/0.53  % (14649)------------------------------
% 0.21/0.53  % (14649)------------------------------
% 0.21/0.53  % (14635)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f41,f146,f324])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    spl4_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f323])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    $false | spl4_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f322,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    sK0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    (~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))) & sK0 != sK1),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1) => ((~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))) & sK0 != sK1)),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1)),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    sK0 = sK1 | spl4_2),
% 0.21/0.53    inference(resolution,[],[f302,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl4_2),
% 0.21/0.53    inference(resolution,[],[f130,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    spl4_2 <=> r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X19,X17,X18,X16] : (r1_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(X18,X19)) | ~r1_xboole_0(X17,X19)) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X19,X17,X18,X16] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(X18,X19)) | ~r1_xboole_0(X17,X19)) )),
% 0.21/0.53    inference(superposition,[],[f25,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f55,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) = k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f29,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl4_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    $false | spl4_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f18])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    sK0 = sK1 | spl4_1),
% 0.21/0.53    inference(resolution,[],[f136,f22])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl4_1),
% 0.21/0.53    inference(resolution,[],[f71,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) | spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    spl4_1 <=> r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X14,X12,X15,X13] : (r1_xboole_0(k2_zfmisc_1(X12,X13),k2_zfmisc_1(X14,X15)) | ~r1_xboole_0(X12,X14)) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X14,X12,X15,X13] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X12,X13),k2_zfmisc_1(X14,X15)) | ~r1_xboole_0(X12,X14)) )),
% 0.21/0.53    inference(superposition,[],[f25,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f54,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X2,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f29,f24])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f19,f38,f34])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14635)------------------------------
% 0.21/0.53  % (14635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14635)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14635)Memory used [KB]: 6268
% 0.21/0.53  % (14635)Time elapsed: 0.118 s
% 0.21/0.53  % (14635)------------------------------
% 0.21/0.53  % (14635)------------------------------
% 0.21/0.53  % (14637)Refutation not found, incomplete strategy% (14637)------------------------------
% 0.21/0.53  % (14637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14637)Memory used [KB]: 10490
% 0.21/0.53  % (14637)Time elapsed: 0.120 s
% 0.21/0.53  % (14637)------------------------------
% 0.21/0.53  % (14637)------------------------------
% 0.21/0.53  % (14651)Refutation not found, incomplete strategy% (14651)------------------------------
% 0.21/0.53  % (14651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14651)Memory used [KB]: 10618
% 0.21/0.53  % (14651)Time elapsed: 0.124 s
% 0.21/0.53  % (14651)------------------------------
% 0.21/0.53  % (14651)------------------------------
% 0.21/0.53  % (14639)Refutation not found, incomplete strategy% (14639)------------------------------
% 0.21/0.53  % (14639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14639)Memory used [KB]: 1663
% 0.21/0.53  % (14639)Time elapsed: 0.121 s
% 0.21/0.53  % (14639)------------------------------
% 0.21/0.53  % (14639)------------------------------
% 0.21/0.54  % (14643)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (14653)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (14647)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (14646)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (14645)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (14656)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (14630)Success in time 0.185 s
%------------------------------------------------------------------------------
