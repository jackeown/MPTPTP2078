%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:45 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 160 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 ( 384 expanded)
%              Number of equality atoms :   44 ( 142 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f58,f82,f95,f121,f140])).

fof(f140,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f138,f93])).

fof(f93,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f138,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f112,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f111,f45])).

fof(f45,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f107,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f121,plain,
    ( ~ spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl2_1
    | spl2_3 ),
    inference(subsumption_resolution,[],[f119,f89])).

fof(f89,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f119,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f117,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f117,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f114,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f51,f96])).

fof(f96,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f95,plain,
    ( ~ spl2_4
    | ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f85,f54,f87,f91])).

fof(f54,plain,
    ( spl2_2
  <=> sK1 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK1,sK0)
    | spl2_2 ),
    inference(extensionality_resolution,[],[f40,f83])).

fof(f83,plain,
    ( sK0 != sK1
    | spl2_2 ),
    inference(forward_demodulation,[],[f56,f45])).

fof(f56,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f82,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f80,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f60,f73])).

fof(f73,plain,
    ( k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f36,f61])).

fof(f61,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f26,f59])).

fof(f59,plain,
    ( sK0 = sK1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f55,f45])).

fof(f55,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f60,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f52,f59])).

fof(f52,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f58,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f44,f54,f50])).

fof(f44,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f27,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f54,f50])).

fof(f43,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f28,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:17:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (6918)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (6914)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (6934)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.55  % (6938)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (6918)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f141,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(avatar_sat_refutation,[],[f57,f58,f82,f95,f121,f140])).
% 1.38/0.55  fof(f140,plain,(
% 1.38/0.55    spl2_4),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f139])).
% 1.38/0.55  fof(f139,plain,(
% 1.38/0.55    $false | spl2_4),
% 1.38/0.55    inference(subsumption_resolution,[],[f138,f93])).
% 1.38/0.55  fof(f93,plain,(
% 1.38/0.55    ~r1_tarski(sK1,sK0) | spl2_4),
% 1.38/0.55    inference(avatar_component_clause,[],[f91])).
% 1.38/0.55  fof(f91,plain,(
% 1.38/0.55    spl2_4 <=> r1_tarski(sK1,sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.38/0.55  fof(f138,plain,(
% 1.38/0.55    r1_tarski(sK1,sK0)),
% 1.38/0.55    inference(resolution,[],[f112,f26])).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.55    inference(flattening,[],[f20])).
% 1.38/0.55  fof(f20,plain,(
% 1.38/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.55    inference(nnf_transformation,[],[f15])).
% 1.38/0.55  fof(f15,plain,(
% 1.38/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f13])).
% 1.38/0.55  fof(f13,negated_conjecture,(
% 1.38/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.38/0.55    inference(negated_conjecture,[],[f12])).
% 1.38/0.55  fof(f12,conjecture,(
% 1.38/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.38/0.55  fof(f112,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.55    inference(forward_demodulation,[],[f111,f45])).
% 1.38/0.55  fof(f45,plain,(
% 1.38/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.38/0.55    inference(definition_unfolding,[],[f31,f42])).
% 1.38/0.55  fof(f42,plain,(
% 1.38/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.38/0.55    inference(definition_unfolding,[],[f33,f30])).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.38/0.55  fof(f33,plain,(
% 1.38/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f10])).
% 1.38/0.55  fof(f10,axiom,(
% 1.38/0.55    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.38/0.55  fof(f31,plain,(
% 1.38/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,axiom,(
% 1.38/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.38/0.55  fof(f111,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f107,f46])).
% 1.38/0.55  fof(f46,plain,(
% 1.38/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.38/0.55    inference(definition_unfolding,[],[f32,f30])).
% 1.38/0.55  fof(f32,plain,(
% 1.38/0.55    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f9])).
% 1.38/0.55  fof(f9,axiom,(
% 1.38/0.55    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.38/0.55  fof(f107,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 1.38/0.55    inference(resolution,[],[f37,f29])).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f3])).
% 1.38/0.55  fof(f3,axiom,(
% 1.38/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.38/0.55  fof(f37,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f18])).
% 1.38/0.55  fof(f18,plain,(
% 1.38/0.55    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.55    inference(flattening,[],[f17])).
% 1.38/0.55  fof(f17,plain,(
% 1.38/0.55    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f11])).
% 1.38/0.55  fof(f11,axiom,(
% 1.38/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 1.38/0.55  fof(f121,plain,(
% 1.38/0.55    ~spl2_1 | spl2_3),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f120])).
% 1.38/0.55  fof(f120,plain,(
% 1.38/0.55    $false | (~spl2_1 | spl2_3)),
% 1.38/0.55    inference(subsumption_resolution,[],[f119,f89])).
% 1.38/0.55  fof(f89,plain,(
% 1.38/0.55    ~r1_tarski(sK0,sK1) | spl2_3),
% 1.38/0.55    inference(avatar_component_clause,[],[f87])).
% 1.38/0.55  fof(f87,plain,(
% 1.38/0.55    spl2_3 <=> r1_tarski(sK0,sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.38/0.55  fof(f119,plain,(
% 1.38/0.55    r1_tarski(sK0,sK1) | ~spl2_1),
% 1.38/0.55    inference(forward_demodulation,[],[f117,f34])).
% 1.38/0.55  fof(f34,plain,(
% 1.38/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f14])).
% 1.38/0.55  fof(f14,plain,(
% 1.38/0.55    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.38/0.55    inference(rectify,[],[f1])).
% 1.38/0.55  fof(f1,axiom,(
% 1.38/0.55    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.38/0.55  fof(f117,plain,(
% 1.38/0.55    r1_tarski(sK0,k2_xboole_0(sK1,sK1)) | ~spl2_1),
% 1.38/0.55    inference(resolution,[],[f114,f41])).
% 1.38/0.55  fof(f41,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f19])).
% 1.38/0.55  fof(f19,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.38/0.55    inference(ennf_transformation,[],[f5])).
% 1.38/0.55  fof(f5,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.38/0.55  fof(f114,plain,(
% 1.38/0.55    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~spl2_1),
% 1.38/0.55    inference(backward_demodulation,[],[f51,f96])).
% 1.38/0.55  fof(f96,plain,(
% 1.38/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.38/0.55    inference(resolution,[],[f26,f36])).
% 1.38/0.55  fof(f36,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f16])).
% 1.38/0.55  fof(f16,plain,(
% 1.38/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f8])).
% 1.38/0.55  fof(f8,axiom,(
% 1.38/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.38/0.55  fof(f51,plain,(
% 1.38/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl2_1),
% 1.38/0.55    inference(avatar_component_clause,[],[f50])).
% 1.38/0.55  fof(f50,plain,(
% 1.38/0.55    spl2_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.38/0.55  fof(f95,plain,(
% 1.38/0.55    ~spl2_4 | ~spl2_3 | spl2_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f85,f54,f87,f91])).
% 1.38/0.55  fof(f54,plain,(
% 1.38/0.55    spl2_2 <=> sK1 = k3_subset_1(sK0,k1_xboole_0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.38/0.55  fof(f85,plain,(
% 1.38/0.55    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK1,sK0) | spl2_2),
% 1.38/0.55    inference(extensionality_resolution,[],[f40,f83])).
% 1.38/0.55  fof(f83,plain,(
% 1.38/0.55    sK0 != sK1 | spl2_2),
% 1.38/0.55    inference(forward_demodulation,[],[f56,f45])).
% 1.38/0.55  fof(f56,plain,(
% 1.38/0.55    sK1 != k3_subset_1(sK0,k1_xboole_0) | spl2_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f54])).
% 1.38/0.55  fof(f40,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f25])).
% 1.38/0.55  fof(f25,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(flattening,[],[f24])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(nnf_transformation,[],[f2])).
% 1.38/0.55  fof(f2,axiom,(
% 1.38/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.55  fof(f82,plain,(
% 1.38/0.55    spl2_1 | ~spl2_2),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f81])).
% 1.38/0.55  fof(f81,plain,(
% 1.38/0.55    $false | (spl2_1 | ~spl2_2)),
% 1.38/0.55    inference(subsumption_resolution,[],[f80,f35])).
% 1.38/0.55  fof(f35,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f4])).
% 1.38/0.55  fof(f4,axiom,(
% 1.38/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.38/0.55  fof(f80,plain,(
% 1.38/0.55    ~r1_tarski(k4_xboole_0(sK0,sK0),sK0) | (spl2_1 | ~spl2_2)),
% 1.38/0.55    inference(backward_demodulation,[],[f60,f73])).
% 1.38/0.55  fof(f73,plain,(
% 1.38/0.55    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) | ~spl2_2),
% 1.38/0.55    inference(resolution,[],[f36,f61])).
% 1.38/0.55  fof(f61,plain,(
% 1.38/0.55    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl2_2),
% 1.38/0.55    inference(backward_demodulation,[],[f26,f59])).
% 1.38/0.55  fof(f59,plain,(
% 1.38/0.55    sK0 = sK1 | ~spl2_2),
% 1.38/0.55    inference(backward_demodulation,[],[f55,f45])).
% 1.38/0.55  fof(f55,plain,(
% 1.38/0.55    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl2_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f54])).
% 1.38/0.55  fof(f60,plain,(
% 1.38/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl2_1 | ~spl2_2)),
% 1.38/0.55    inference(backward_demodulation,[],[f52,f59])).
% 1.38/0.55  fof(f52,plain,(
% 1.38/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl2_1),
% 1.38/0.55    inference(avatar_component_clause,[],[f50])).
% 1.38/0.55  fof(f58,plain,(
% 1.38/0.55    spl2_1 | spl2_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f44,f54,f50])).
% 1.38/0.55  fof(f44,plain,(
% 1.38/0.55    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.38/0.55    inference(definition_unfolding,[],[f27,f42])).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f57,plain,(
% 1.38/0.55    ~spl2_1 | ~spl2_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f43,f54,f50])).
% 1.38/0.55  fof(f43,plain,(
% 1.38/0.55    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.38/0.55    inference(definition_unfolding,[],[f28,f42])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (6918)------------------------------
% 1.38/0.55  % (6918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (6918)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (6918)Memory used [KB]: 10746
% 1.38/0.55  % (6918)Time elapsed: 0.125 s
% 1.38/0.55  % (6918)------------------------------
% 1.38/0.55  % (6918)------------------------------
% 1.38/0.56  % (6911)Success in time 0.192 s
%------------------------------------------------------------------------------
