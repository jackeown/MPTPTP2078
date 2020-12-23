%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  84 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 192 expanded)
%              Number of equality atoms :   59 ( 114 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f54,f70,f73,f86])).

fof(f86,plain,
    ( ~ spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl2_1
    | spl2_3 ),
    inference(subsumption_resolution,[],[f84,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f84,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1
    | spl2_3 ),
    inference(resolution,[],[f83,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f83,plain,
    ( ! [X3] : r1_tarski(sK0,X3)
    | ~ spl2_1
    | spl2_3 ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f44,plain,
    ( k1_xboole_0 != k2_tarski(sK1,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f82,plain,
    ( ! [X3] :
        ( r1_tarski(sK0,X3)
        | k1_xboole_0 = k2_tarski(sK1,sK1) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f77,f17])).

fof(f17,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f77,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_tarski(sK1,sK1),X3))
        | r1_tarski(sK0,X3)
        | k1_xboole_0 = k2_tarski(sK1,sK1) )
    | ~ spl2_1 ),
    inference(superposition,[],[f24,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f73,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f71,f15])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(resolution,[],[f53,f20])).

fof(f53,plain,
    ( ! [X1] : r1_tarski(sK0,X1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X1] : r1_tarski(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f70,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f66,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f66,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f28,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f28,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f21,f19,f19,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

% (804)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f54,plain,
    ( spl2_3
    | spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f34,f52,f43])).

fof(f34,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f50,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,X1)
        | k1_xboole_0 = k2_tarski(sK1,sK1) )
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f39,f17])).

fof(f39,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,k2_tarski(sK1,sK1)))
        | r1_tarski(sK0,X1)
        | k1_xboole_0 = k2_tarski(sK1,sK1) )
    | ~ spl2_2 ),
    inference(superposition,[],[f23,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f25,f34,f30])).

fof(f25,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f16,f19,f19])).

fof(f16,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:23:30 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.22/0.51  % (801)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (801)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (818)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (797)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (809)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f37,f54,f70,f73,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ~spl2_1 | spl2_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    $false | (~spl2_1 | spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f84,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | (~spl2_1 | spl2_3)),
% 0.22/0.52    inference(resolution,[],[f83,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X3] : (r1_tarski(sK0,X3)) ) | (~spl2_1 | spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f82,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    k1_xboole_0 != k2_tarski(sK1,sK1) | spl2_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    spl2_3 <=> k1_xboole_0 = k2_tarski(sK1,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X3] : (r1_tarski(sK0,X3) | k1_xboole_0 = k2_tarski(sK1,sK1)) ) | ~spl2_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f77,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X3] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_tarski(sK1,sK1),X3)) | r1_tarski(sK0,X3) | k1_xboole_0 = k2_tarski(sK1,sK1)) ) | ~spl2_1),
% 0.22/0.52    inference(superposition,[],[f24,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) | ~spl2_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    spl2_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ~spl2_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    $false | ~spl2_5),
% 0.22/0.52    inference(subsumption_resolution,[],[f71,f15])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl2_5),
% 0.22/0.52    inference(resolution,[],[f53,f20])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(sK0,X1)) ) | ~spl2_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl2_5 <=> ! [X1] : r1_tarski(sK0,X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ~spl2_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    $false | ~spl2_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f66,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.22/0.52    inference(superposition,[],[f28,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl2_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f43])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f21,f19,f19,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  % (804)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    spl2_3 | spl2_5 | ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f34,f52,f43])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(sK0,X1) | k1_xboole_0 = k2_tarski(sK1,sK1)) ) | ~spl2_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f39,f17])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,k2_tarski(sK1,sK1))) | r1_tarski(sK0,X1) | k1_xboole_0 = k2_tarski(sK1,sK1)) ) | ~spl2_2),
% 0.22/0.53    inference(superposition,[],[f23,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) | ~spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f34])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    spl2_1 | spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f34,f30])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f16,f19,f19])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (801)------------------------------
% 0.22/0.53  % (801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (801)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (801)Memory used [KB]: 10746
% 0.22/0.53  % (801)Time elapsed: 0.098 s
% 0.22/0.53  % (801)------------------------------
% 0.22/0.53  % (801)------------------------------
% 0.22/0.53  % (804)Refutation not found, incomplete strategy% (804)------------------------------
% 0.22/0.53  % (804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (794)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (792)Success in time 0.153 s
%------------------------------------------------------------------------------
