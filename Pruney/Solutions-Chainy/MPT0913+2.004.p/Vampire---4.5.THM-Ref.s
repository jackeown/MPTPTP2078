%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 155 expanded)
%              Number of leaves         :   12 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  198 ( 481 expanded)
%              Number of equality atoms :   12 (  48 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f49,f50,f51,f61,f75,f77,f79,f80,f85])).

fof(f85,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl6_1
    | spl6_5 ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f73,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f71,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f71,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_1 ),
    inference(resolution,[],[f34,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f34,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl6_1
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f80,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_5 ),
    inference(avatar_split_clause,[],[f64,f58,f41,f37])).

% (25936)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f37,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f41,plain,
    ( spl6_3
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f64,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | spl6_5 ),
    inference(resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f52,f20])).

fof(f52,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(forward_demodulation,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f10])).

% (25962)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f79,plain,
    ( spl6_3
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,
    ( ~ r2_hidden(sK1,sK4)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f68,plain,
    ( r2_hidden(sK1,sK4)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f66,f21])).

fof(f66,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK0,sK1)),sK4)
    | ~ spl6_5 ),
    inference(resolution,[],[f59,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f77,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(resolution,[],[f69,f39])).

fof(f39,plain,
    ( ~ r2_hidden(sK0,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f69,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f67,f20])).

fof(f67,plain,
    ( r2_hidden(k1_mcart_1(k4_tarski(sK0,sK1)),sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f59,f24])).

fof(f75,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl6_1
    | spl6_4 ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,
    ( ~ r2_hidden(sK2,sK5)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f72,plain,
    ( r2_hidden(sK2,sK5)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f70,f21])).

fof(f70,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),sK5)
    | ~ spl6_1 ),
    inference(resolution,[],[f34,f25])).

fof(f61,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f54,f33,f45,f58])).

fof(f54,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl6_1 ),
    inference(resolution,[],[f53,f35])).

fof(f35,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f51,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f30,f37,f33])).

fof(f30,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f16,f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f16,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f15])).

% (25940)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f15,plain,
    ( ( ~ r2_hidden(sK2,sK5)
      | ~ r2_hidden(sK1,sK4)
      | ~ r2_hidden(sK0,sK3)
      | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
    & ( ( r2_hidden(sK2,sK5)
        & r2_hidden(sK1,sK4)
        & r2_hidden(sK0,sK3) )
      | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( ~ r2_hidden(X2,X5)
          | ~ r2_hidden(X1,X4)
          | ~ r2_hidden(X0,X3)
          | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
        & ( ( r2_hidden(X2,X5)
            & r2_hidden(X1,X4)
            & r2_hidden(X0,X3) )
          | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) )
   => ( ( ~ r2_hidden(sK2,sK5)
        | ~ r2_hidden(sK1,sK4)
        | ~ r2_hidden(sK0,sK3)
        | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
      & ( ( r2_hidden(sK2,sK5)
          & r2_hidden(sK1,sK4)
          & r2_hidden(sK0,sK3) )
        | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <~> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      <=> ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f50,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f29,f41,f33])).

fof(f29,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f17,f23,f22])).

fof(f17,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f28,f45,f33])).

fof(f28,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f18,f23,f22])).

fof(f18,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f27,f45,f41,f37,f33])).

fof(f27,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f19,f23,f22])).

fof(f19,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (25947)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (25942)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (25947)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f48,f49,f50,f51,f61,f75,f77,f79,f80,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~spl6_1 | spl6_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    $false | (~spl6_1 | spl6_5)),
% 0.20/0.51    inference(resolution,[],[f73,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl6_5 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_1),
% 0.20/0.51    inference(forward_demodulation,[],[f71,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    r2_hidden(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_zfmisc_1(sK3,sK4)) | ~spl6_1),
% 0.20/0.51    inference(resolution,[],[f34,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    spl6_1 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~spl6_2 | ~spl6_3 | spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f64,f58,f41,f37])).
% 0.20/0.51  % (25936)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    spl6_2 <=> r2_hidden(sK0,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    spl6_3 <=> r2_hidden(sK1,sK4)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | spl6_5),
% 0.20/0.51    inference(resolution,[],[f60,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(X4,X2) | ~r2_hidden(X3,X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f52,f20])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X4,X2,X3,X1] : (~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f31,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  % (25962)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0) | (~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl6_3 | ~spl6_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    $false | (spl6_3 | ~spl6_5)),
% 0.20/0.51    inference(resolution,[],[f68,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ~r2_hidden(sK1,sK4) | spl6_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f41])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    r2_hidden(sK1,sK4) | ~spl6_5),
% 0.20/0.51    inference(forward_demodulation,[],[f66,f21])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    r2_hidden(k2_mcart_1(k4_tarski(sK0,sK1)),sK4) | ~spl6_5),
% 0.20/0.51    inference(resolution,[],[f59,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl6_2 | ~spl6_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    $false | (spl6_2 | ~spl6_5)),
% 0.20/0.51    inference(resolution,[],[f69,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK3) | spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f37])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    r2_hidden(sK0,sK3) | ~spl6_5),
% 0.20/0.51    inference(forward_demodulation,[],[f67,f20])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    r2_hidden(k1_mcart_1(k4_tarski(sK0,sK1)),sK3) | ~spl6_5),
% 0.20/0.51    inference(resolution,[],[f59,f24])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ~spl6_1 | spl6_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    $false | (~spl6_1 | spl6_4)),
% 0.20/0.51    inference(resolution,[],[f72,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ~r2_hidden(sK2,sK5) | spl6_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl6_4 <=> r2_hidden(sK2,sK5)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    r2_hidden(sK2,sK5) | ~spl6_1),
% 0.20/0.51    inference(forward_demodulation,[],[f70,f21])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    r2_hidden(k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)),sK5) | ~spl6_1),
% 0.20/0.51    inference(resolution,[],[f34,f25])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~spl6_5 | ~spl6_4 | spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f33,f45,f58])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ~r2_hidden(sK2,sK5) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl6_1),
% 0.20/0.51    inference(resolution,[],[f53,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f33])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    spl6_1 | spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f37,f33])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    r2_hidden(sK0,sK3) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.51    inference(definition_unfolding,[],[f16,f23,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    r2_hidden(sK0,sK3) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % (25940)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    (~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))) & ((r2_hidden(sK2,sK5) & r2_hidden(sK1,sK4) & r2_hidden(sK0,sK3)) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4,X5] : ((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)))) => ((~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))) & ((r2_hidden(sK2,sK5) & r2_hidden(sK1,sK4) & r2_hidden(sK0,sK3)) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4,X5] : ((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4,X5] : (((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3)) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 0.20/0.51    inference(nnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <~> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  fof(f6,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl6_1 | spl6_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f41,f33])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    r2_hidden(sK1,sK4) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.51    inference(definition_unfolding,[],[f17,f23,f22])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    r2_hidden(sK1,sK4) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    spl6_1 | spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f45,f33])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    r2_hidden(sK2,sK5) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f23,f22])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    r2_hidden(sK2,sK5) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f45,f41,f37,f33])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f23,f22])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (25947)------------------------------
% 0.20/0.51  % (25947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25947)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (25947)Memory used [KB]: 6140
% 0.20/0.51  % (25947)Time elapsed: 0.100 s
% 0.20/0.51  % (25947)------------------------------
% 0.20/0.51  % (25947)------------------------------
% 0.20/0.51  % (25934)Success in time 0.151 s
%------------------------------------------------------------------------------
