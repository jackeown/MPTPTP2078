%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 187 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 ( 609 expanded)
%              Number of equality atoms :   28 (  92 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f79,f82])).

fof(f82,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f80,f26])).

fof(f26,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
      | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
    & r2_hidden(sK1,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
            & r2_hidden(X1,X0) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
          & r2_hidden(X1,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
          | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
        & r2_hidden(X1,sK0) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
        | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

fof(f80,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_2 ),
    inference(resolution,[],[f74,f64])).

fof(f64,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_2
  <=> r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,(
    ! [X1] :
      ( r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f72,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f69,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0))
      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0))
      | r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ) ),
    inference(superposition,[],[f53,f66])).

fof(f66,plain,(
    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f69,plain,(
    ! [X2] :
      ( r2_hidden(X2,k4_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0))
      | r2_hidden(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f51,f66])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f77,f26])).

fof(f77,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_1 ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,
    ( ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_1
  <=> r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(k1_mcart_1(X0),k1_relat_1(sK0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f72,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f27,f62,f58])).

fof(f27,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (966)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (974)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.49  % (966)Refutation not found, incomplete strategy% (966)------------------------------
% 0.20/0.49  % (966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (966)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (966)Memory used [KB]: 10618
% 0.20/0.49  % (966)Time elapsed: 0.073 s
% 0.20/0.49  % (966)------------------------------
% 0.20/0.49  % (966)------------------------------
% 0.20/0.51  % (963)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (984)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (963)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f65,f79,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    $false | spl3_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f80,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    r2_hidden(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0)) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0)) => (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) => ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~r2_hidden(sK1,sK0) | spl3_2),
% 0.20/0.51    inference(resolution,[],[f74,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl3_2 <=> r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(X1,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f72,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~r2_hidden(X2,sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f69,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)) | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f67,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(rectify,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)) | r2_hidden(X0,sK0) | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) )),
% 0.20/0.52    inference(superposition,[],[f53,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.20/0.52    inference(resolution,[],[f25,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    v1_relat_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2))) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f41,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f29,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f30,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.52    inference(nnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(X2,k4_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)) | r2_hidden(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~r2_hidden(X2,sK0)) )),
% 0.20/0.52    inference(superposition,[],[f51,f66])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2))) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f43,f49])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl3_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    $false | spl3_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f77,f26])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ~r2_hidden(sK1,sK0) | spl3_1),
% 0.20/0.52    inference(resolution,[],[f73,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) | spl3_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    spl3_1 <=> r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k1_mcart_1(X0),k1_relat_1(sK0)) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f72,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f62,f58])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (963)------------------------------
% 0.20/0.52  % (963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (963)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (963)Memory used [KB]: 10746
% 0.20/0.52  % (963)Time elapsed: 0.108 s
% 0.20/0.52  % (963)------------------------------
% 0.20/0.52  % (963)------------------------------
% 0.20/0.52  % (952)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (948)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (947)Success in time 0.154 s
%------------------------------------------------------------------------------
