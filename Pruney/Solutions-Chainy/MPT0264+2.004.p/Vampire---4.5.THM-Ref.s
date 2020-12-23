%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:20 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   51 (  87 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 ( 454 expanded)
%              Number of equality atoms :   81 ( 163 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f32])).

fof(f32,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK2 != sK3
    & r2_hidden(sK3,sK4)
    & k1_tarski(sK2) = k3_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) )
   => ( sK2 != sK3
      & r2_hidden(sK3,sK4)
      & k1_tarski(sK2) = k3_xboole_0(k2_tarski(sK2,sK3),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

% (16225)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f139,plain,(
    sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( sK2 = sK3
    | sK2 = sK3 ),
    inference(resolution,[],[f135,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f5,f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f135,plain,(
    r2_hidden(sK3,k2_tarski(sK2,sK2)) ),
    inference(subsumption_resolution,[],[f133,f31])).

fof(f31,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK2))
    | ~ r2_hidden(sK3,sK4) ),
    inference(resolution,[],[f131,f65])).

fof(f65,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f58,f60])).

fof(f58,plain,(
    ! [X4,X2,X1] :
      ( ~ sP1(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f131,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_tarski(sK2,sK3))
      | r2_hidden(X1,k2_tarski(sK2,sK2))
      | ~ r2_hidden(X1,sK4) ) ),
    inference(resolution,[],[f99,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X3] :
      ( r2_hidden(X3,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
      | ~ r2_hidden(X3,k2_tarski(sK2,sK3))
      | r2_hidden(X3,k2_tarski(sK2,sK2)) ) ),
    inference(resolution,[],[f40,f78])).

fof(f78,plain,(
    sP0(k4_xboole_0(k2_tarski(sK2,sK3),sK4),k2_tarski(sK2,sK3),k2_tarski(sK2,sK2)) ),
    inference(superposition,[],[f57,f54])).

fof(f54,plain,(
    k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK3),k4_xboole_0(k2_tarski(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f30,f33,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    k1_tarski(sK2) = k3_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:08:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (16204)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.55  % (16202)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.55  % (16203)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.56  % (16211)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.56  % (16220)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.53/0.56  % (16218)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.53/0.56  % (16212)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.53/0.57  % (16202)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f140,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(subsumption_resolution,[],[f139,f32])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    sK2 != sK3),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    sK2 != sK3 & r2_hidden(sK3,sK4) & k1_tarski(sK2) = k3_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2)) => (sK2 != sK3 & r2_hidden(sK3,sK4) & k1_tarski(sK2) = k3_xboole_0(k2_tarski(sK2,sK3),sK4))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f10,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.53/0.57    inference(ennf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.53/0.57    inference(negated_conjecture,[],[f8])).
% 1.53/0.57  fof(f8,conjecture,(
% 1.53/0.57    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 1.53/0.57  % (16225)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.53/0.57  fof(f139,plain,(
% 1.53/0.57    sK2 = sK3),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f138])).
% 1.53/0.57  fof(f138,plain,(
% 1.53/0.57    sK2 = sK3 | sK2 = sK3),
% 1.53/0.57    inference(resolution,[],[f135,f121])).
% 1.53/0.57  fof(f121,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.53/0.57    inference(resolution,[],[f46,f60])).
% 1.53/0.57  fof(f60,plain,(
% 1.53/0.57    ( ! [X0,X1] : (sP1(X1,X0,k2_tarski(X0,X1))) )),
% 1.53/0.57    inference(equality_resolution,[],[f52])).
% 1.53/0.57  fof(f52,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.53/0.57    inference(cnf_transformation,[],[f29])).
% 1.53/0.57  fof(f29,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.53/0.57    inference(nnf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.53/0.57    inference(definition_folding,[],[f5,f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.53/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.53/0.57    inference(cnf_transformation,[],[f28])).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.53/0.57    inference(rectify,[],[f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.53/0.57    inference(flattening,[],[f24])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.53/0.57    inference(nnf_transformation,[],[f14])).
% 1.53/0.57  fof(f135,plain,(
% 1.53/0.57    r2_hidden(sK3,k2_tarski(sK2,sK2))),
% 1.53/0.57    inference(subsumption_resolution,[],[f133,f31])).
% 1.53/0.57  fof(f31,plain,(
% 1.53/0.57    r2_hidden(sK3,sK4)),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f133,plain,(
% 1.53/0.57    r2_hidden(sK3,k2_tarski(sK2,sK2)) | ~r2_hidden(sK3,sK4)),
% 1.53/0.57    inference(resolution,[],[f131,f65])).
% 1.53/0.57  fof(f65,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 1.53/0.57    inference(resolution,[],[f58,f60])).
% 1.53/0.57  fof(f58,plain,(
% 1.53/0.57    ( ! [X4,X2,X1] : (~sP1(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.53/0.57    inference(equality_resolution,[],[f48])).
% 1.53/0.57  fof(f48,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP1(X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f28])).
% 1.53/0.57  fof(f131,plain,(
% 1.53/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK2,sK3)) | r2_hidden(X1,k2_tarski(sK2,sK2)) | ~r2_hidden(X1,sK4)) )),
% 1.53/0.57    inference(resolution,[],[f99,f82])).
% 1.53/0.57  fof(f82,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(resolution,[],[f39,f57])).
% 1.53/0.57  fof(f57,plain,(
% 1.53/0.57    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.53/0.57    inference(equality_resolution,[],[f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.57    inference(cnf_transformation,[],[f23])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.57    inference(nnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.53/0.57    inference(definition_folding,[],[f1,f12])).
% 1.53/0.57  fof(f12,plain,(
% 1.53/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f22])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.53/0.57    inference(rectify,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.53/0.57    inference(flattening,[],[f18])).
% 1.53/0.57  fof(f18,plain,(
% 1.53/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.53/0.57    inference(nnf_transformation,[],[f12])).
% 1.53/0.57  fof(f99,plain,(
% 1.53/0.57    ( ! [X3] : (r2_hidden(X3,k4_xboole_0(k2_tarski(sK2,sK3),sK4)) | ~r2_hidden(X3,k2_tarski(sK2,sK3)) | r2_hidden(X3,k2_tarski(sK2,sK2))) )),
% 1.53/0.57    inference(resolution,[],[f40,f78])).
% 1.53/0.57  fof(f78,plain,(
% 1.53/0.57    sP0(k4_xboole_0(k2_tarski(sK2,sK3),sK4),k2_tarski(sK2,sK3),k2_tarski(sK2,sK2))),
% 1.53/0.57    inference(superposition,[],[f57,f54])).
% 1.53/0.57  fof(f54,plain,(
% 1.53/0.57    k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK3),k4_xboole_0(k2_tarski(sK2,sK3),sK4))),
% 1.53/0.57    inference(definition_unfolding,[],[f30,f33,f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    k1_tarski(sK2) = k3_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f22])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (16202)------------------------------
% 1.53/0.57  % (16202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (16202)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (16202)Memory used [KB]: 10746
% 1.53/0.57  % (16202)Time elapsed: 0.126 s
% 1.53/0.57  % (16202)------------------------------
% 1.53/0.57  % (16202)------------------------------
% 1.53/0.57  % (16212)Refutation not found, incomplete strategy% (16212)------------------------------
% 1.53/0.57  % (16212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (16212)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (16212)Memory used [KB]: 10618
% 1.53/0.57  % (16212)Time elapsed: 0.125 s
% 1.53/0.57  % (16212)------------------------------
% 1.53/0.57  % (16212)------------------------------
% 1.53/0.57  % (16207)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.57  % (16195)Success in time 0.199 s
%------------------------------------------------------------------------------
