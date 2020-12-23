%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 366 expanded)
%              Number of leaves         :   11 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          :  254 (1498 expanded)
%              Number of equality atoms :   80 ( 315 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f140])).

fof(f140,plain,(
    r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f121,f80])).

fof(f80,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f79])).

% (31302)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f79,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

% (31295)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_enumset1(X0,X0,X0,X0))
      | r2_hidden(sK1,k11_relat_1(sK2,X0))
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f109,f91])).

fof(f91,plain,(
    ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f109,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k9_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,X0)
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(subsumption_resolution,[],[f107,f98])).

fof(f98,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f95,f36])).

fof(f36,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),sK2)
      | r2_hidden(X7,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | r2_hidden(sK1,k9_relat_1(sK2,X0))
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(resolution,[],[f94,f36])).

fof(f94,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X6),sK2)
      | ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X4,k1_relat_1(sK2))
      | r2_hidden(X6,k9_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f171,plain,(
    ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f170,f91])).

fof(f170,plain,(
    ~ r2_hidden(sK1,k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(subsumption_resolution,[],[f166,f145])).

fof(f145,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f140,f37])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f166,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f92,f162])).

fof(f162,plain,(
    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2)
    | sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2) ),
    inference(resolution,[],[f146,f83])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f146,plain,(
    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f140,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1,k2_enumset1(X0,X0,X0,X0),sK2),k2_enumset1(X0,X0,X0,X0))
      | ~ r2_hidden(X1,k11_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f93,f91])).

fof(f93,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(sK2,X3))
      | r2_hidden(sK3(X2,X3,sK2),X3) ) ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,sK2),X0),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.51  % (31275)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (31301)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.51  % (31289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.51  % (31287)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.51  % (31290)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.52  % (31282)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (31283)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.52  % (31276)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (31291)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.52  % (31296)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.52  % (31279)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (31287)Refutation not found, incomplete strategy% (31287)------------------------------
% 0.19/0.53  % (31287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (31287)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (31287)Memory used [KB]: 10746
% 0.19/0.53  % (31287)Time elapsed: 0.104 s
% 0.19/0.53  % (31287)------------------------------
% 0.19/0.53  % (31287)------------------------------
% 0.19/0.53  % (31305)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.53  % (31278)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.53  % (31280)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.53  % (31277)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.53  % (31303)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (31285)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.53  % (31304)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (31289)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f172,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(subsumption_resolution,[],[f171,f140])).
% 0.19/0.54  fof(f140,plain,(
% 0.19/0.54    r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f131])).
% 0.19/0.54  fof(f131,plain,(
% 0.19/0.54    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.19/0.54    inference(resolution,[],[f121,f80])).
% 0.19/0.54  fof(f80,plain,(
% 0.19/0.54    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 0.19/0.54    inference(equality_resolution,[],[f79])).
% 0.19/0.54  % (31302)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.54  fof(f79,plain,(
% 0.19/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 0.19/0.54    inference(equality_resolution,[],[f68])).
% 0.19/0.54  fof(f68,plain,(
% 0.19/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.19/0.54    inference(definition_unfolding,[],[f50,f62])).
% 0.19/0.54  fof(f62,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f40,f41])).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.54  fof(f40,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.54  fof(f50,plain,(
% 0.19/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  % (31295)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.54    inference(rectify,[],[f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.54    inference(flattening,[],[f25])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.54    inference(nnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.19/0.54  fof(f121,plain,(
% 0.19/0.54    ( ! [X0] : (~r2_hidden(sK0,k2_enumset1(X0,X0,X0,X0)) | r2_hidden(sK1,k11_relat_1(sK2,X0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 0.19/0.54    inference(superposition,[],[f109,f91])).
% 0.19/0.54  fof(f91,plain,(
% 0.19/0.54    ( ! [X0] : (k11_relat_1(sK2,X0) = k9_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))) )),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f35,f64])).
% 0.19/0.54  fof(f64,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.19/0.54    inference(definition_unfolding,[],[f39,f63])).
% 0.19/0.54  fof(f63,plain,(
% 0.19/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f38,f62])).
% 0.19/0.54  fof(f38,plain,(
% 0.19/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f3])).
% 0.19/0.54  fof(f3,axiom,(
% 0.19/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.54  fof(f39,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f12])).
% 0.19/0.54  fof(f12,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    v1_relat_1(sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f20])).
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    (~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2)),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.19/0.54  fof(f19,plain,(
% 0.19/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2)) => ((~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 0.19/0.54    inference(flattening,[],[f17])).
% 0.19/0.54  fof(f17,plain,(
% 0.19/0.54    ? [X0,X1,X2] : (((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2))) & v1_relat_1(X2))),
% 0.19/0.54    inference(nnf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,plain,(
% 0.19/0.54    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r2_hidden(X1,k11_relat_1(X2,X0))) & v1_relat_1(X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f10])).
% 0.19/0.54  fof(f10,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.19/0.54    inference(negated_conjecture,[],[f9])).
% 0.19/0.54  fof(f9,conjecture,(
% 0.19/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.19/0.54  fof(f109,plain,(
% 0.19/0.54    ( ! [X0] : (r2_hidden(sK1,k9_relat_1(sK2,X0)) | ~r2_hidden(sK0,X0) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 0.19/0.54    inference(subsumption_resolution,[],[f107,f98])).
% 0.19/0.54  fof(f98,plain,(
% 0.19/0.54    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.19/0.54    inference(resolution,[],[f95,f36])).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    r2_hidden(k4_tarski(sK0,sK1),sK2) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.19/0.54    inference(cnf_transformation,[],[f20])).
% 0.19/0.54  fof(f95,plain,(
% 0.19/0.54    ( ! [X8,X7] : (~r2_hidden(k4_tarski(X7,X8),sK2) | r2_hidden(X7,k1_relat_1(sK2))) )),
% 0.19/0.54    inference(resolution,[],[f35,f42])).
% 0.19/0.54  fof(f42,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(flattening,[],[f13])).
% 0.19/0.54  fof(f13,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.19/0.54  fof(f107,plain,(
% 0.19/0.54    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK1,k9_relat_1(sK2,X0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 0.19/0.54    inference(resolution,[],[f94,f36])).
% 0.19/0.54  fof(f94,plain,(
% 0.19/0.54    ( ! [X6,X4,X5] : (~r2_hidden(k4_tarski(X4,X6),sK2) | ~r2_hidden(X4,X5) | ~r2_hidden(X4,k1_relat_1(sK2)) | r2_hidden(X6,k9_relat_1(sK2,X5))) )),
% 0.19/0.54    inference(resolution,[],[f35,f47])).
% 0.19/0.54  fof(f47,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f24])).
% 0.19/0.54  fof(f24,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f22,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(rectify,[],[f21])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(nnf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.19/0.54  fof(f171,plain,(
% 0.19/0.54    ~r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.19/0.54    inference(forward_demodulation,[],[f170,f91])).
% 0.19/0.54  fof(f170,plain,(
% 0.19/0.54    ~r2_hidden(sK1,k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.19/0.54    inference(subsumption_resolution,[],[f166,f145])).
% 0.19/0.54  fof(f145,plain,(
% 0.19/0.54    ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f140,f37])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    ~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f20])).
% 0.19/0.54  fof(f166,plain,(
% 0.19/0.54    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k9_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.19/0.54    inference(superposition,[],[f92,f162])).
% 0.19/0.54  fof(f162,plain,(
% 0.19/0.54    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2)),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f159])).
% 0.19/0.54  fof(f159,plain,(
% 0.19/0.54    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2) | sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2)),
% 0.19/0.54    inference(resolution,[],[f146,f83])).
% 0.19/0.54  fof(f83,plain,(
% 0.19/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.19/0.54    inference(equality_resolution,[],[f70])).
% 0.19/0.54  fof(f70,plain,(
% 0.19/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.19/0.54    inference(definition_unfolding,[],[f48,f62])).
% 0.19/0.54  fof(f48,plain,(
% 0.19/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f146,plain,(
% 0.19/0.54    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f140,f104])).
% 0.19/0.54  fof(f104,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X1,k2_enumset1(X0,X0,X0,X0),sK2),k2_enumset1(X0,X0,X0,X0)) | ~r2_hidden(X1,k11_relat_1(sK2,X0))) )),
% 0.19/0.54    inference(superposition,[],[f93,f91])).
% 0.19/0.54  fof(f93,plain,(
% 0.19/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k9_relat_1(sK2,X3)) | r2_hidden(sK3(X2,X3,sK2),X3)) )),
% 0.19/0.54    inference(resolution,[],[f35,f46])).
% 0.19/0.54  fof(f46,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f24])).
% 0.19/0.54  fof(f92,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,sK2),X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.19/0.54    inference(resolution,[],[f35,f45])).
% 0.19/0.54  fof(f45,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f24])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (31289)------------------------------
% 0.19/0.54  % (31289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31289)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (31289)Memory used [KB]: 6396
% 0.19/0.54  % (31289)Time elapsed: 0.137 s
% 0.19/0.54  % (31289)------------------------------
% 0.19/0.54  % (31289)------------------------------
% 0.19/0.54  % (31270)Success in time 0.185 s
%------------------------------------------------------------------------------
