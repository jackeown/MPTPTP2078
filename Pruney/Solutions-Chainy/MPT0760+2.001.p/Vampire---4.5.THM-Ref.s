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
% DateTime   : Thu Dec  3 12:55:50 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  248 ( 319 expanded)
%              Number of equality atoms :   58 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(resolution,[],[f217,f51])).

fof(f51,plain,(
    ~ r2_hidden(sK3,k3_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k1_wellord1(sK4,sK3)
    & ~ r2_hidden(sK3,k3_relat_1(sK4))
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != k1_wellord1(X1,X0)
        & ~ r2_hidden(X0,k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_xboole_0 != k1_wellord1(sK4,sK3)
      & ~ r2_hidden(sK3,k3_relat_1(sK4))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

fof(f217,plain,(
    r2_hidden(sK3,k3_relat_1(sK4)) ),
    inference(resolution,[],[f171,f105])).

fof(f105,plain,(
    r1_tarski(k2_relat_1(sK4),k3_relat_1(sK4)) ),
    inference(superposition,[],[f66,f103])).

fof(f103,plain,(
    k3_relat_1(sK4) = k2_xboole_0(k2_relat_1(sK4),k1_relat_1(sK4)) ),
    inference(resolution,[],[f94,f50])).

fof(f50,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k2_relat_1(X0),k1_relat_1(X0)) ) ),
    inference(backward_demodulation,[],[f56,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f56,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f171,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(sK4),X2)
      | r2_hidden(sK3,X2) ) ),
    inference(resolution,[],[f153,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

% (3848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f153,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(resolution,[],[f139,f90])).

fof(f90,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f139,plain,(
    r2_hidden(k4_tarski(sK5(sK4,sK3,k1_xboole_0),sK3),sK4) ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK5(sK4,sK3,k1_xboole_0),sK3),sK4) ),
    inference(superposition,[],[f52,f126])).

fof(f126,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_wellord1(sK4,X2)
      | r2_hidden(k4_tarski(sK5(sK4,X2,k1_xboole_0),X2),sK4) ) ),
    inference(resolution,[],[f119,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f119,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X8,sK5(sK4,X7,X8))
      | k1_wellord1(sK4,X7) = X8
      | r2_hidden(k4_tarski(sK5(sK4,X7,X8),X7),sK4) ) ),
    inference(resolution,[],[f116,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK4,X0,X1),X1)
      | r2_hidden(k4_tarski(sK5(sK4,X0,X1),X0),sK4)
      | k1_wellord1(sK4,X0) = X1 ) ),
    inference(resolution,[],[f63,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK4,X0,X1)
      | k1_wellord1(sK4,X0) = X1 ) ),
    inference(resolution,[],[f106,f50])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_wellord1(X0,X1) = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f22,f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,X1),X0)
            & X1 != X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (3847)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1,X2)
      | k1_wellord1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
            | sK5(X0,X1,X2) = X1
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
              & sK5(X0,X1,X2) != X1 )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
          | sK5(X0,X1,X2) = X1
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
            & sK5(X0,X1,X2) != X1 )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3 )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3 )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f52,plain,(
    k1_xboole_0 != k1_wellord1(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.57  % (3838)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (3844)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (3854)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.58  % (3852)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.58  % (3846)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.58  % (3840)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.58  % (3836)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.58  % (3832)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.59  % (3836)Refutation not found, incomplete strategy% (3836)------------------------------
% 1.58/0.59  % (3836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (3836)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (3836)Memory used [KB]: 10618
% 1.58/0.59  % (3836)Time elapsed: 0.148 s
% 1.58/0.59  % (3836)------------------------------
% 1.58/0.59  % (3836)------------------------------
% 1.58/0.60  % (3838)Refutation found. Thanks to Tanya!
% 1.58/0.60  % SZS status Theorem for theBenchmark
% 1.58/0.60  % SZS output start Proof for theBenchmark
% 1.58/0.60  fof(f221,plain,(
% 1.58/0.60    $false),
% 1.58/0.60    inference(resolution,[],[f217,f51])).
% 1.58/0.60  fof(f51,plain,(
% 1.58/0.60    ~r2_hidden(sK3,k3_relat_1(sK4))),
% 1.58/0.60    inference(cnf_transformation,[],[f27])).
% 1.58/0.60  fof(f27,plain,(
% 1.58/0.60    k1_xboole_0 != k1_wellord1(sK4,sK3) & ~r2_hidden(sK3,k3_relat_1(sK4)) & v1_relat_1(sK4)),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f26])).
% 1.58/0.60  fof(f26,plain,(
% 1.58/0.60    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1)) => (k1_xboole_0 != k1_wellord1(sK4,sK3) & ~r2_hidden(sK3,k3_relat_1(sK4)) & v1_relat_1(sK4))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f16,plain,(
% 1.58/0.60    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 1.58/0.60    inference(flattening,[],[f15])).
% 1.58/0.60  fof(f15,plain,(
% 1.58/0.60    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 1.58/0.60    inference(ennf_transformation,[],[f14])).
% 1.58/0.60  fof(f14,negated_conjecture,(
% 1.58/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 1.58/0.60    inference(negated_conjecture,[],[f13])).
% 1.58/0.60  fof(f13,conjecture,(
% 1.58/0.60    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).
% 1.58/0.60  fof(f217,plain,(
% 1.58/0.60    r2_hidden(sK3,k3_relat_1(sK4))),
% 1.58/0.60    inference(resolution,[],[f171,f105])).
% 1.58/0.60  fof(f105,plain,(
% 1.58/0.60    r1_tarski(k2_relat_1(sK4),k3_relat_1(sK4))),
% 1.58/0.60    inference(superposition,[],[f66,f103])).
% 1.58/0.60  fof(f103,plain,(
% 1.58/0.60    k3_relat_1(sK4) = k2_xboole_0(k2_relat_1(sK4),k1_relat_1(sK4))),
% 1.58/0.60    inference(resolution,[],[f94,f50])).
% 1.58/0.60  fof(f50,plain,(
% 1.58/0.60    v1_relat_1(sK4)),
% 1.58/0.60    inference(cnf_transformation,[],[f27])).
% 1.58/0.60  fof(f94,plain,(
% 1.58/0.60    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) )),
% 1.58/0.60    inference(backward_demodulation,[],[f56,f67])).
% 1.58/0.60  fof(f67,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f1])).
% 1.58/0.60  fof(f1,axiom,(
% 1.58/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.58/0.60  fof(f56,plain,(
% 1.58/0.60    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f17])).
% 1.58/0.60  fof(f17,plain,(
% 1.58/0.60    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.58/0.60    inference(ennf_transformation,[],[f10])).
% 1.58/0.60  fof(f10,axiom,(
% 1.58/0.60    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.58/0.60  fof(f66,plain,(
% 1.58/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f8])).
% 1.58/0.60  fof(f8,axiom,(
% 1.58/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.58/0.60  fof(f171,plain,(
% 1.58/0.60    ( ! [X2] : (~r1_tarski(k2_relat_1(sK4),X2) | r2_hidden(sK3,X2)) )),
% 1.58/0.60    inference(resolution,[],[f153,f69])).
% 1.58/0.60  fof(f69,plain,(
% 1.58/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f37])).
% 1.58/0.60  fof(f37,plain,(
% 1.58/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 1.58/0.60  % (3848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.60  fof(f36,plain,(
% 1.58/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f35,plain,(
% 1.58/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.60    inference(rectify,[],[f34])).
% 1.58/0.60  fof(f34,plain,(
% 1.58/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.60    inference(nnf_transformation,[],[f19])).
% 1.58/0.60  fof(f19,plain,(
% 1.58/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.58/0.60    inference(ennf_transformation,[],[f2])).
% 1.58/0.60  fof(f2,axiom,(
% 1.58/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.58/0.60  fof(f153,plain,(
% 1.58/0.60    r2_hidden(sK3,k2_relat_1(sK4))),
% 1.58/0.60    inference(resolution,[],[f139,f90])).
% 1.58/0.60  fof(f90,plain,(
% 1.58/0.60    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 1.58/0.60    inference(equality_resolution,[],[f73])).
% 1.58/0.60  fof(f73,plain,(
% 1.58/0.60    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.58/0.60    inference(cnf_transformation,[],[f43])).
% 1.58/0.60  fof(f43,plain,(
% 1.58/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).
% 1.58/0.60  fof(f40,plain,(
% 1.58/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f41,plain,(
% 1.58/0.60    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f42,plain,(
% 1.58/0.60    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f39,plain,(
% 1.58/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.58/0.60    inference(rectify,[],[f38])).
% 1.58/0.60  fof(f38,plain,(
% 1.58/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.58/0.60    inference(nnf_transformation,[],[f9])).
% 1.58/0.60  fof(f9,axiom,(
% 1.58/0.60    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.58/0.60  fof(f139,plain,(
% 1.58/0.60    r2_hidden(k4_tarski(sK5(sK4,sK3,k1_xboole_0),sK3),sK4)),
% 1.58/0.60    inference(trivial_inequality_removal,[],[f137])).
% 1.58/0.60  fof(f137,plain,(
% 1.58/0.60    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK5(sK4,sK3,k1_xboole_0),sK3),sK4)),
% 1.58/0.60    inference(superposition,[],[f52,f126])).
% 1.58/0.60  fof(f126,plain,(
% 1.58/0.60    ( ! [X2] : (k1_xboole_0 = k1_wellord1(sK4,X2) | r2_hidden(k4_tarski(sK5(sK4,X2,k1_xboole_0),X2),sK4)) )),
% 1.58/0.60    inference(resolution,[],[f119,f53])).
% 1.58/0.60  fof(f53,plain,(
% 1.58/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f5])).
% 1.58/0.60  fof(f5,axiom,(
% 1.58/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.58/0.60  fof(f119,plain,(
% 1.58/0.60    ( ! [X8,X7] : (~r1_tarski(X8,sK5(sK4,X7,X8)) | k1_wellord1(sK4,X7) = X8 | r2_hidden(k4_tarski(sK5(sK4,X7,X8),X7),sK4)) )),
% 1.58/0.60    inference(resolution,[],[f116,f76])).
% 1.58/0.60  fof(f76,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f20])).
% 1.58/0.60  fof(f20,plain,(
% 1.58/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.58/0.60    inference(ennf_transformation,[],[f11])).
% 1.58/0.60  fof(f11,axiom,(
% 1.58/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.58/0.60  fof(f116,plain,(
% 1.58/0.60    ( ! [X0,X1] : (r2_hidden(sK5(sK4,X0,X1),X1) | r2_hidden(k4_tarski(sK5(sK4,X0,X1),X0),sK4) | k1_wellord1(sK4,X0) = X1) )),
% 1.58/0.60    inference(resolution,[],[f63,f112])).
% 1.58/0.60  fof(f112,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~sP0(sK4,X0,X1) | k1_wellord1(sK4,X0) = X1) )),
% 1.58/0.60    inference(resolution,[],[f106,f50])).
% 1.58/0.60  fof(f106,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_wellord1(X0,X1) = X2 | ~sP0(X0,X1,X2)) )),
% 1.58/0.60    inference(resolution,[],[f58,f65])).
% 1.58/0.60  fof(f65,plain,(
% 1.58/0.60    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f23])).
% 1.58/0.60  fof(f23,plain,(
% 1.58/0.60    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 1.58/0.60    inference(definition_folding,[],[f18,f22,f21])).
% 1.58/0.60  fof(f21,plain,(
% 1.58/0.60    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3)))),
% 1.58/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.58/0.60  % (3847)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.60  fof(f22,plain,(
% 1.58/0.60    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 1.58/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.58/0.60  fof(f18,plain,(
% 1.58/0.60    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.58/0.60    inference(ennf_transformation,[],[f12])).
% 1.58/0.60  fof(f12,axiom,(
% 1.58/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.58/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.58/0.60  fof(f58,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~sP1(X0) | ~sP0(X0,X1,X2) | k1_wellord1(X0,X1) = X2) )),
% 1.58/0.60    inference(cnf_transformation,[],[f28])).
% 1.58/0.60  fof(f28,plain,(
% 1.58/0.60    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k1_wellord1(X0,X1) != X2)) | ~sP1(X0))),
% 1.58/0.60    inference(nnf_transformation,[],[f22])).
% 1.58/0.60  fof(f63,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f33])).
% 1.58/0.60  fof(f33,plain,(
% 1.58/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | sK5(X0,X1,X2) = X1 | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) & sK5(X0,X1,X2) != X1) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.58/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 1.58/0.60  fof(f32,plain,(
% 1.58/0.60    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) | sK5(X0,X1,X2) = X1 | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0) & sK5(X0,X1,X2) != X1) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.58/0.60    introduced(choice_axiom,[])).
% 1.58/0.60  fof(f31,plain,(
% 1.58/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.58/0.60    inference(rectify,[],[f30])).
% 1.58/0.60  fof(f30,plain,(
% 1.58/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 1.58/0.60    inference(flattening,[],[f29])).
% 1.58/0.60  fof(f29,plain,(
% 1.58/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 1.58/0.60    inference(nnf_transformation,[],[f21])).
% 1.58/0.60  fof(f52,plain,(
% 1.58/0.60    k1_xboole_0 != k1_wellord1(sK4,sK3)),
% 1.58/0.60    inference(cnf_transformation,[],[f27])).
% 1.58/0.60  % SZS output end Proof for theBenchmark
% 1.58/0.60  % (3838)------------------------------
% 1.58/0.60  % (3838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (3838)Termination reason: Refutation
% 1.58/0.60  
% 1.58/0.60  % (3838)Memory used [KB]: 6268
% 1.58/0.60  % (3838)Time elapsed: 0.159 s
% 1.58/0.60  % (3838)------------------------------
% 1.58/0.60  % (3838)------------------------------
% 1.58/0.60  % (3825)Success in time 0.225 s
%------------------------------------------------------------------------------
