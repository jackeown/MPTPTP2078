%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (1021 expanded)
%              Number of leaves         :   23 ( 306 expanded)
%              Depth                    :   23
%              Number of atoms          :  599 (3879 expanded)
%              Number of equality atoms :  276 (1032 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f119,f289,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f106])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f104])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f289,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f288,f241])).

fof(f241,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f240,f219])).

fof(f219,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f213,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f213,plain,(
    r1_tarski(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f52,f51,f200,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f200,plain,(
    r1_ordinal1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f52,f51,f193,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f193,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f192,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f192,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f188,f52])).

fof(f188,plain,
    ( ~ v3_ordinal1(sK2)
    | r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f165,f150])).

fof(f150,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f108,f121])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f71,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f104])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f108,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ r1_ordinal1(sK1,sK2) ),
    inference(definition_unfolding,[],[f54,f107])).

fof(f107,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f56,f105,f106])).

fof(f56,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f54,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_ordinal1(sK1,sK2)
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( r1_ordinal1(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK1,X1)
            | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK1,X1)
            | r2_hidden(sK1,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK1,X1)
          | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK1,X1)
          | r2_hidden(sK1,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK1,sK2)
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( r1_ordinal1(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

% (8666)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f165,plain,(
    ! [X0] :
      ( r1_ordinal1(sK1,X0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X0] :
      ( r1_ordinal1(sK1,X0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f138,f136])).

% (8668)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f136,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f51,f61])).

fof(f138,plain,(
    ! [X2] :
      ( r1_ordinal1(sK1,X2)
      | r1_ordinal1(X2,sK1)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f51,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f240,plain,
    ( sK1 = sK2
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f239,f51])).

fof(f239,plain,
    ( sK1 = sK2
    | r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f237,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK2)
      | r1_tarski(X0,sK2)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f52,f61])).

fof(f237,plain,
    ( r1_ordinal1(sK1,sK2)
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,
    ( sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | r1_ordinal1(sK1,sK2) ),
    inference(resolution,[],[f198,f131])).

fof(f131,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) )
      & ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ),
    inference(definition_folding,[],[f28,f29])).

fof(f29,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f198,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
      | sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK1 = X5
      | sK1 = X6
      | sK1 = X7
      | r1_ordinal1(sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f197,f193])).

fof(f197,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(sK1,sK2)
      | r1_ordinal1(sK1,sK2)
      | sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK1 = X5
      | sK1 = X6
      | sK1 = X7
      | ~ sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ) ),
    inference(resolution,[],[f155,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ r2_hidden(X10,X8)
      | X1 = X10
      | X2 = X10
      | X3 = X10
      | X4 = X10
      | X5 = X10
      | X6 = X10
      | X7 = X10
      | X0 = X10
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

% (8691)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f48,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X0 != X9
              & X1 != X9
              & X2 != X9
              & X3 != X9
              & X4 != X9
              & X5 != X9
              & X6 != X9
              & X7 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X0 = X9
            | X1 = X9
            | X2 = X9
            | X3 = X9
            | X4 = X9
            | X5 = X9
            | X6 = X9
            | X7 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9
                & X7 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | X7 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f155,plain,
    ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,sK2)
    | r1_ordinal1(sK1,sK2) ),
    inference(resolution,[],[f109,f122])).

fof(f122,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f70,f105])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | r1_ordinal1(sK1,sK2) ),
    inference(definition_unfolding,[],[f53,f107])).

fof(f53,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f288,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f251,f135])).

fof(f135,plain,(
    r1_ordinal1(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f51,f118,f51,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f251,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(backward_demodulation,[],[f151,f241])).

fof(f151,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r1_ordinal1(sK1,sK2) ),
    inference(resolution,[],[f108,f120])).

fof(f120,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f72,f105])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (8677)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.49  % (8677)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (8669)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f327,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f119,f289,f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f66,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f55,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f59,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f69,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f76,f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f77,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f78,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f288,f241])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    sK1 = sK2),
% 0.20/0.49    inference(subsumption_resolution,[],[f240,f219])).
% 0.20/0.49  fof(f219,plain,(
% 0.20/0.49    ~r1_tarski(sK1,sK2) | sK1 = sK2),
% 0.20/0.49    inference(resolution,[],[f213,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    r1_tarski(sK2,sK1)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f51,f200,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    r1_ordinal1(sK2,sK1)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f51,f193,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f192,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    r1_tarski(sK2,sK1) | ~r2_hidden(sK1,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f188,f52])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ~v3_ordinal1(sK2) | r1_tarski(sK2,sK1) | ~r2_hidden(sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f165,f150])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f108,f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.50    inference(definition_unfolding,[],[f71,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f58,f104])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(rectify,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(flattening,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~r1_ordinal1(sK1,sK2)),
% 0.20/0.50    inference(definition_unfolding,[],[f54,f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f56,f105,f106])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.51  % (8666)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ( ! [X0] : (r1_ordinal1(sK1,X0) | ~v3_ordinal1(X0) | r1_tarski(X0,sK1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    ( ! [X0] : (r1_ordinal1(sK1,X0) | ~v3_ordinal1(X0) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f138,f136])).
% 0.20/0.51  % (8668)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_ordinal1(X0,sK1) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f51,f61])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ( ! [X2] : (r1_ordinal1(sK1,X2) | r1_ordinal1(X2,sK1) | ~v3_ordinal1(X2)) )),
% 0.20/0.51    inference(resolution,[],[f51,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    v3_ordinal1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    v3_ordinal1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    sK1 = sK2 | r1_tarski(sK1,sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f239,f51])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    sK1 = sK2 | r1_tarski(sK1,sK2) | ~v3_ordinal1(sK1)),
% 0.20/0.51    inference(resolution,[],[f237,f144])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_ordinal1(X0,sK2) | r1_tarski(X0,sK2) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f52,f61])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    r1_ordinal1(sK1,sK2) | sK1 = sK2),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f236])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | r1_ordinal1(sK1,sK2)),
% 0.20/0.51    inference(resolution,[],[f198,f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.20/0.51    inference(equality_resolution,[],[f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)) & (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.20/0.51    inference(nnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8))),
% 0.20/0.51    inference(definition_folding,[],[f28,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK1 = X5 | sK1 = X6 | sK1 = X7 | r1_ordinal1(sK1,sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f197,f193])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(sK1,sK2) | r1_ordinal1(sK1,sK2) | sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK1 = X5 | sK1 = X6 | sK1 = X7 | ~sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) )),
% 0.20/0.51    inference(resolution,[],[f155,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (~r2_hidden(X10,X8) | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X0 = X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 0.20/0.51  % (8691)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8))) => (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.20/0.51    inference(rectify,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 0.20/0.51    inference(flattening,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 0.20/0.51    inference(nnf_transformation,[],[f29])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK1,sK2) | r1_ordinal1(sK1,sK2)),
% 0.20/0.51    inference(resolution,[],[f109,f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f70,f105])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r1_ordinal1(sK1,sK2)),
% 0.20/0.51    inference(definition_unfolding,[],[f53,f107])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f251,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    r1_ordinal1(sK1,sK1)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f51,f118,f51,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    ~r1_ordinal1(sK1,sK1) | ~r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 0.20/0.51    inference(backward_demodulation,[],[f151,f241])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~r1_ordinal1(sK1,sK2)),
% 0.20/0.51    inference(resolution,[],[f108,f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f72,f105])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (8677)------------------------------
% 0.20/0.51  % (8677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8677)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (8677)Memory used [KB]: 6396
% 0.20/0.51  % (8677)Time elapsed: 0.088 s
% 0.20/0.51  % (8677)------------------------------
% 0.20/0.51  % (8677)------------------------------
% 0.20/0.51  % (8675)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (8665)Success in time 0.153 s
%------------------------------------------------------------------------------
