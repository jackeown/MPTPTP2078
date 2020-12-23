%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:09 EST 2020

% Result     : Theorem 3.07s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 461 expanded)
%              Number of leaves         :   35 ( 138 expanded)
%              Depth                    :   19
%              Number of atoms          :  492 (1630 expanded)
%              Number of equality atoms :  110 ( 326 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3992,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3991,f2379])).

fof(f2379,plain,(
    ~ r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f2371,f77])).

fof(f77,plain,(
    ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(X1))
          & r1_tarski(sK1,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(X1))
        & r1_tarski(sK1,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f2371,plain,
    ( r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(resolution,[],[f317,f918])).

fof(f918,plain,(
    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(resolution,[],[f890,f504])).

fof(f504,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK2))
      | r1_tarski(X2,k3_relat_1(sK2)) ) ),
    inference(superposition,[],[f124,f291])).

fof(f291,plain,(
    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f120,f75])).

fof(f75,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f82,f119])).

fof(f119,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f89,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f82,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f105,f119])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f890,plain,(
    r1_tarski(k2_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f827,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f170,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k6_subset_1(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(extensionality_resolution,[],[f96,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f101,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f827,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f403,f795])).

fof(f795,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f794,f141])).

fof(f141,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f81,f78])).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f794,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f786,f749])).

fof(f749,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f744,f168])).

fof(f168,plain,(
    ! [X17,X18,X16] :
      ( ~ r1_xboole_0(X16,k1_enumset1(X17,X17,X18))
      | ~ r2_hidden(X18,X16) ) ),
    inference(resolution,[],[f92,f144])).

fof(f144,plain,(
    ! [X2,X3] : r2_hidden(X2,k1_enumset1(X3,X3,X2)) ),
    inference(resolution,[],[f138,f136])).

fof(f136,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK11(X0,X1,X2) != X0
              & sK11(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sK11(X0,X1,X2) = X0
            | sK11(X0,X1,X2) = X1
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK11(X0,X1,X2) != X0
            & sK11(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sK11(X0,X1,X2) = X0
          | sK11(X0,X1,X2) = X1
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f138,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f117,f88])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f13,f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f744,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f742,f79])).

fof(f79,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f742,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f738])).

fof(f738,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f163,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f163,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK4(X3,X4),X2)
      | ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f92,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f786,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f221,f765])).

fof(f765,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f749,f242])).

fof(f242,plain,(
    ! [X3] :
      ( r2_hidden(sK9(X3),X3)
      | k1_xboole_0 = k1_relat_1(X3) ) ),
    inference(resolution,[],[f238,f85])).

fof(f85,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f238,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X6))
      | r2_hidden(sK9(X6),X6) ) ),
    inference(resolution,[],[f135,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK9(X1),X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f64])).

fof(f64,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f135,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f58,f61,f60,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f221,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f93,f85])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f53])).

fof(f53,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK5(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f403,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f402,f74])).

fof(f74,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f402,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f375,f75])).

fof(f375,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f83,f152])).

fof(f152,plain,(
    k1_xboole_0 = k6_subset_1(sK1,sK2) ),
    inference(resolution,[],[f122,f76])).

fof(f76,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f102,f87])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f317,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | r1_tarski(k3_relat_1(sK1),X0)
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f126,f290])).

fof(f290,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f120,f74])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f107,f119])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f3991,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(resolution,[],[f3964,f844])).

fof(f844,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(resolution,[],[f785,f176])).

fof(f785,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f429,f765])).

fof(f429,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f428,f74])).

fof(f428,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f423,f75])).

fof(f423,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f84,f152])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f3964,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | r1_tarski(X0,k3_relat_1(sK2)) ) ),
    inference(superposition,[],[f124,f695])).

fof(f695,plain,(
    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),k1_relat_1(sK2))) ),
    inference(resolution,[],[f573,f506])).

fof(f506,plain,(
    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) ),
    inference(superposition,[],[f121,f291])).

fof(f121,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f86,f119])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f573,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f572,f132])).

fof(f132,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f572,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f569])).

fof(f569,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f129,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK10(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f110,f119])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK10(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK10(X0,X1,X2))
        & r1_tarski(X2,sK10(X0,X1,X2))
        & r1_tarski(X0,sK10(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK10(X0,X1,X2))
        & r1_tarski(X2,sK10(X0,X1,X2))
        & r1_tarski(X0,sK10(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK10(X0,X1,X2))
      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f108,f119])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK10(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (14052)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (14068)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (14054)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (14047)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (14057)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (14046)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (14049)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (14074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (14048)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (14065)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (14075)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (14067)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (14061)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (14059)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (14075)Refutation not found, incomplete strategy% (14075)------------------------------
% 0.21/0.54  % (14075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14075)Memory used [KB]: 1663
% 0.21/0.54  % (14075)Time elapsed: 0.099 s
% 0.21/0.54  % (14075)------------------------------
% 0.21/0.54  % (14075)------------------------------
% 0.21/0.54  % (14062)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (14064)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (14062)Refutation not found, incomplete strategy% (14062)------------------------------
% 0.21/0.54  % (14062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14062)Memory used [KB]: 10746
% 0.21/0.54  % (14062)Time elapsed: 0.140 s
% 0.21/0.54  % (14062)------------------------------
% 0.21/0.54  % (14062)------------------------------
% 0.21/0.54  % (14072)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (14069)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (14070)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (14066)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (14073)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (14055)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (14058)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (14051)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (14056)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (14053)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (14074)Refutation not found, incomplete strategy% (14074)------------------------------
% 0.21/0.56  % (14074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14074)Memory used [KB]: 10746
% 0.21/0.56  % (14074)Time elapsed: 0.148 s
% 0.21/0.56  % (14074)------------------------------
% 0.21/0.56  % (14074)------------------------------
% 0.21/0.56  % (14050)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (14071)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (14056)Refutation not found, incomplete strategy% (14056)------------------------------
% 0.21/0.57  % (14056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14063)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (14056)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14056)Memory used [KB]: 10746
% 0.21/0.57  % (14056)Time elapsed: 0.147 s
% 0.21/0.57  % (14056)------------------------------
% 0.21/0.57  % (14056)------------------------------
% 0.21/0.58  % (14060)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.34/0.68  % (14078)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.34/0.68  % (14078)Refutation not found, incomplete strategy% (14078)------------------------------
% 2.34/0.68  % (14078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.68  % (14078)Termination reason: Refutation not found, incomplete strategy
% 2.34/0.68  
% 2.34/0.68  % (14078)Memory used [KB]: 6140
% 2.34/0.68  % (14078)Time elapsed: 0.062 s
% 2.34/0.68  % (14078)------------------------------
% 2.34/0.68  % (14078)------------------------------
% 2.34/0.70  % (14049)Refutation not found, incomplete strategy% (14049)------------------------------
% 2.34/0.70  % (14049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.70  % (14049)Termination reason: Refutation not found, incomplete strategy
% 2.34/0.70  
% 2.34/0.70  % (14049)Memory used [KB]: 6140
% 2.34/0.70  % (14049)Time elapsed: 0.273 s
% 2.34/0.70  % (14049)------------------------------
% 2.34/0.70  % (14049)------------------------------
% 2.34/0.72  % (14076)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.85/0.74  % (14079)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.85/0.74  % (14077)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.07/0.78  % (14052)Refutation found. Thanks to Tanya!
% 3.07/0.78  % SZS status Theorem for theBenchmark
% 3.07/0.79  % SZS output start Proof for theBenchmark
% 3.07/0.79  fof(f3992,plain,(
% 3.07/0.79    $false),
% 3.07/0.79    inference(subsumption_resolution,[],[f3991,f2379])).
% 3.07/0.79  fof(f2379,plain,(
% 3.07/0.79    ~r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2))),
% 3.07/0.79    inference(subsumption_resolution,[],[f2371,f77])).
% 3.07/0.79  fof(f77,plain,(
% 3.07/0.79    ~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))),
% 3.07/0.79    inference(cnf_transformation,[],[f48])).
% 3.07/0.79  fof(f48,plain,(
% 3.07/0.79    (~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f47,f46])).
% 3.07/0.79  fof(f46,plain,(
% 3.07/0.79    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK1),k3_relat_1(X1)) & r1_tarski(sK1,X1) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f47,plain,(
% 3.07/0.79    ? [X1] : (~r1_tarski(k3_relat_1(sK1),k3_relat_1(X1)) & r1_tarski(sK1,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f28,plain,(
% 3.07/0.79    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.07/0.79    inference(flattening,[],[f27])).
% 3.07/0.79  fof(f27,plain,(
% 3.07/0.79    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.07/0.79    inference(ennf_transformation,[],[f25])).
% 3.07/0.79  fof(f25,negated_conjecture,(
% 3.07/0.79    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.07/0.79    inference(negated_conjecture,[],[f24])).
% 3.07/0.79  fof(f24,conjecture,(
% 3.07/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 3.07/0.79  fof(f2371,plain,(
% 3.07/0.79    r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) | ~r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2))),
% 3.07/0.79    inference(resolution,[],[f317,f918])).
% 3.07/0.79  fof(f918,plain,(
% 3.07/0.79    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2))),
% 3.07/0.79    inference(resolution,[],[f890,f504])).
% 3.07/0.79  fof(f504,plain,(
% 3.07/0.79    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK2)) | r1_tarski(X2,k3_relat_1(sK2))) )),
% 3.07/0.79    inference(superposition,[],[f124,f291])).
% 3.07/0.79  fof(f291,plain,(
% 3.07/0.79    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))),
% 3.07/0.79    inference(resolution,[],[f120,f75])).
% 3.07/0.79  fof(f75,plain,(
% 3.07/0.79    v1_relat_1(sK2)),
% 3.07/0.79    inference(cnf_transformation,[],[f48])).
% 3.07/0.79  fof(f120,plain,(
% 3.07/0.79    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 3.07/0.79    inference(definition_unfolding,[],[f82,f119])).
% 3.07/0.79  fof(f119,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.07/0.79    inference(definition_unfolding,[],[f89,f88])).
% 3.07/0.79  fof(f88,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f14])).
% 3.07/0.79  fof(f14,axiom,(
% 3.07/0.79    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.07/0.79  fof(f89,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.07/0.79    inference(cnf_transformation,[],[f15])).
% 3.07/0.79  fof(f15,axiom,(
% 3.07/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.07/0.79  fof(f82,plain,(
% 3.07/0.79    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f30])).
% 3.07/0.79  fof(f30,plain,(
% 3.07/0.79    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.07/0.79    inference(ennf_transformation,[],[f20])).
% 3.07/0.79  fof(f20,axiom,(
% 3.07/0.79    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 3.07/0.79  fof(f124,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(definition_unfolding,[],[f105,f119])).
% 3.07/0.79  fof(f105,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f38])).
% 3.07/0.79  fof(f38,plain,(
% 3.07/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.07/0.79    inference(ennf_transformation,[],[f6])).
% 3.07/0.79  fof(f6,axiom,(
% 3.07/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.07/0.79  fof(f890,plain,(
% 3.07/0.79    r1_tarski(k2_relat_1(sK1),k2_relat_1(sK2))),
% 3.07/0.79    inference(resolution,[],[f827,f176])).
% 3.07/0.79  fof(f176,plain,(
% 3.07/0.79    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(subsumption_resolution,[],[f170,f80])).
% 3.07/0.79  fof(f80,plain,(
% 3.07/0.79    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f8])).
% 3.07/0.79  fof(f8,axiom,(
% 3.07/0.79    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.07/0.79  fof(f170,plain,(
% 3.07/0.79    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_subset_1(X0,X1)) | r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(extensionality_resolution,[],[f96,f123])).
% 3.07/0.79  fof(f123,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(definition_unfolding,[],[f101,f87])).
% 3.07/0.79  fof(f87,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f17])).
% 3.07/0.79  fof(f17,axiom,(
% 3.07/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.07/0.79  fof(f101,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f63])).
% 3.07/0.79  fof(f63,plain,(
% 3.07/0.79    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.07/0.79    inference(nnf_transformation,[],[f5])).
% 3.07/0.79  fof(f5,axiom,(
% 3.07/0.79    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.07/0.79  fof(f96,plain,(
% 3.07/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f56])).
% 3.07/0.79  fof(f56,plain,(
% 3.07/0.79    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.79    inference(flattening,[],[f55])).
% 3.07/0.79  fof(f55,plain,(
% 3.07/0.79    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.79    inference(nnf_transformation,[],[f4])).
% 3.07/0.79  fof(f4,axiom,(
% 3.07/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.07/0.79  fof(f827,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k1_xboole_0)),
% 3.07/0.79    inference(backward_demodulation,[],[f403,f795])).
% 3.07/0.79  fof(f795,plain,(
% 3.07/0.79    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.07/0.79    inference(subsumption_resolution,[],[f794,f141])).
% 3.07/0.79  fof(f141,plain,(
% 3.07/0.79    v1_relat_1(k1_xboole_0)),
% 3.07/0.79    inference(resolution,[],[f81,f78])).
% 3.07/0.79  fof(f78,plain,(
% 3.07/0.79    v1_xboole_0(k1_xboole_0)),
% 3.07/0.79    inference(cnf_transformation,[],[f1])).
% 3.07/0.79  fof(f1,axiom,(
% 3.07/0.79    v1_xboole_0(k1_xboole_0)),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.07/0.79  fof(f81,plain,(
% 3.07/0.79    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f29])).
% 3.07/0.79  fof(f29,plain,(
% 3.07/0.79    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.07/0.79    inference(ennf_transformation,[],[f18])).
% 3.07/0.79  fof(f18,axiom,(
% 3.07/0.79    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 3.07/0.79  fof(f794,plain,(
% 3.07/0.79    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.07/0.79    inference(subsumption_resolution,[],[f786,f749])).
% 3.07/0.79  fof(f749,plain,(
% 3.07/0.79    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.07/0.79    inference(resolution,[],[f744,f168])).
% 3.07/0.79  fof(f168,plain,(
% 3.07/0.79    ( ! [X17,X18,X16] : (~r1_xboole_0(X16,k1_enumset1(X17,X17,X18)) | ~r2_hidden(X18,X16)) )),
% 3.07/0.79    inference(resolution,[],[f92,f144])).
% 3.07/0.79  fof(f144,plain,(
% 3.07/0.79    ( ! [X2,X3] : (r2_hidden(X2,k1_enumset1(X3,X3,X2))) )),
% 3.07/0.79    inference(resolution,[],[f138,f136])).
% 3.07/0.79  fof(f136,plain,(
% 3.07/0.79    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 3.07/0.79    inference(equality_resolution,[],[f113])).
% 3.07/0.79  fof(f113,plain,(
% 3.07/0.79    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f72])).
% 3.07/0.79  fof(f72,plain,(
% 3.07/0.79    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK11(X0,X1,X2) != X0 & sK11(X0,X1,X2) != X1) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sK11(X0,X1,X2) = X0 | sK11(X0,X1,X2) = X1 | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f70,f71])).
% 3.07/0.79  fof(f71,plain,(
% 3.07/0.79    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK11(X0,X1,X2) != X0 & sK11(X0,X1,X2) != X1) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sK11(X0,X1,X2) = X0 | sK11(X0,X1,X2) = X1 | r2_hidden(sK11(X0,X1,X2),X2))))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f70,plain,(
% 3.07/0.79    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.07/0.79    inference(rectify,[],[f69])).
% 3.07/0.79  fof(f69,plain,(
% 3.07/0.79    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.07/0.79    inference(flattening,[],[f68])).
% 3.07/0.79  fof(f68,plain,(
% 3.07/0.79    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.07/0.79    inference(nnf_transformation,[],[f44])).
% 3.07/0.79  fof(f44,plain,(
% 3.07/0.79    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.07/0.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.07/0.79  fof(f138,plain,(
% 3.07/0.79    ( ! [X0,X1] : (sP0(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 3.07/0.79    inference(equality_resolution,[],[f131])).
% 3.07/0.79  fof(f131,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.07/0.79    inference(definition_unfolding,[],[f117,f88])).
% 3.07/0.79  fof(f117,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 3.07/0.79    inference(cnf_transformation,[],[f73])).
% 3.07/0.79  fof(f73,plain,(
% 3.07/0.79    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 3.07/0.79    inference(nnf_transformation,[],[f45])).
% 3.07/0.79  fof(f45,plain,(
% 3.07/0.79    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.07/0.79    inference(definition_folding,[],[f13,f44])).
% 3.07/0.79  fof(f13,axiom,(
% 3.07/0.79    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 3.07/0.79  fof(f92,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f52])).
% 3.07/0.79  fof(f52,plain,(
% 3.07/0.79    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f51])).
% 3.07/0.79  fof(f51,plain,(
% 3.07/0.79    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f34,plain,(
% 3.07/0.79    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.07/0.79    inference(ennf_transformation,[],[f26])).
% 3.07/0.79  fof(f26,plain,(
% 3.07/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.07/0.79    inference(rectify,[],[f2])).
% 3.07/0.79  fof(f2,axiom,(
% 3.07/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.07/0.79  fof(f744,plain,(
% 3.07/0.79    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 3.07/0.79    inference(resolution,[],[f742,f79])).
% 3.07/0.79  fof(f79,plain,(
% 3.07/0.79    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f10])).
% 3.07/0.79  fof(f10,axiom,(
% 3.07/0.79    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 3.07/0.79  fof(f742,plain,(
% 3.07/0.79    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 3.07/0.79    inference(duplicate_literal_removal,[],[f738])).
% 3.07/0.79  fof(f738,plain,(
% 3.07/0.79    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 3.07/0.79    inference(resolution,[],[f163,f91])).
% 3.07/0.79  fof(f91,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f52])).
% 3.07/0.79  fof(f163,plain,(
% 3.07/0.79    ( ! [X4,X2,X3] : (~r2_hidden(sK4(X3,X4),X2) | ~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X4)) )),
% 3.07/0.79    inference(resolution,[],[f92,f90])).
% 3.07/0.79  fof(f90,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f52])).
% 3.07/0.79  fof(f786,plain,(
% 3.07/0.79    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.07/0.79    inference(superposition,[],[f221,f765])).
% 3.07/0.79  fof(f765,plain,(
% 3.07/0.79    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.07/0.79    inference(resolution,[],[f749,f242])).
% 3.07/0.79  fof(f242,plain,(
% 3.07/0.79    ( ! [X3] : (r2_hidden(sK9(X3),X3) | k1_xboole_0 = k1_relat_1(X3)) )),
% 3.07/0.79    inference(resolution,[],[f238,f85])).
% 3.07/0.79  fof(f85,plain,(
% 3.07/0.79    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.07/0.79    inference(cnf_transformation,[],[f50])).
% 3.07/0.79  fof(f50,plain,(
% 3.07/0.79    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f49])).
% 3.07/0.79  fof(f49,plain,(
% 3.07/0.79    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f33,plain,(
% 3.07/0.79    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.07/0.79    inference(ennf_transformation,[],[f3])).
% 3.07/0.79  fof(f3,axiom,(
% 3.07/0.79    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.07/0.79  fof(f238,plain,(
% 3.07/0.79    ( ! [X6,X5] : (~r2_hidden(X5,k1_relat_1(X6)) | r2_hidden(sK9(X6),X6)) )),
% 3.07/0.79    inference(resolution,[],[f135,f103])).
% 3.07/0.79  fof(f103,plain,(
% 3.07/0.79    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK9(X1),X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f65])).
% 3.07/0.79  fof(f65,plain,(
% 3.07/0.79    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK9(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK9(X1),X1)) | ~r2_hidden(X0,X1))),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f64])).
% 3.07/0.79  fof(f64,plain,(
% 3.07/0.79    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK9(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK9(X1),X1)))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f37,plain,(
% 3.07/0.79    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.07/0.79    inference(ennf_transformation,[],[f16])).
% 3.07/0.79  fof(f16,axiom,(
% 3.07/0.79    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 3.07/0.79  fof(f135,plain,(
% 3.07/0.79    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.07/0.79    inference(equality_resolution,[],[f97])).
% 3.07/0.79  fof(f97,plain,(
% 3.07/0.79    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.07/0.79    inference(cnf_transformation,[],[f62])).
% 3.07/0.79  fof(f62,plain,(
% 3.07/0.79    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f58,f61,f60,f59])).
% 3.07/0.79  fof(f59,plain,(
% 3.07/0.79    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f60,plain,(
% 3.07/0.79    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f61,plain,(
% 3.07/0.79    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f58,plain,(
% 3.07/0.79    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.07/0.79    inference(rectify,[],[f57])).
% 3.07/0.79  fof(f57,plain,(
% 3.07/0.79    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.07/0.79    inference(nnf_transformation,[],[f19])).
% 3.07/0.79  fof(f19,axiom,(
% 3.07/0.79    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 3.07/0.79  fof(f221,plain,(
% 3.07/0.79    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 3.07/0.79    inference(resolution,[],[f93,f85])).
% 3.07/0.79  fof(f93,plain,(
% 3.07/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK5(X1),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f54])).
% 3.07/0.79  fof(f54,plain,(
% 3.07/0.79    ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f53])).
% 3.07/0.79  fof(f53,plain,(
% 3.07/0.79    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK5(X1),k1_relat_1(X1)))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f36,plain,(
% 3.07/0.79    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.07/0.79    inference(flattening,[],[f35])).
% 3.07/0.79  fof(f35,plain,(
% 3.07/0.79    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.07/0.79    inference(ennf_transformation,[],[f22])).
% 3.07/0.79  fof(f22,axiom,(
% 3.07/0.79    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 3.07/0.79  fof(f403,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k2_relat_1(k1_xboole_0))),
% 3.07/0.79    inference(subsumption_resolution,[],[f402,f74])).
% 3.07/0.79  fof(f74,plain,(
% 3.07/0.79    v1_relat_1(sK1)),
% 3.07/0.79    inference(cnf_transformation,[],[f48])).
% 3.07/0.79  fof(f402,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1)),
% 3.07/0.79    inference(subsumption_resolution,[],[f375,f75])).
% 3.07/0.79  fof(f375,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k2_relat_1(sK1),k2_relat_1(sK2)),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1)),
% 3.07/0.79    inference(superposition,[],[f83,f152])).
% 3.07/0.79  fof(f152,plain,(
% 3.07/0.79    k1_xboole_0 = k6_subset_1(sK1,sK2)),
% 3.07/0.79    inference(resolution,[],[f122,f76])).
% 3.07/0.79  fof(f76,plain,(
% 3.07/0.79    r1_tarski(sK1,sK2)),
% 3.07/0.79    inference(cnf_transformation,[],[f48])).
% 3.07/0.79  fof(f122,plain,(
% 3.07/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 3.07/0.79    inference(definition_unfolding,[],[f102,f87])).
% 3.07/0.79  fof(f102,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f63])).
% 3.07/0.79  fof(f83,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f31])).
% 3.07/0.79  fof(f31,plain,(
% 3.07/0.79    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.07/0.79    inference(ennf_transformation,[],[f23])).
% 3.07/0.79  fof(f23,axiom,(
% 3.07/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 3.07/0.79  fof(f317,plain,(
% 3.07/0.79    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | r1_tarski(k3_relat_1(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 3.07/0.79    inference(superposition,[],[f126,f290])).
% 3.07/0.79  fof(f290,plain,(
% 3.07/0.79    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 3.07/0.79    inference(resolution,[],[f120,f74])).
% 3.07/0.79  fof(f126,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(definition_unfolding,[],[f107,f119])).
% 3.07/0.79  fof(f107,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f41])).
% 3.07/0.79  fof(f41,plain,(
% 3.07/0.79    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.07/0.79    inference(flattening,[],[f40])).
% 3.07/0.79  fof(f40,plain,(
% 3.07/0.79    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.07/0.79    inference(ennf_transformation,[],[f12])).
% 3.07/0.79  fof(f12,axiom,(
% 3.07/0.79    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.07/0.79  fof(f3991,plain,(
% 3.07/0.79    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2))),
% 3.07/0.79    inference(resolution,[],[f3964,f844])).
% 3.07/0.79  fof(f844,plain,(
% 3.07/0.79    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))),
% 3.07/0.79    inference(resolution,[],[f785,f176])).
% 3.07/0.79  fof(f785,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_xboole_0)),
% 3.07/0.79    inference(backward_demodulation,[],[f429,f765])).
% 3.07/0.79  fof(f429,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0))),
% 3.07/0.79    inference(subsumption_resolution,[],[f428,f74])).
% 3.07/0.79  fof(f428,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1)),
% 3.07/0.79    inference(subsumption_resolution,[],[f423,f75])).
% 3.07/0.79  fof(f423,plain,(
% 3.07/0.79    r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(sK2)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1)),
% 3.07/0.79    inference(superposition,[],[f84,f152])).
% 3.07/0.79  fof(f84,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f32])).
% 3.07/0.79  fof(f32,plain,(
% 3.07/0.79    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.07/0.79    inference(ennf_transformation,[],[f21])).
% 3.07/0.79  fof(f21,axiom,(
% 3.07/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 3.07/0.79  fof(f3964,plain,(
% 3.07/0.79    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k3_relat_1(sK2))) )),
% 3.07/0.79    inference(superposition,[],[f124,f695])).
% 3.07/0.79  fof(f695,plain,(
% 3.07/0.79    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),k1_relat_1(sK2)))),
% 3.07/0.79    inference(resolution,[],[f573,f506])).
% 3.07/0.79  fof(f506,plain,(
% 3.07/0.79    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2))),
% 3.07/0.79    inference(superposition,[],[f121,f291])).
% 3.07/0.79  fof(f121,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.07/0.79    inference(definition_unfolding,[],[f86,f119])).
% 3.07/0.79  fof(f86,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.07/0.79    inference(cnf_transformation,[],[f11])).
% 3.07/0.79  fof(f11,axiom,(
% 3.07/0.79    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.07/0.79  fof(f573,plain,(
% 3.07/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0) )),
% 3.07/0.79    inference(subsumption_resolution,[],[f572,f132])).
% 3.07/0.79  fof(f132,plain,(
% 3.07/0.79    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.07/0.79    inference(equality_resolution,[],[f95])).
% 3.07/0.79  fof(f95,plain,(
% 3.07/0.79    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.07/0.79    inference(cnf_transformation,[],[f56])).
% 3.07/0.79  fof(f572,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 3.07/0.79    inference(duplicate_literal_removal,[],[f569])).
% 3.07/0.79  fof(f569,plain,(
% 3.07/0.79    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 3.07/0.79    inference(resolution,[],[f129,f127])).
% 3.07/0.79  fof(f127,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK10(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(definition_unfolding,[],[f110,f119])).
% 3.07/0.79  fof(f110,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK10(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f67])).
% 3.07/0.79  fof(f67,plain,(
% 3.07/0.79    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK10(X0,X1,X2)) & r1_tarski(X2,sK10(X0,X1,X2)) & r1_tarski(X0,sK10(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.07/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f66])).
% 3.07/0.79  fof(f66,plain,(
% 3.07/0.79    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK10(X0,X1,X2)) & r1_tarski(X2,sK10(X0,X1,X2)) & r1_tarski(X0,sK10(X0,X1,X2))))),
% 3.07/0.79    introduced(choice_axiom,[])).
% 3.07/0.79  fof(f43,plain,(
% 3.07/0.79    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.07/0.79    inference(flattening,[],[f42])).
% 3.07/0.79  fof(f42,plain,(
% 3.07/0.79    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.07/0.79    inference(ennf_transformation,[],[f7])).
% 3.07/0.79  fof(f7,axiom,(
% 3.07/0.79    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 3.07/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 3.07/0.79  fof(f129,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (r1_tarski(X0,sK10(X0,X1,X2)) | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(definition_unfolding,[],[f108,f119])).
% 3.07/0.79  fof(f108,plain,(
% 3.07/0.79    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK10(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.07/0.79    inference(cnf_transformation,[],[f67])).
% 3.07/0.79  % SZS output end Proof for theBenchmark
% 3.07/0.79  % (14052)------------------------------
% 3.07/0.79  % (14052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.79  % (14052)Termination reason: Refutation
% 3.07/0.79  
% 3.07/0.79  % (14052)Memory used [KB]: 13944
% 3.07/0.79  % (14052)Time elapsed: 0.347 s
% 3.07/0.79  % (14052)------------------------------
% 3.07/0.79  % (14052)------------------------------
% 3.07/0.79  % (14045)Success in time 0.434 s
%------------------------------------------------------------------------------
