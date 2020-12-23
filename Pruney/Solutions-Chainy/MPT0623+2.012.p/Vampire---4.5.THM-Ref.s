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
% DateTime   : Thu Dec  3 12:52:04 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 311 expanded)
%              Number of leaves         :   22 (  91 expanded)
%              Depth                    :   25
%              Number of atoms          :  407 (1280 expanded)
%              Number of equality atoms :  132 ( 520 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(subsumption_resolution,[],[f598,f220])).

fof(f220,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f69,f215])).

fof(f215,plain,(
    k1_xboole_0 = sK7(k1_xboole_0) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK7(X0) ) ),
    inference(subsumption_resolution,[],[f133,f69])).

fof(f133,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK7(X0)
      | ~ v1_relat_1(sK7(X0)) ) ),
    inference(superposition,[],[f62,f71])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK7(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK7(X0)) = X0
      & v1_funct_1(sK7(X0))
      & v1_relat_1(sK7(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK7(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK7(X0)) = X0
        & v1_funct_1(sK7(X0))
        & v1_relat_1(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f69,plain,(
    ! [X0] : v1_relat_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f598,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f597,f219])).

fof(f219,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f70,f215])).

fof(f70,plain,(
    ! [X0] : v1_funct_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f597,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f591])).

fof(f591,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f183,f590])).

fof(f590,plain,(
    k1_xboole_0 = sK5 ),
    inference(trivial_inequality_removal,[],[f577])).

fof(f577,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(backward_demodulation,[],[f56,f565])).

fof(f565,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f537,f162])).

fof(f162,plain,(
    ! [X6,X7] :
      ( ~ sP3(k1_xboole_0,X6,X7)
      | k1_xboole_0 = X7 ) ),
    inference(superposition,[],[f98,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[],[f97,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f61,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f96,f75])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f28,f27])).

fof(f27,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f537,plain,(
    ! [X16] : sP3(X16,sK4,sK4) ),
    inference(resolution,[],[f319,f492])).

fof(f492,plain,(
    ! [X2] : ~ r2_hidden(X2,sK4) ),
    inference(resolution,[],[f489,f388])).

fof(f388,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK4) ),
    inference(subsumption_resolution,[],[f386,f292])).

fof(f292,plain,(
    sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( sP0(sK5)
    | sP0(sK5) ),
    inference(superposition,[],[f261,f216])).

fof(f216,plain,(
    ! [X0] :
      ( sK7(X0) = X0
      | sP0(X0) ) ),
    inference(superposition,[],[f215,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f20,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f261,plain,(
    sP0(sK7(sK5)) ),
    inference(subsumption_resolution,[],[f260,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | sP0(X0) ) ),
    inference(superposition,[],[f60,f68])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f260,plain,
    ( ~ r1_tarski(sK7(sK5),sK4)
    | sP0(sK7(sK5)) ),
    inference(superposition,[],[f234,f106])).

fof(f106,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = X0
      | sP0(X0) ) ),
    inference(superposition,[],[f59,f68])).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f234,plain,(
    ~ r1_tarski(k2_relat_1(sK7(sK5)),sK4) ),
    inference(equality_resolution,[],[f187])).

fof(f187,plain,(
    ! [X3] :
      ( sK5 != X3
      | ~ r1_tarski(k2_relat_1(sK7(X3)),sK4) ) ),
    inference(subsumption_resolution,[],[f186,f69])).

fof(f186,plain,(
    ! [X3] :
      ( sK5 != X3
      | ~ r1_tarski(k2_relat_1(sK7(X3)),sK4)
      | ~ v1_relat_1(sK7(X3)) ) ),
    inference(subsumption_resolution,[],[f181,f70])).

fof(f181,plain,(
    ! [X3] :
      ( sK5 != X3
      | ~ r1_tarski(k2_relat_1(sK7(X3)),sK4)
      | ~ v1_funct_1(sK7(X3))
      | ~ v1_relat_1(sK7(X3)) ) ),
    inference(superposition,[],[f57,f71])).

fof(f57,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK5
      | ~ r1_tarski(k2_relat_1(X2),sK4)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK4)
        | k1_relat_1(X2) != sK5
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK5
      | k1_xboole_0 != sK4 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK4)
          | k1_relat_1(X2) != sK5
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK5
        | k1_xboole_0 != sK4 ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f386,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK4)
      | ~ sP0(sK5) ) ),
    inference(superposition,[],[f384,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
          & k1_relat_1(sK6(X0,X1)) = X0
          & v1_funct_1(sK6(X0,X1))
          & v1_relat_1(sK6(X0,X1)) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f384,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4) ),
    inference(subsumption_resolution,[],[f284,f292])).

fof(f284,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4)
      | ~ sP0(sK5) ) ),
    inference(equality_resolution,[],[f185])).

fof(f185,plain,(
    ! [X2,X1] :
      ( sK5 != X1
      | ~ r1_tarski(k2_relat_1(sK6(X1,X2)),sK4)
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f184,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK6(X0,X1))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f184,plain,(
    ! [X2,X1] :
      ( sK5 != X1
      | ~ r1_tarski(k2_relat_1(sK6(X1,X2)),sK4)
      | ~ v1_relat_1(sK6(X1,X2))
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f180,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK6(X0,X1))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f180,plain,(
    ! [X2,X1] :
      ( sK5 != X1
      | ~ r1_tarski(k2_relat_1(sK6(X1,X2)),sK4)
      | ~ v1_funct_1(sK6(X1,X2))
      | ~ v1_relat_1(sK6(X1,X2))
      | ~ sP0(X1) ) ),
    inference(superposition,[],[f57,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK6(X0,X1)) = X0
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f489,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_tarski(X3),X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | r1_tarski(k1_tarski(X3),X4)
      | r1_tarski(k1_tarski(X3),X4) ) ),
    inference(superposition,[],[f78,f222])).

fof(f222,plain,(
    ! [X2,X1] :
      ( sK8(k1_tarski(X1),X2) = X1
      | r1_tarski(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f155,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f79,f101])).

fof(f101,plain,(
    ! [X0] : sP1(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP1(X0,X1) )
      & ( sP1(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f6,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f319,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1,X1),X1)
      | sP3(X0,X1,X1) ) ),
    inference(factoring,[],[f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X2)
      | sP3(X0,X1,X2)
      | r2_hidden(sK10(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f90,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,sK10(X0,X1,X2),X0)
      | sP3(X0,X1,X2)
      | r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK10(X0,X1,X2),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP2(X1,sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK10(X0,X1,X2),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP2(X1,sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f56,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f31])).

fof(f183,plain,
    ( k1_xboole_0 != sK5
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f182,f60])).

fof(f182,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | k1_xboole_0 != sK5
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f179,f59])).

fof(f179,plain,
    ( k1_xboole_0 != sK5
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK4)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f57,f58])).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (32072)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (32072)Refutation not found, incomplete strategy% (32072)------------------------------
% 0.22/0.53  % (32072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32089)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (32072)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32072)Memory used [KB]: 10618
% 0.22/0.53  % (32072)Time elapsed: 0.072 s
% 0.22/0.53  % (32072)------------------------------
% 0.22/0.53  % (32072)------------------------------
% 1.47/0.55  % (32063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.56  % (32070)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.56  % (32070)Refutation not found, incomplete strategy% (32070)------------------------------
% 1.47/0.56  % (32070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (32070)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (32070)Memory used [KB]: 10746
% 1.47/0.56  % (32070)Time elapsed: 0.147 s
% 1.47/0.56  % (32070)------------------------------
% 1.47/0.56  % (32070)------------------------------
% 1.47/0.57  % (32066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.57  % (32064)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.57  % (32081)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.57  % (32064)Refutation not found, incomplete strategy% (32064)------------------------------
% 1.59/0.57  % (32064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (32064)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (32064)Memory used [KB]: 10746
% 1.59/0.57  % (32064)Time elapsed: 0.153 s
% 1.59/0.57  % (32064)------------------------------
% 1.59/0.57  % (32064)------------------------------
% 1.59/0.57  % (32088)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.57  % (32074)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.57  % (32085)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.57  % (32078)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.58  % (32075)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.59/0.58  % (32077)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.59/0.58  % (32067)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.58  % (32062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.59/0.58  % (32062)Refutation not found, incomplete strategy% (32062)------------------------------
% 1.59/0.58  % (32062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (32062)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (32062)Memory used [KB]: 1663
% 1.59/0.58  % (32062)Time elapsed: 0.138 s
% 1.59/0.58  % (32062)------------------------------
% 1.59/0.58  % (32062)------------------------------
% 1.59/0.58  % (32071)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.58  % (32076)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.59/0.58  % (32086)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.58  % (32091)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.58  % (32084)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.58  % (32071)Refutation not found, incomplete strategy% (32071)------------------------------
% 1.59/0.58  % (32071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (32083)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.59/0.58  % (32087)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.58  % (32071)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (32071)Memory used [KB]: 10618
% 1.59/0.58  % (32071)Time elapsed: 0.141 s
% 1.59/0.58  % (32071)------------------------------
% 1.59/0.58  % (32071)------------------------------
% 1.59/0.59  % (32069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.59/0.59  % (32093)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.60  % (32068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.59/0.60  % (32090)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.60  % (32092)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.60  % (32086)Refutation not found, incomplete strategy% (32086)------------------------------
% 1.59/0.60  % (32086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (32080)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.60  % (32086)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (32086)Memory used [KB]: 10746
% 1.59/0.60  % (32086)Time elapsed: 0.172 s
% 1.59/0.60  % (32086)------------------------------
% 1.59/0.60  % (32086)------------------------------
% 1.59/0.61  % (32080)Refutation not found, incomplete strategy% (32080)------------------------------
% 1.59/0.61  % (32080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (32080)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.61  
% 1.59/0.61  % (32080)Memory used [KB]: 10618
% 1.59/0.61  % (32080)Time elapsed: 0.135 s
% 1.59/0.61  % (32080)------------------------------
% 1.59/0.61  % (32080)------------------------------
% 1.59/0.61  % (32073)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.61  % (32065)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.59/0.62  % (32093)Refutation found. Thanks to Tanya!
% 1.59/0.62  % SZS status Theorem for theBenchmark
% 1.59/0.62  % SZS output start Proof for theBenchmark
% 1.59/0.62  fof(f599,plain,(
% 1.59/0.62    $false),
% 1.59/0.62    inference(subsumption_resolution,[],[f598,f220])).
% 1.59/0.62  fof(f220,plain,(
% 1.59/0.62    v1_relat_1(k1_xboole_0)),
% 1.59/0.62    inference(superposition,[],[f69,f215])).
% 1.59/0.62  fof(f215,plain,(
% 1.59/0.62    k1_xboole_0 = sK7(k1_xboole_0)),
% 1.59/0.62    inference(equality_resolution,[],[f135])).
% 1.59/0.62  fof(f135,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK7(X0)) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f133,f69])).
% 1.59/0.62  fof(f133,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK7(X0) | ~v1_relat_1(sK7(X0))) )),
% 1.59/0.62    inference(superposition,[],[f62,f71])).
% 1.59/0.62  fof(f71,plain,(
% 1.59/0.62    ( ! [X0] : (k1_relat_1(sK7(X0)) = X0) )),
% 1.59/0.62    inference(cnf_transformation,[],[f36])).
% 1.59/0.62  fof(f36,plain,(
% 1.59/0.62    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0)))),
% 1.59/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f35])).
% 1.59/0.62  fof(f35,plain,(
% 1.59/0.62    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0))))),
% 1.59/0.62    introduced(choice_axiom,[])).
% 1.59/0.62  fof(f21,plain,(
% 1.59/0.62    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.59/0.62    inference(ennf_transformation,[],[f12])).
% 1.59/0.62  fof(f12,axiom,(
% 1.59/0.62    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.59/0.62  fof(f62,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f19])).
% 1.59/0.62  fof(f19,plain,(
% 1.59/0.62    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.59/0.62    inference(flattening,[],[f18])).
% 1.59/0.62  fof(f18,plain,(
% 1.59/0.62    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.59/0.62    inference(ennf_transformation,[],[f11])).
% 1.59/0.62  fof(f11,axiom,(
% 1.59/0.62    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.59/0.62  fof(f69,plain,(
% 1.59/0.62    ( ! [X0] : (v1_relat_1(sK7(X0))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f36])).
% 1.59/0.62  fof(f598,plain,(
% 1.59/0.62    ~v1_relat_1(k1_xboole_0)),
% 1.59/0.62    inference(subsumption_resolution,[],[f597,f219])).
% 1.59/0.62  fof(f219,plain,(
% 1.59/0.62    v1_funct_1(k1_xboole_0)),
% 1.59/0.62    inference(superposition,[],[f70,f215])).
% 1.59/0.62  fof(f70,plain,(
% 1.59/0.62    ( ! [X0] : (v1_funct_1(sK7(X0))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f36])).
% 1.59/0.62  fof(f597,plain,(
% 1.59/0.62    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.59/0.62    inference(trivial_inequality_removal,[],[f591])).
% 1.59/0.62  fof(f591,plain,(
% 1.59/0.62    k1_xboole_0 != k1_xboole_0 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.59/0.62    inference(backward_demodulation,[],[f183,f590])).
% 1.59/0.62  fof(f590,plain,(
% 1.59/0.62    k1_xboole_0 = sK5),
% 1.59/0.62    inference(trivial_inequality_removal,[],[f577])).
% 1.59/0.62  fof(f577,plain,(
% 1.59/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK5),
% 1.59/0.62    inference(backward_demodulation,[],[f56,f565])).
% 1.59/0.62  fof(f565,plain,(
% 1.59/0.62    k1_xboole_0 = sK4),
% 1.59/0.62    inference(resolution,[],[f537,f162])).
% 1.59/0.62  fof(f162,plain,(
% 1.59/0.62    ( ! [X6,X7] : (~sP3(k1_xboole_0,X6,X7) | k1_xboole_0 = X7) )),
% 1.59/0.62    inference(superposition,[],[f98,f116])).
% 1.59/0.62  fof(f116,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 1.59/0.62    inference(superposition,[],[f97,f74])).
% 1.59/0.62  fof(f74,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f5])).
% 1.59/0.62  fof(f5,axiom,(
% 1.59/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.59/0.62  fof(f97,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.59/0.62    inference(definition_unfolding,[],[f61,f75])).
% 1.59/0.62  fof(f75,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f9])).
% 1.59/0.62  fof(f9,axiom,(
% 1.59/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.59/0.62  fof(f61,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f3])).
% 1.59/0.62  fof(f3,axiom,(
% 1.59/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.59/0.62  fof(f98,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~sP3(X0,X1,X2)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f96,f75])).
% 1.59/0.62  fof(f96,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f55])).
% 1.59/0.62  fof(f55,plain,(
% 1.59/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.62    inference(nnf_transformation,[],[f29])).
% 1.59/0.62  fof(f29,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 1.59/0.62    inference(definition_folding,[],[f2,f28,f27])).
% 1.59/0.62  fof(f27,plain,(
% 1.59/0.62    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.59/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.59/0.62  fof(f28,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 1.59/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.59/0.62  fof(f2,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.59/0.62  fof(f537,plain,(
% 1.59/0.62    ( ! [X16] : (sP3(X16,sK4,sK4)) )),
% 1.59/0.62    inference(resolution,[],[f319,f492])).
% 1.59/0.62  fof(f492,plain,(
% 1.59/0.62    ( ! [X2] : (~r2_hidden(X2,sK4)) )),
% 1.59/0.62    inference(resolution,[],[f489,f388])).
% 1.59/0.62  fof(f388,plain,(
% 1.59/0.62    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK4)) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f386,f292])).
% 1.59/0.62  fof(f292,plain,(
% 1.59/0.62    sP0(sK5)),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f290])).
% 1.59/0.62  fof(f290,plain,(
% 1.59/0.62    sP0(sK5) | sP0(sK5)),
% 1.59/0.62    inference(superposition,[],[f261,f216])).
% 1.59/0.62  fof(f216,plain,(
% 1.59/0.62    ( ! [X0] : (sK7(X0) = X0 | sP0(X0)) )),
% 1.59/0.62    inference(superposition,[],[f215,f68])).
% 1.59/0.62  fof(f68,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 = X0 | sP0(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f24])).
% 1.59/0.62  fof(f24,plain,(
% 1.59/0.62    ! [X0] : (sP0(X0) | k1_xboole_0 = X0)),
% 1.59/0.62    inference(definition_folding,[],[f20,f23])).
% 1.59/0.62  fof(f23,plain,(
% 1.59/0.62    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | ~sP0(X0))),
% 1.59/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.59/0.62  fof(f20,plain,(
% 1.59/0.62    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.59/0.62    inference(ennf_transformation,[],[f13])).
% 1.59/0.62  fof(f13,axiom,(
% 1.59/0.62    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.59/0.62  fof(f261,plain,(
% 1.59/0.62    sP0(sK7(sK5))),
% 1.59/0.62    inference(subsumption_resolution,[],[f260,f108])).
% 1.59/0.62  fof(f108,plain,(
% 1.59/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | sP0(X0)) )),
% 1.59/0.62    inference(superposition,[],[f60,f68])).
% 1.59/0.62  fof(f60,plain,(
% 1.59/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f4])).
% 1.59/0.62  fof(f4,axiom,(
% 1.59/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.62  fof(f260,plain,(
% 1.59/0.62    ~r1_tarski(sK7(sK5),sK4) | sP0(sK7(sK5))),
% 1.59/0.62    inference(superposition,[],[f234,f106])).
% 1.59/0.62  fof(f106,plain,(
% 1.59/0.62    ( ! [X0] : (k2_relat_1(X0) = X0 | sP0(X0)) )),
% 1.59/0.62    inference(superposition,[],[f59,f68])).
% 1.59/0.62  fof(f59,plain,(
% 1.59/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.59/0.62    inference(cnf_transformation,[],[f10])).
% 1.59/0.62  fof(f10,axiom,(
% 1.59/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.59/0.62  fof(f234,plain,(
% 1.59/0.62    ~r1_tarski(k2_relat_1(sK7(sK5)),sK4)),
% 1.59/0.62    inference(equality_resolution,[],[f187])).
% 1.59/0.62  fof(f187,plain,(
% 1.59/0.62    ( ! [X3] : (sK5 != X3 | ~r1_tarski(k2_relat_1(sK7(X3)),sK4)) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f186,f69])).
% 1.59/0.62  fof(f186,plain,(
% 1.59/0.62    ( ! [X3] : (sK5 != X3 | ~r1_tarski(k2_relat_1(sK7(X3)),sK4) | ~v1_relat_1(sK7(X3))) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f181,f70])).
% 1.59/0.62  fof(f181,plain,(
% 1.59/0.62    ( ! [X3] : (sK5 != X3 | ~r1_tarski(k2_relat_1(sK7(X3)),sK4) | ~v1_funct_1(sK7(X3)) | ~v1_relat_1(sK7(X3))) )),
% 1.59/0.62    inference(superposition,[],[f57,f71])).
% 1.59/0.62  fof(f57,plain,(
% 1.59/0.62    ( ! [X2] : (k1_relat_1(X2) != sK5 | ~r1_tarski(k2_relat_1(X2),sK4) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f31])).
% 1.59/0.62  fof(f31,plain,(
% 1.59/0.62    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK4) | k1_relat_1(X2) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK5 | k1_xboole_0 != sK4)),
% 1.59/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f30])).
% 1.59/0.62  fof(f30,plain,(
% 1.59/0.62    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK4) | k1_relat_1(X2) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK5 | k1_xboole_0 != sK4))),
% 1.59/0.62    introduced(choice_axiom,[])).
% 1.59/0.62  fof(f17,plain,(
% 1.59/0.62    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.59/0.62    inference(flattening,[],[f16])).
% 1.59/0.62  fof(f16,plain,(
% 1.59/0.62    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.59/0.62    inference(ennf_transformation,[],[f15])).
% 1.59/0.62  fof(f15,negated_conjecture,(
% 1.59/0.62    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.59/0.62    inference(negated_conjecture,[],[f14])).
% 1.59/0.62  fof(f14,conjecture,(
% 1.59/0.62    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.59/0.62  fof(f386,plain,(
% 1.59/0.62    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK4) | ~sP0(sK5)) )),
% 1.59/0.62    inference(superposition,[],[f384,f67])).
% 1.59/0.62  fof(f67,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) | ~sP0(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f34])).
% 1.59/0.62  fof(f34,plain,(
% 1.59/0.62    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))) | ~sP0(X0))),
% 1.59/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 1.59/0.62  fof(f33,plain,(
% 1.59/0.62    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 1.59/0.62    introduced(choice_axiom,[])).
% 1.59/0.62  fof(f32,plain,(
% 1.59/0.62    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | ~sP0(X0))),
% 1.59/0.62    inference(nnf_transformation,[],[f23])).
% 1.59/0.62  fof(f384,plain,(
% 1.59/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4)) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f284,f292])).
% 1.59/0.62  fof(f284,plain,(
% 1.59/0.62    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4) | ~sP0(sK5)) )),
% 1.59/0.62    inference(equality_resolution,[],[f185])).
% 1.59/0.62  fof(f185,plain,(
% 1.59/0.62    ( ! [X2,X1] : (sK5 != X1 | ~r1_tarski(k2_relat_1(sK6(X1,X2)),sK4) | ~sP0(X1)) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f184,f64])).
% 1.59/0.62  fof(f64,plain,(
% 1.59/0.62    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1)) | ~sP0(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f34])).
% 1.59/0.62  fof(f184,plain,(
% 1.59/0.62    ( ! [X2,X1] : (sK5 != X1 | ~r1_tarski(k2_relat_1(sK6(X1,X2)),sK4) | ~v1_relat_1(sK6(X1,X2)) | ~sP0(X1)) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f180,f65])).
% 1.59/0.62  fof(f65,plain,(
% 1.59/0.62    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1)) | ~sP0(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f34])).
% 1.59/0.62  fof(f180,plain,(
% 1.59/0.62    ( ! [X2,X1] : (sK5 != X1 | ~r1_tarski(k2_relat_1(sK6(X1,X2)),sK4) | ~v1_funct_1(sK6(X1,X2)) | ~v1_relat_1(sK6(X1,X2)) | ~sP0(X1)) )),
% 1.59/0.62    inference(superposition,[],[f57,f66])).
% 1.59/0.62  fof(f66,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0 | ~sP0(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f34])).
% 1.59/0.62  fof(f489,plain,(
% 1.59/0.62    ( ! [X4,X3] : (r1_tarski(k1_tarski(X3),X4) | ~r2_hidden(X3,X4)) )),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f486])).
% 1.59/0.62  fof(f486,plain,(
% 1.59/0.62    ( ! [X4,X3] : (~r2_hidden(X3,X4) | r1_tarski(k1_tarski(X3),X4) | r1_tarski(k1_tarski(X3),X4)) )),
% 1.59/0.62    inference(superposition,[],[f78,f222])).
% 1.59/0.62  fof(f222,plain,(
% 1.59/0.62    ( ! [X2,X1] : (sK8(k1_tarski(X1),X2) = X1 | r1_tarski(k1_tarski(X1),X2)) )),
% 1.59/0.62    inference(resolution,[],[f155,f77])).
% 1.59/0.62  fof(f77,plain,(
% 1.59/0.62    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f40])).
% 1.59/0.62  fof(f40,plain,(
% 1.59/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).
% 1.99/0.64  fof(f39,plain,(
% 1.99/0.64    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 1.99/0.64    introduced(choice_axiom,[])).
% 1.99/0.64  fof(f38,plain,(
% 1.99/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.64    inference(rectify,[],[f37])).
% 1.99/0.64  fof(f37,plain,(
% 1.99/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.64    inference(nnf_transformation,[],[f22])).
% 1.99/0.64  fof(f22,plain,(
% 1.99/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.99/0.64    inference(ennf_transformation,[],[f1])).
% 1.99/0.64  fof(f1,axiom,(
% 1.99/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.99/0.64  fof(f155,plain,(
% 1.99/0.64    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 1.99/0.64    inference(resolution,[],[f79,f101])).
% 1.99/0.64  fof(f101,plain,(
% 1.99/0.64    ( ! [X0] : (sP1(X0,k1_tarski(X0))) )),
% 1.99/0.64    inference(equality_resolution,[],[f83])).
% 1.99/0.64  fof(f83,plain,(
% 1.99/0.64    ( ! [X0,X1] : (sP1(X0,X1) | k1_tarski(X0) != X1) )),
% 1.99/0.64    inference(cnf_transformation,[],[f45])).
% 1.99/0.64  fof(f45,plain,(
% 1.99/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k1_tarski(X0) != X1))),
% 1.99/0.64    inference(nnf_transformation,[],[f26])).
% 1.99/0.64  fof(f26,plain,(
% 1.99/0.64    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP1(X0,X1))),
% 1.99/0.64    inference(definition_folding,[],[f6,f25])).
% 1.99/0.64  fof(f25,plain,(
% 1.99/0.64    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.99/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.99/0.64  fof(f6,axiom,(
% 1.99/0.64    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.99/0.64  fof(f79,plain,(
% 1.99/0.64    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 1.99/0.64    inference(cnf_transformation,[],[f44])).
% 1.99/0.64  fof(f44,plain,(
% 1.99/0.64    ! [X0,X1] : ((sP1(X0,X1) | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.99/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).
% 1.99/0.64  fof(f43,plain,(
% 1.99/0.64    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 1.99/0.64    introduced(choice_axiom,[])).
% 1.99/0.64  fof(f42,plain,(
% 1.99/0.64    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 1.99/0.64    inference(rectify,[],[f41])).
% 1.99/0.64  fof(f41,plain,(
% 1.99/0.64    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 1.99/0.64    inference(nnf_transformation,[],[f25])).
% 1.99/0.64  fof(f78,plain,(
% 1.99/0.64    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.99/0.64    inference(cnf_transformation,[],[f40])).
% 1.99/0.64  fof(f319,plain,(
% 1.99/0.64    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1,X1),X1) | sP3(X0,X1,X1)) )),
% 1.99/0.64    inference(factoring,[],[f196])).
% 1.99/0.64  fof(f196,plain,(
% 1.99/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X2) | sP3(X0,X1,X2) | r2_hidden(sK10(X0,X1,X2),X1)) )),
% 1.99/0.64    inference(resolution,[],[f90,f93])).
% 1.99/0.64  fof(f93,plain,(
% 1.99/0.64    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 1.99/0.64    inference(cnf_transformation,[],[f54])).
% 1.99/0.64  fof(f54,plain,(
% 1.99/0.64    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 1.99/0.64    inference(rectify,[],[f53])).
% 1.99/0.64  fof(f53,plain,(
% 1.99/0.64    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 1.99/0.64    inference(flattening,[],[f52])).
% 1.99/0.64  fof(f52,plain,(
% 1.99/0.64    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 1.99/0.64    inference(nnf_transformation,[],[f27])).
% 1.99/0.64  fof(f90,plain,(
% 1.99/0.64    ( ! [X2,X0,X1] : (sP2(X1,sK10(X0,X1,X2),X0) | sP3(X0,X1,X2) | r2_hidden(sK10(X0,X1,X2),X2)) )),
% 1.99/0.64    inference(cnf_transformation,[],[f51])).
% 1.99/0.64  fof(f51,plain,(
% 1.99/0.64    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP2(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 1.99/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).
% 1.99/0.64  fof(f50,plain,(
% 1.99/0.64    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP2(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 1.99/0.64    introduced(choice_axiom,[])).
% 1.99/0.64  fof(f49,plain,(
% 1.99/0.64    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 1.99/0.64    inference(rectify,[],[f48])).
% 1.99/0.64  fof(f48,plain,(
% 1.99/0.64    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 1.99/0.64    inference(nnf_transformation,[],[f28])).
% 1.99/0.64  fof(f56,plain,(
% 1.99/0.64    k1_xboole_0 != sK4 | k1_xboole_0 = sK5),
% 1.99/0.64    inference(cnf_transformation,[],[f31])).
% 1.99/0.64  fof(f183,plain,(
% 1.99/0.64    k1_xboole_0 != sK5 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.99/0.64    inference(subsumption_resolution,[],[f182,f60])).
% 1.99/0.64  fof(f182,plain,(
% 1.99/0.64    ~r1_tarski(k1_xboole_0,sK4) | k1_xboole_0 != sK5 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.99/0.64    inference(forward_demodulation,[],[f179,f59])).
% 1.99/0.64  fof(f179,plain,(
% 1.99/0.64    k1_xboole_0 != sK5 | ~r1_tarski(k2_relat_1(k1_xboole_0),sK4) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.99/0.64    inference(superposition,[],[f57,f58])).
% 1.99/0.64  fof(f58,plain,(
% 1.99/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.99/0.64    inference(cnf_transformation,[],[f10])).
% 1.99/0.64  % SZS output end Proof for theBenchmark
% 1.99/0.64  % (32093)------------------------------
% 1.99/0.64  % (32093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.64  % (32093)Termination reason: Refutation
% 1.99/0.64  
% 1.99/0.64  % (32093)Memory used [KB]: 1918
% 1.99/0.64  % (32093)Time elapsed: 0.192 s
% 1.99/0.64  % (32093)------------------------------
% 1.99/0.64  % (32093)------------------------------
% 1.99/0.64  % (32055)Success in time 0.274 s
%------------------------------------------------------------------------------
