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
% DateTime   : Thu Dec  3 12:52:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 450 expanded)
%              Number of leaves         :   16 ( 131 expanded)
%              Depth                    :   23
%              Number of atoms          :  340 (1931 expanded)
%              Number of equality atoms :  122 ( 799 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(subsumption_resolution,[],[f411,f257])).

fof(f257,plain,(
    ~ sP0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f252,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f252,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ sP0(k1_xboole_0) ),
    inference(superposition,[],[f206,f242])).

fof(f242,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(X0)
      | ~ sP0(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(X0)
      | ~ sP0(k1_xboole_0)
      | ~ sP0(k1_xboole_0) ) ),
    inference(superposition,[],[f63,f208])).

fof(f208,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK6(k1_xboole_0,X0))
      | ~ sP0(k1_xboole_0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_relat_1(sK6(X1,X2))
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f118,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK6(X0,X1))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
          & k1_relat_1(sK6(X0,X1)) = X0
          & v1_funct_1(sK6(X0,X1))
          & v1_relat_1(sK6(X0,X1)) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f30])).

fof(f30,plain,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f118,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_relat_1(sK6(X1,X2))
      | ~ v1_relat_1(sK6(X1,X2))
      | ~ sP0(X1) ) ),
    inference(superposition,[],[f58,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK6(X0,X1)) = X0
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f206,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK4) ),
    inference(subsumption_resolution,[],[f205,f181])).

fof(f181,plain,(
    sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( sP0(sK5)
    | sP0(sK5) ),
    inference(superposition,[],[f159,f168])).

fof(f168,plain,(
    ! [X0] :
      ( k2_relat_1(sK7(X0)) = X0
      | sP0(X0) ) ),
    inference(superposition,[],[f167,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f15,f19])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f167,plain,(
    k1_xboole_0 = k2_relat_1(sK7(k1_xboole_0)) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_relat_1(sK7(X0)) ) ),
    inference(subsumption_resolution,[],[f117,f65])).

fof(f65,plain,(
    ! [X0] : v1_relat_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK7(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK7(X0)) = X0
      & v1_funct_1(sK7(X0))
      & v1_relat_1(sK7(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK7(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK7(X0)) = X0
        & v1_funct_1(sK7(X0))
        & v1_relat_1(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f117,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_relat_1(sK7(X0))
      | ~ v1_relat_1(sK7(X0)) ) ),
    inference(superposition,[],[f58,f67])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f159,plain,(
    sP0(k2_relat_1(sK7(sK5))) ),
    inference(resolution,[],[f158,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | sP0(X0) ) ),
    inference(superposition,[],[f56,f64])).

fof(f158,plain,(
    ~ r1_tarski(k2_relat_1(sK7(sK5)),sK4) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( sK5 != X0
      | ~ r1_tarski(k2_relat_1(sK7(X0)),sK4) ) ),
    inference(subsumption_resolution,[],[f140,f65])).

fof(f140,plain,(
    ! [X0] :
      ( sK5 != X0
      | ~ r1_tarski(k2_relat_1(sK7(X0)),sK4)
      | ~ v1_relat_1(sK7(X0)) ) ),
    inference(subsumption_resolution,[],[f138,f66])).

fof(f66,plain,(
    ! [X0] : v1_funct_1(sK7(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f138,plain,(
    ! [X0] :
      ( sK5 != X0
      | ~ r1_tarski(k2_relat_1(sK7(X0)),sK4)
      | ~ v1_funct_1(sK7(X0))
      | ~ v1_relat_1(sK7(X0)) ) ),
    inference(superposition,[],[f55,f67])).

fof(f55,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK5
      | ~ r1_tarski(k2_relat_1(X2),sK4)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK4)
        | k1_relat_1(X2) != sK5
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK5
      | k1_xboole_0 != sK4 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f26])).

fof(f26,plain,
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

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f205,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK4)
      | ~ sP0(sK5) ) ),
    inference(superposition,[],[f194,f63])).

fof(f194,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4) ),
    inference(subsumption_resolution,[],[f193,f181])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4)
      | ~ sP0(sK5) ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X2,X1] :
      ( sK5 != X1
      | ~ r1_tarski(k2_relat_1(sK6(X1,X2)),sK4)
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f142,f60])).

fof(f142,plain,(
    ! [X2,X1] :
      ( sK5 != X1
      | ~ r1_tarski(k2_relat_1(sK6(X1,X2)),sK4)
      | ~ v1_relat_1(sK6(X1,X2))
      | ~ sP0(X1) ) ),
    inference(subsumption_resolution,[],[f139,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK6(X0,X1))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f139,plain,(
    ! [X2,X1] :
      ( sK5 != X1
      | ~ r1_tarski(k2_relat_1(sK6(X1,X2)),sK4)
      | ~ v1_funct_1(sK6(X1,X2))
      | ~ v1_relat_1(sK6(X1,X2))
      | ~ sP0(X1) ) ),
    inference(superposition,[],[f55,f62])).

fof(f411,plain,(
    sP0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f408,f167])).

fof(f408,plain,(
    sP0(k2_relat_1(sK7(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f159,f406])).

fof(f406,plain,(
    k1_xboole_0 = sK5 ),
    inference(trivial_inequality_removal,[],[f394])).

fof(f394,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(backward_demodulation,[],[f54,f372])).

fof(f372,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f335,f56])).

fof(f335,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK4)
      | sK4 = X3 ) ),
    inference(resolution,[],[f309,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | X0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(factoring,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1),X2)
      | r2_hidden(sK8(X0,X1),X0)
      | X0 = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f69,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK8(X0,X1),X1)
          | ~ r2_hidden(sK8(X0,X1),X0) )
        & ( r2_hidden(sK8(X0,X1),X1)
          | r2_hidden(sK8(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1),X1)
          | ~ r2_hidden(sK8(X0,X1),X0) )
        & ( r2_hidden(sK8(X0,X1),X1)
          | r2_hidden(sK8(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f309,plain,(
    ! [X2] : ~ r2_hidden(X2,sK4) ),
    inference(resolution,[],[f272,f206])).

fof(f272,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_tarski(X3),X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | r1_tarski(k1_tarski(X3),X4)
      | r1_tarski(k1_tarski(X3),X4) ) ),
    inference(superposition,[],[f73,f122])).

fof(f122,plain,(
    ! [X2,X1] :
      ( sK9(k1_tarski(X1),X2) = X1
      | r1_tarski(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f109,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f74,f90])).

fof(f90,plain,(
    ! [X0] : sP1(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f6,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

% (24728)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f21])).

% (24727)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK5 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:09:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (24720)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (24712)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (24712)Refutation not found, incomplete strategy% (24712)------------------------------
% 0.22/0.51  % (24712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24712)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24712)Memory used [KB]: 1663
% 0.22/0.51  % (24712)Time elapsed: 0.094 s
% 0.22/0.51  % (24712)------------------------------
% 0.22/0.51  % (24712)------------------------------
% 0.22/0.52  % (24714)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (24741)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (24735)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (24720)Refutation not found, incomplete strategy% (24720)------------------------------
% 0.22/0.52  % (24720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (24720)Memory used [KB]: 10746
% 0.22/0.52  % (24720)Time elapsed: 0.110 s
% 0.22/0.52  % (24720)------------------------------
% 0.22/0.52  % (24720)------------------------------
% 0.22/0.52  % (24724)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (24718)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (24725)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (24719)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (24741)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f412,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f411,f257])).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    ~sP0(k1_xboole_0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f252,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK4) | ~sP0(k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f206,f242])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k1_tarski(X0) | ~sP0(k1_xboole_0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f239])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k1_tarski(X0) | ~sP0(k1_xboole_0) | ~sP0(k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f63,f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK6(k1_xboole_0,X0)) | ~sP0(k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_relat_1(sK6(X1,X2)) | ~sP0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f118,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1)) | ~sP0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))) | ~sP0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | ~sP0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | ~sP0(X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_relat_1(sK6(X1,X2)) | ~v1_relat_1(sK6(X1,X2)) | ~sP0(X1)) )),
% 0.22/0.53    inference(superposition,[],[f58,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0 | ~sP0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) | ~sP0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f205,f181])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    sP0(sK5)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    sP0(sK5) | sP0(sK5)),
% 0.22/0.53    inference(superposition,[],[f159,f168])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(sK7(X0)) = X0 | sP0(X0)) )),
% 0.22/0.53    inference(superposition,[],[f167,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = X0 | sP0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (sP0(X0) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(definition_folding,[],[f15,f19])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(sK7(k1_xboole_0))),
% 0.22/0.53    inference(equality_resolution,[],[f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_relat_1(sK7(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f117,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(sK7(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK7(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK7(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_relat_1(sK7(X0)) | ~v1_relat_1(sK7(X0))) )),
% 0.22/0.53    inference(superposition,[],[f58,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(sK7(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    sP0(k2_relat_1(sK7(sK5)))),
% 0.22/0.53    inference(resolution,[],[f158,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | sP0(X0)) )),
% 0.22/0.53    inference(superposition,[],[f56,f64])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK7(sK5)),sK4)),
% 0.22/0.53    inference(equality_resolution,[],[f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ( ! [X0] : (sK5 != X0 | ~r1_tarski(k2_relat_1(sK7(X0)),sK4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f65])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ( ! [X0] : (sK5 != X0 | ~r1_tarski(k2_relat_1(sK7(X0)),sK4) | ~v1_relat_1(sK7(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f138,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(sK7(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X0] : (sK5 != X0 | ~r1_tarski(k2_relat_1(sK7(X0)),sK4) | ~v1_funct_1(sK7(X0)) | ~v1_relat_1(sK7(X0))) )),
% 0.22/0.53    inference(superposition,[],[f55,f67])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2] : (k1_relat_1(X2) != sK5 | ~r1_tarski(k2_relat_1(X2),sK4) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK4) | k1_relat_1(X2) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK5 | k1_xboole_0 != sK4)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK4) | k1_relat_1(X2) != sK5 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK5 | k1_xboole_0 != sK4))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK4) | ~sP0(sK5)) )),
% 0.22/0.53    inference(superposition,[],[f194,f63])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f193,f181])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK5,X0)),sK4) | ~sP0(sK5)) )),
% 0.22/0.53    inference(equality_resolution,[],[f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ( ! [X2,X1] : (sK5 != X1 | ~r1_tarski(k2_relat_1(sK6(X1,X2)),sK4) | ~sP0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f142,f60])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X2,X1] : (sK5 != X1 | ~r1_tarski(k2_relat_1(sK6(X1,X2)),sK4) | ~v1_relat_1(sK6(X1,X2)) | ~sP0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f139,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1)) | ~sP0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ( ! [X2,X1] : (sK5 != X1 | ~r1_tarski(k2_relat_1(sK6(X1,X2)),sK4) | ~v1_funct_1(sK6(X1,X2)) | ~v1_relat_1(sK6(X1,X2)) | ~sP0(X1)) )),
% 0.22/0.53    inference(superposition,[],[f55,f62])).
% 0.22/0.53  fof(f411,plain,(
% 0.22/0.53    sP0(k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f408,f167])).
% 0.22/0.53  fof(f408,plain,(
% 0.22/0.53    sP0(k2_relat_1(sK7(k1_xboole_0)))),
% 0.22/0.53    inference(backward_demodulation,[],[f159,f406])).
% 0.22/0.53  fof(f406,plain,(
% 0.22/0.53    k1_xboole_0 = sK5),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f394])).
% 0.22/0.53  fof(f394,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK5),
% 0.22/0.53    inference(backward_demodulation,[],[f54,f372])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    k1_xboole_0 = sK4),
% 0.22/0.53    inference(resolution,[],[f335,f56])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    ( ! [X3] : (~r1_tarski(X3,sK4) | sK4 = X3) )),
% 0.22/0.53    inference(resolution,[],[f309,f217])).
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | X0 = X1 | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(factoring,[],[f147])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1),X2) | r2_hidden(sK8(X0,X1),X0) | X0 = X1 | ~r1_tarski(X1,X2)) )),
% 0.22/0.53    inference(resolution,[],[f69,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | X0 = X1 | r2_hidden(sK8(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK8(X0,X1),X1) | ~r2_hidden(sK8(X0,X1),X0)) & (r2_hidden(sK8(X0,X1),X1) | r2_hidden(sK8(X0,X1),X0))))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK8(X0,X1),X1) | ~r2_hidden(sK8(X0,X1),X0)) & (r2_hidden(sK8(X0,X1),X1) | r2_hidden(sK8(X0,X1),X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.22/0.53    inference(nnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(X2,sK4)) )),
% 0.22/0.53    inference(resolution,[],[f272,f206])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    ( ! [X4,X3] : (r1_tarski(k1_tarski(X3),X4) | ~r2_hidden(X3,X4)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f269])).
% 0.22/0.53  fof(f269,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X3,X4) | r1_tarski(k1_tarski(X3),X4) | r1_tarski(k1_tarski(X3),X4)) )),
% 0.22/0.53    inference(superposition,[],[f73,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ( ! [X2,X1] : (sK9(k1_tarski(X1),X2) = X1 | r1_tarski(k1_tarski(X1),X2)) )),
% 0.22/0.53    inference(resolution,[],[f109,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(resolution,[],[f74,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0] : (sP1(X0,k1_tarski(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP1(X0,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP1(X0,X1))),
% 0.22/0.53    inference(definition_folding,[],[f6,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  % (24728)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP1(X0,X1) | ((sK10(X0,X1) != X0 | ~r2_hidden(sK10(X0,X1),X1)) & (sK10(X0,X1) = X0 | r2_hidden(sK10(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f42,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK10(X0,X1) != X0 | ~r2_hidden(sK10(X0,X1),X1)) & (sK10(X0,X1) = X0 | r2_hidden(sK10(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f21])).
% 0.22/0.54  % (24727)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    k1_xboole_0 != sK4 | k1_xboole_0 = sK5),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24741)------------------------------
% 0.22/0.54  % (24741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24741)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (24741)Memory used [KB]: 1918
% 0.22/0.54  % (24741)Time elapsed: 0.126 s
% 0.22/0.54  % (24741)------------------------------
% 0.22/0.54  % (24741)------------------------------
% 0.22/0.54  % (24713)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (24714)Refutation not found, incomplete strategy% (24714)------------------------------
% 0.22/0.54  % (24714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24715)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (24716)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (24711)Success in time 0.173 s
%------------------------------------------------------------------------------
