%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:14 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 280 expanded)
%              Number of leaves         :   33 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  426 ( 899 expanded)
%              Number of equality atoms :   40 (  91 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f984,plain,(
    $false ),
    inference(subsumption_resolution,[],[f961,f510])).

fof(f510,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f509,f68])).

fof(f68,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f509,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f508,f70])).

fof(f70,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f508,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f502,f71])).

fof(f71,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f502,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f392,f422])).

fof(f422,plain,(
    ! [X8] :
      ( r1_tarski(k2_relat_1(X8),k3_relat_1(sK1))
      | ~ r1_tarski(X8,sK1)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f421,f69])).

fof(f69,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f421,plain,(
    ! [X8] :
      ( r1_tarski(k2_relat_1(X8),k3_relat_1(sK1))
      | ~ r1_tarski(X8,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f403,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f403,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK1))
      | r1_tarski(X2,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f114,f354])).

fof(f354,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f110,f69])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f74,f108])).

fof(f108,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f87,f88])).

fof(f88,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f87,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f74,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f103,f108])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f392,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f117,f353])).

fof(f353,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f110,f68])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f107,f108])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f961,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f954,f402])).

fof(f402,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f115,f354])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f104,f108,f85])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f954,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),X0) ),
    inference(resolution,[],[f953,f160])).

fof(f160,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f105,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f953,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f553,f792])).

fof(f792,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f781,f261])).

fof(f261,plain,(
    ! [X4] :
      ( r2_hidden(sK9(X4),X4)
      | k1_xboole_0 = k1_relat_1(X4) ) ),
    inference(resolution,[],[f254,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f254,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X6))
      | r2_hidden(sK9(X6),X6) ) ),
    inference(resolution,[],[f121,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK9(X1),X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f66])).

fof(f66,plain,(
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

fof(f39,plain,(
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

fof(f121,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f61,f64,f63,f62])).

fof(f62,plain,(
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

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f781,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f766,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,sK3(X1))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f92,f79])).

fof(f79,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK3(X0))
          | r2_tarski(X2,sK3(X0))
          | ~ r1_tarski(X2,sK3(X0)) )
      & ! [X3] :
          ( ( ! [X5] :
                ( r2_hidden(X5,sK4(X0,X3))
                | ~ r1_tarski(X5,X3) )
            & r2_hidden(sK4(X0,X3),sK3(X0)) )
          | ~ r2_hidden(X3,sK3(X0)) )
      & ! [X6,X7] :
          ( r2_hidden(X7,sK3(X0))
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f54,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( ? [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X4)
                      | ~ r1_tarski(X5,X3) )
                  & r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X1) )
          & ! [X6,X7] :
              ( r2_hidden(X7,X1)
              | ~ r1_tarski(X7,X6)
              | ~ r2_hidden(X6,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK3(X0))
            | r2_tarski(X2,sK3(X0))
            | ~ r1_tarski(X2,sK3(X0)) )
        & ! [X3] :
            ( ? [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X4)
                    | ~ r1_tarski(X5,X3) )
                & r2_hidden(X4,sK3(X0)) )
            | ~ r2_hidden(X3,sK3(X0)) )
        & ! [X7,X6] :
            ( r2_hidden(X7,sK3(X0))
            | ~ r1_tarski(X7,X6)
            | ~ r2_hidden(X6,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,X4)
              | ~ r1_tarski(X5,X3) )
          & r2_hidden(X4,sK3(X0)) )
     => ( ! [X5] :
            ( r2_hidden(X5,sK4(X0,X3))
            | ~ r1_tarski(X5,X3) )
        & r2_hidden(sK4(X0,X3),sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f766,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f649,f72])).

fof(f72,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f649,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f643])).

fof(f643,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f133,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f133,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK5(X5,X6),X4)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X6) ) ),
    inference(resolution,[],[f92,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f553,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f552,f68])).

fof(f552,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f536,f69])).

fof(f536,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f75,f521])).

fof(f521,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f414,f165])).

fof(f165,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),sK1) ),
    inference(resolution,[],[f162,f111])).

fof(f111,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f162,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,sK0)
      | r1_tarski(X7,sK1) ) ),
    inference(resolution,[],[f105,f70])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f404,f111])).

fof(f404,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
      | ~ r1_tarski(k6_subset_1(X0,X1),X0)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(resolution,[],[f375,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_subset_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f93,f85])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f375,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f116,f112])).

fof(f112,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f89,f85,f85,f109])).

fof(f109,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f86,f88])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f106,f109])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (10892)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (10893)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (10887)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (10881)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (10901)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (10897)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (10870)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (10886)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (10878)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  % (10875)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (10885)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (10884)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (10876)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.58  % (10895)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.58  % (10869)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.59  % (10882)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.59  % (10868)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.59  % (10894)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.60  % (10899)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.60  % (10879)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.60  % (10890)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.60  % (10898)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.60  % (10872)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.61  % (10871)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.62  % (10891)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.95/0.63  % (10883)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.95/0.63  % (10900)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.95/0.64  % (10873)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.95/0.64  % (10888)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.17/0.64  % (10875)Refutation found. Thanks to Tanya!
% 2.17/0.64  % SZS status Theorem for theBenchmark
% 2.17/0.64  % (10880)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.24/0.65  % SZS output start Proof for theBenchmark
% 2.24/0.65  fof(f984,plain,(
% 2.24/0.65    $false),
% 2.24/0.65    inference(subsumption_resolution,[],[f961,f510])).
% 2.24/0.65  fof(f510,plain,(
% 2.24/0.65    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.24/0.65    inference(subsumption_resolution,[],[f509,f68])).
% 2.24/0.65  fof(f68,plain,(
% 2.24/0.65    v1_relat_1(sK0)),
% 2.24/0.65    inference(cnf_transformation,[],[f50])).
% 2.24/0.65  fof(f50,plain,(
% 2.24/0.65    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.24/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f49,f48])).
% 2.24/0.65  fof(f48,plain,(
% 2.24/0.65    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.24/0.65    introduced(choice_axiom,[])).
% 2.24/0.65  fof(f49,plain,(
% 2.24/0.65    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.24/0.65    introduced(choice_axiom,[])).
% 2.24/0.65  fof(f29,plain,(
% 2.24/0.65    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.24/0.65    inference(flattening,[],[f28])).
% 2.24/0.65  fof(f28,plain,(
% 2.24/0.65    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.24/0.65    inference(ennf_transformation,[],[f25])).
% 2.24/0.65  fof(f25,negated_conjecture,(
% 2.24/0.65    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.24/0.65    inference(negated_conjecture,[],[f24])).
% 2.24/0.65  fof(f24,conjecture,(
% 2.24/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.24/0.65  fof(f509,plain,(
% 2.24/0.65    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 2.24/0.65    inference(subsumption_resolution,[],[f508,f70])).
% 2.24/0.65  fof(f70,plain,(
% 2.24/0.65    r1_tarski(sK0,sK1)),
% 2.24/0.65    inference(cnf_transformation,[],[f50])).
% 2.24/0.65  fof(f508,plain,(
% 2.24/0.65    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 2.24/0.65    inference(subsumption_resolution,[],[f502,f71])).
% 2.24/0.65  fof(f71,plain,(
% 2.24/0.65    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.24/0.65    inference(cnf_transformation,[],[f50])).
% 2.24/0.65  fof(f502,plain,(
% 2.24/0.65    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 2.24/0.65    inference(resolution,[],[f392,f422])).
% 2.24/0.65  fof(f422,plain,(
% 2.24/0.65    ( ! [X8] : (r1_tarski(k2_relat_1(X8),k3_relat_1(sK1)) | ~r1_tarski(X8,sK1) | ~v1_relat_1(X8)) )),
% 2.24/0.65    inference(subsumption_resolution,[],[f421,f69])).
% 2.24/0.65  fof(f69,plain,(
% 2.24/0.65    v1_relat_1(sK1)),
% 2.24/0.65    inference(cnf_transformation,[],[f50])).
% 2.24/0.65  fof(f421,plain,(
% 2.24/0.65    ( ! [X8] : (r1_tarski(k2_relat_1(X8),k3_relat_1(sK1)) | ~r1_tarski(X8,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(X8)) )),
% 2.24/0.65    inference(resolution,[],[f403,f77])).
% 2.24/0.65  fof(f77,plain,(
% 2.24/0.65    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f33])).
% 2.24/0.65  fof(f33,plain,(
% 2.24/0.65    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.24/0.65    inference(flattening,[],[f32])).
% 2.24/0.65  fof(f32,plain,(
% 2.24/0.65    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.24/0.65    inference(ennf_transformation,[],[f23])).
% 2.24/0.65  fof(f23,axiom,(
% 2.24/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.24/0.65  fof(f403,plain,(
% 2.24/0.65    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK1)) | r1_tarski(X2,k3_relat_1(sK1))) )),
% 2.24/0.65    inference(superposition,[],[f114,f354])).
% 2.24/0.65  fof(f354,plain,(
% 2.24/0.65    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.24/0.65    inference(resolution,[],[f110,f69])).
% 2.24/0.65  fof(f110,plain,(
% 2.24/0.65    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.24/0.65    inference(definition_unfolding,[],[f74,f108])).
% 2.24/0.65  fof(f108,plain,(
% 2.24/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.24/0.65    inference(definition_unfolding,[],[f87,f88])).
% 2.24/0.65  fof(f88,plain,(
% 2.24/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f14])).
% 2.24/0.65  fof(f14,axiom,(
% 2.24/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.24/0.65  fof(f87,plain,(
% 2.24/0.65    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f15])).
% 2.24/0.65  fof(f15,axiom,(
% 2.24/0.65    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.24/0.65  fof(f74,plain,(
% 2.24/0.65    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f30])).
% 2.24/0.65  fof(f30,plain,(
% 2.24/0.65    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.24/0.65    inference(ennf_transformation,[],[f21])).
% 2.24/0.65  fof(f21,axiom,(
% 2.24/0.65    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.24/0.65  fof(f114,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.24/0.65    inference(definition_unfolding,[],[f103,f108])).
% 2.24/0.65  fof(f103,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f40])).
% 2.24/0.65  fof(f40,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.24/0.65    inference(ennf_transformation,[],[f4])).
% 2.24/0.65  fof(f4,axiom,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.24/0.65  fof(f392,plain,(
% 2.24/0.65    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.24/0.65    inference(superposition,[],[f117,f353])).
% 2.24/0.65  fof(f353,plain,(
% 2.24/0.65    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.24/0.65    inference(resolution,[],[f110,f68])).
% 2.24/0.65  fof(f117,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.24/0.65    inference(definition_unfolding,[],[f107,f108])).
% 2.24/0.65  fof(f107,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f47])).
% 2.24/0.65  fof(f47,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.24/0.65    inference(flattening,[],[f46])).
% 2.24/0.65  fof(f46,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.24/0.65    inference(ennf_transformation,[],[f13])).
% 2.24/0.65  fof(f13,axiom,(
% 2.24/0.65    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.24/0.65  fof(f961,plain,(
% 2.24/0.65    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.24/0.65    inference(resolution,[],[f954,f402])).
% 2.24/0.65  fof(f402,plain,(
% 2.24/0.65    ( ! [X1] : (~r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 2.24/0.65    inference(superposition,[],[f115,f354])).
% 2.24/0.65  fof(f115,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.24/0.65    inference(definition_unfolding,[],[f104,f108,f85])).
% 2.24/0.65  fof(f85,plain,(
% 2.24/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f18])).
% 2.24/0.65  fof(f18,axiom,(
% 2.24/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.24/0.65  fof(f104,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f41])).
% 2.24/0.65  fof(f41,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.24/0.65    inference(ennf_transformation,[],[f10])).
% 2.24/0.65  fof(f10,axiom,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.24/0.65  fof(f954,plain,(
% 2.24/0.65    ( ! [X0] : (r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),X0)) )),
% 2.24/0.65    inference(resolution,[],[f953,f160])).
% 2.24/0.65  fof(f160,plain,(
% 2.24/0.65    ( ! [X2,X3] : (~r1_tarski(X2,k1_xboole_0) | r1_tarski(X2,X3)) )),
% 2.24/0.65    inference(resolution,[],[f105,f73])).
% 2.24/0.65  fof(f73,plain,(
% 2.24/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f7])).
% 2.24/0.65  fof(f7,axiom,(
% 2.24/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.24/0.65  fof(f105,plain,(
% 2.24/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f43])).
% 2.24/0.65  fof(f43,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.24/0.65    inference(flattening,[],[f42])).
% 2.24/0.65  fof(f42,plain,(
% 2.24/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.24/0.65    inference(ennf_transformation,[],[f6])).
% 2.24/0.65  fof(f6,axiom,(
% 2.24/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.24/0.65  fof(f953,plain,(
% 2.24/0.65    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.24/0.65    inference(forward_demodulation,[],[f553,f792])).
% 2.24/0.65  fof(f792,plain,(
% 2.24/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.24/0.65    inference(resolution,[],[f781,f261])).
% 2.24/0.65  fof(f261,plain,(
% 2.24/0.65    ( ! [X4] : (r2_hidden(sK9(X4),X4) | k1_xboole_0 = k1_relat_1(X4)) )),
% 2.24/0.65    inference(resolution,[],[f254,f78])).
% 2.24/0.65  fof(f78,plain,(
% 2.24/0.65    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.24/0.65    inference(cnf_transformation,[],[f52])).
% 2.24/0.65  fof(f52,plain,(
% 2.24/0.65    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.24/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f51])).
% 2.24/0.65  fof(f51,plain,(
% 2.24/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.24/0.65    introduced(choice_axiom,[])).
% 2.24/0.65  fof(f34,plain,(
% 2.24/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.24/0.65    inference(ennf_transformation,[],[f2])).
% 2.24/0.65  fof(f2,axiom,(
% 2.24/0.65    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.24/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.24/0.65  fof(f254,plain,(
% 2.24/0.65    ( ! [X6,X5] : (~r2_hidden(X5,k1_relat_1(X6)) | r2_hidden(sK9(X6),X6)) )),
% 2.24/0.65    inference(resolution,[],[f121,f101])).
% 2.24/0.65  fof(f101,plain,(
% 2.24/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK9(X1),X1)) )),
% 2.24/0.65    inference(cnf_transformation,[],[f67])).
% 2.24/0.65  fof(f67,plain,(
% 2.24/0.65    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK9(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK9(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.24/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f66])).
% 2.24/0.66  fof(f66,plain,(
% 2.24/0.66    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK9(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK9(X1),X1)))),
% 2.24/0.66    introduced(choice_axiom,[])).
% 2.24/0.66  fof(f39,plain,(
% 2.24/0.66    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.24/0.66    inference(ennf_transformation,[],[f16])).
% 2.24/0.66  fof(f16,axiom,(
% 2.24/0.66    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 2.24/0.66  fof(f121,plain,(
% 2.24/0.66    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.24/0.66    inference(equality_resolution,[],[f97])).
% 2.24/0.66  fof(f97,plain,(
% 2.24/0.66    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.24/0.66    inference(cnf_transformation,[],[f65])).
% 2.24/0.66  fof(f65,plain,(
% 2.24/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.24/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f61,f64,f63,f62])).
% 2.24/0.66  fof(f62,plain,(
% 2.24/0.66    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 2.24/0.66    introduced(choice_axiom,[])).
% 2.24/0.66  fof(f63,plain,(
% 2.24/0.66    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 2.24/0.66    introduced(choice_axiom,[])).
% 2.24/0.66  fof(f64,plain,(
% 2.24/0.66    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 2.24/0.66    introduced(choice_axiom,[])).
% 2.24/0.66  fof(f61,plain,(
% 2.24/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.24/0.66    inference(rectify,[],[f60])).
% 2.24/0.66  fof(f60,plain,(
% 2.24/0.66    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.24/0.66    inference(nnf_transformation,[],[f20])).
% 2.24/0.66  fof(f20,axiom,(
% 2.24/0.66    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 2.24/0.66  fof(f781,plain,(
% 2.24/0.66    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.24/0.66    inference(resolution,[],[f766,f131])).
% 2.24/0.66  fof(f131,plain,(
% 2.24/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,sK3(X1)) | ~r2_hidden(X1,X0)) )),
% 2.24/0.66    inference(resolution,[],[f92,f79])).
% 2.24/0.66  fof(f79,plain,(
% 2.24/0.66    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 2.24/0.66    inference(cnf_transformation,[],[f55])).
% 2.24/0.66  fof(f55,plain,(
% 2.24/0.66    ! [X0] : (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : ((! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X6,X7] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 2.24/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f54,f53])).
% 2.24/0.66  fof(f53,plain,(
% 2.24/0.66    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X7,X6] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 2.24/0.66    introduced(choice_axiom,[])).
% 2.24/0.66  fof(f54,plain,(
% 2.24/0.66    ! [X3,X0] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) => (! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))))),
% 2.24/0.66    introduced(choice_axiom,[])).
% 2.24/0.66  fof(f36,plain,(
% 2.24/0.66    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1))),
% 2.24/0.66    inference(flattening,[],[f35])).
% 2.24/0.66  fof(f35,plain,(
% 2.24/0.66    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | (~r1_tarski(X7,X6) | ~r2_hidden(X6,X1))) & r2_hidden(X0,X1))),
% 2.24/0.66    inference(ennf_transformation,[],[f26])).
% 2.24/0.66  fof(f26,plain,(
% 2.24/0.66    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 2.24/0.66    inference(rectify,[],[f17])).
% 2.24/0.66  fof(f17,axiom,(
% 2.24/0.66    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : ~(! [X3] : ~(! [X4] : (r1_tarski(X4,X2) => r2_hidden(X4,X3)) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).
% 2.24/0.66  fof(f92,plain,(
% 2.24/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f57])).
% 2.24/0.66  fof(f57,plain,(
% 2.24/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.24/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f56])).
% 2.24/0.66  fof(f56,plain,(
% 2.24/0.66    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.24/0.66    introduced(choice_axiom,[])).
% 2.24/0.66  fof(f37,plain,(
% 2.24/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.24/0.66    inference(ennf_transformation,[],[f27])).
% 2.24/0.66  fof(f27,plain,(
% 2.24/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.24/0.66    inference(rectify,[],[f1])).
% 2.24/0.66  fof(f1,axiom,(
% 2.24/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.24/0.66  fof(f766,plain,(
% 2.24/0.66    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.24/0.66    inference(resolution,[],[f649,f72])).
% 2.24/0.66  fof(f72,plain,(
% 2.24/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f12])).
% 2.24/0.66  fof(f12,axiom,(
% 2.24/0.66    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.24/0.66  fof(f649,plain,(
% 2.24/0.66    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 2.24/0.66    inference(duplicate_literal_removal,[],[f643])).
% 2.24/0.66  fof(f643,plain,(
% 2.24/0.66    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 2.24/0.66    inference(resolution,[],[f133,f91])).
% 2.24/0.66  fof(f91,plain,(
% 2.24/0.66    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f57])).
% 2.24/0.66  fof(f133,plain,(
% 2.24/0.66    ( ! [X6,X4,X5] : (~r2_hidden(sK5(X5,X6),X4) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X5,X6)) )),
% 2.24/0.66    inference(resolution,[],[f92,f90])).
% 2.24/0.66  fof(f90,plain,(
% 2.24/0.66    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f57])).
% 2.24/0.66  fof(f553,plain,(
% 2.24/0.66    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 2.24/0.66    inference(subsumption_resolution,[],[f552,f68])).
% 2.24/0.66  fof(f552,plain,(
% 2.24/0.66    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 2.24/0.66    inference(subsumption_resolution,[],[f536,f69])).
% 2.24/0.66  fof(f536,plain,(
% 2.24/0.66    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.24/0.66    inference(superposition,[],[f75,f521])).
% 2.24/0.66  fof(f521,plain,(
% 2.24/0.66    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.24/0.66    inference(resolution,[],[f414,f165])).
% 2.24/0.66  fof(f165,plain,(
% 2.24/0.66    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),sK1)) )),
% 2.24/0.66    inference(resolution,[],[f162,f111])).
% 2.24/0.66  fof(f111,plain,(
% 2.24/0.66    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.24/0.66    inference(definition_unfolding,[],[f84,f85])).
% 2.24/0.66  fof(f84,plain,(
% 2.24/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f8])).
% 2.24/0.66  fof(f8,axiom,(
% 2.24/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.24/0.66  fof(f162,plain,(
% 2.24/0.66    ( ! [X7] : (~r1_tarski(X7,sK0) | r1_tarski(X7,sK1)) )),
% 2.24/0.66    inference(resolution,[],[f105,f70])).
% 2.24/0.66  fof(f414,plain,(
% 2.24/0.66    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.24/0.66    inference(subsumption_resolution,[],[f404,f111])).
% 2.24/0.66  fof(f404,plain,(
% 2.24/0.66    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X1) | ~r1_tarski(k6_subset_1(X0,X1),X0) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.24/0.66    inference(resolution,[],[f375,f113])).
% 2.24/0.66  fof(f113,plain,(
% 2.24/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k6_subset_1(X1,X0)) | k1_xboole_0 = X0) )),
% 2.24/0.66    inference(definition_unfolding,[],[f93,f85])).
% 2.24/0.66  fof(f93,plain,(
% 2.24/0.66    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 2.24/0.66    inference(cnf_transformation,[],[f38])).
% 2.24/0.66  fof(f38,plain,(
% 2.24/0.66    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.24/0.66    inference(ennf_transformation,[],[f9])).
% 2.24/0.66  fof(f9,axiom,(
% 2.24/0.66    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 2.24/0.66  fof(f375,plain,(
% 2.24/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.24/0.66    inference(forward_demodulation,[],[f116,f112])).
% 2.24/0.66  fof(f112,plain,(
% 2.24/0.66    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.24/0.66    inference(definition_unfolding,[],[f89,f85,f85,f109])).
% 2.24/0.66  fof(f109,plain,(
% 2.24/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.24/0.66    inference(definition_unfolding,[],[f86,f88])).
% 2.24/0.66  fof(f86,plain,(
% 2.24/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.24/0.66    inference(cnf_transformation,[],[f19])).
% 2.24/0.66  fof(f19,axiom,(
% 2.24/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.24/0.66  fof(f89,plain,(
% 2.24/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f11])).
% 2.24/0.66  fof(f11,axiom,(
% 2.24/0.66    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.24/0.66  fof(f116,plain,(
% 2.24/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.24/0.66    inference(definition_unfolding,[],[f106,f109])).
% 2.24/0.66  fof(f106,plain,(
% 2.24/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f45])).
% 2.24/0.66  fof(f45,plain,(
% 2.24/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.24/0.66    inference(flattening,[],[f44])).
% 2.24/0.66  fof(f44,plain,(
% 2.24/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.24/0.66    inference(ennf_transformation,[],[f5])).
% 2.24/0.66  fof(f5,axiom,(
% 2.24/0.66    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.24/0.66  fof(f75,plain,(
% 2.24/0.66    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.24/0.66    inference(cnf_transformation,[],[f31])).
% 2.24/0.66  fof(f31,plain,(
% 2.24/0.66    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.24/0.66    inference(ennf_transformation,[],[f22])).
% 2.24/0.66  fof(f22,axiom,(
% 2.24/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.24/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 2.24/0.66  % SZS output end Proof for theBenchmark
% 2.24/0.66  % (10875)------------------------------
% 2.24/0.66  % (10875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.66  % (10875)Termination reason: Refutation
% 2.24/0.66  
% 2.24/0.66  % (10875)Memory used [KB]: 11513
% 2.24/0.66  % (10875)Time elapsed: 0.189 s
% 2.24/0.66  % (10875)------------------------------
% 2.24/0.66  % (10875)------------------------------
% 2.24/0.67  % (10861)Success in time 0.308 s
%------------------------------------------------------------------------------
