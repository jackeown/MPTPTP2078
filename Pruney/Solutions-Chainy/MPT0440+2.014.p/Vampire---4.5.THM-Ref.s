%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 222 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  289 ( 897 expanded)
%              Number of equality atoms :  144 ( 455 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(global_subsumption,[],[f39,f582,f662])).

fof(f662,plain,(
    k1_tarski(sK1) = k2_relat_1(sK2) ),
    inference(equality_resolution,[],[f661])).

fof(f661,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_tarski(X0) = k2_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f660,f96])).

fof(f96,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f40,f91])).

fof(f91,plain,(
    k2_relat_1(sK2) = k2_xboole_0(k1_tarski(sK1),k2_relat_1(sK2)) ),
    inference(resolution,[],[f88,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f88,plain,(
    r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f62,f69])).

fof(f69,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f65,f38])).

fof(f38,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f65,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f62,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f660,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 = k2_relat_1(sK2)
      | k1_tarski(X0) = k2_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f657])).

fof(f657,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 = k2_relat_1(sK2)
      | k1_tarski(X0) = k2_relat_1(sK2)
      | k1_tarski(X0) = k2_relat_1(sK2) ) ),
    inference(superposition,[],[f56,f625])).

fof(f625,plain,(
    ! [X3] :
      ( sK1 = sK10(k2_relat_1(sK2),X3)
      | k1_tarski(X3) = k2_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f623,f96])).

fof(f623,plain,(
    ! [X3] :
      ( sK1 = sK10(k2_relat_1(sK2),X3)
      | k1_xboole_0 = k2_relat_1(sK2)
      | k1_tarski(X3) = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f616,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f14,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f616,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | sK1 = X0 ) ),
    inference(resolution,[],[f612,f63])).

fof(f63,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f612,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK1 = X1 ) ),
    inference(superposition,[],[f608,f38])).

fof(f608,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X1 = X3 ) ),
    inference(forward_demodulation,[],[f58,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK10(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f582,plain,(
    k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(equality_resolution,[],[f581])).

fof(f581,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_tarski(X0) = k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f580,f87])).

fof(f87,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(superposition,[],[f40,f83])).

fof(f83,plain,(
    k1_relat_1(sK2) = k2_xboole_0(k1_tarski(sK0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f81,f42])).

fof(f81,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f60,f69])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f580,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = k1_relat_1(sK2)
      | k1_tarski(X0) = k1_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f577])).

fof(f577,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = k1_relat_1(sK2)
      | k1_tarski(X0) = k1_relat_1(sK2)
      | k1_tarski(X0) = k1_relat_1(sK2) ) ),
    inference(superposition,[],[f56,f546])).

fof(f546,plain,(
    ! [X3] :
      ( sK0 = sK10(k1_relat_1(sK2),X3)
      | k1_tarski(X3) = k1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f545,f87])).

fof(f545,plain,(
    ! [X3] :
      ( sK0 = sK10(k1_relat_1(sK2),X3)
      | k1_xboole_0 = k1_relat_1(sK2)
      | k1_tarski(X3) = k1_relat_1(sK2) ) ),
    inference(resolution,[],[f540,f55])).

fof(f540,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | sK0 = X1 ) ),
    inference(resolution,[],[f535,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f535,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK0 = X0 ) ),
    inference(superposition,[],[f531,f38])).

fof(f531,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3)))
      | X0 = X2 ) ),
    inference(forward_demodulation,[],[f57,f41])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:40:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.44  % (1084)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (1071)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (1093)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (1086)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.48  % (1074)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (1072)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (1077)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (1085)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (1077)Refutation not found, incomplete strategy% (1077)------------------------------
% 0.20/0.49  % (1077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1077)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1077)Memory used [KB]: 10618
% 0.20/0.49  % (1077)Time elapsed: 0.113 s
% 0.20/0.49  % (1077)------------------------------
% 0.20/0.49  % (1077)------------------------------
% 0.20/0.49  % (1078)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.49  % (1091)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (1087)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.49  % (1094)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.49  % (1076)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (1090)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (1081)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (1070)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (1089)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (1073)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (1079)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (1092)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (1080)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (1083)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (1095)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (1096)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (1088)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (1082)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.56  % (1092)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f663,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(global_subsumption,[],[f39,f582,f662])).
% 0.20/0.56  fof(f662,plain,(
% 0.20/0.56    k1_tarski(sK1) = k2_relat_1(sK2)),
% 0.20/0.56    inference(equality_resolution,[],[f661])).
% 0.20/0.56  fof(f661,plain,(
% 0.20/0.56    ( ! [X0] : (sK1 != X0 | k1_tarski(X0) = k2_relat_1(sK2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f660,f96])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    k1_xboole_0 != k2_relat_1(sK2)),
% 0.20/0.56    inference(superposition,[],[f40,f91])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    k2_relat_1(sK2) = k2_xboole_0(k1_tarski(sK1),k2_relat_1(sK2))),
% 0.20/0.56    inference(resolution,[],[f88,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    r2_hidden(sK1,k2_relat_1(sK2))),
% 0.20/0.56    inference(resolution,[],[f62,f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.56    inference(superposition,[],[f65,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 0.20/0.56    inference(flattening,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.20/0.56    inference(negated_conjecture,[],[f9])).
% 0.20/0.56  fof(f9,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.56    inference(equality_resolution,[],[f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.56    inference(equality_resolution,[],[f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.56    inference(rectify,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f24,f27,f26,f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.56    inference(rectify,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.56  fof(f660,plain,(
% 0.20/0.56    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = k2_relat_1(sK2) | k1_tarski(X0) = k2_relat_1(sK2)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f657])).
% 0.20/0.56  fof(f657,plain,(
% 0.20/0.56    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = k2_relat_1(sK2) | k1_tarski(X0) = k2_relat_1(sK2) | k1_tarski(X0) = k2_relat_1(sK2)) )),
% 0.20/0.56    inference(superposition,[],[f56,f625])).
% 0.20/0.56  fof(f625,plain,(
% 0.20/0.56    ( ! [X3] : (sK1 = sK10(k2_relat_1(sK2),X3) | k1_tarski(X3) = k2_relat_1(sK2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f623,f96])).
% 0.20/0.56  fof(f623,plain,(
% 0.20/0.56    ( ! [X3] : (sK1 = sK10(k2_relat_1(sK2),X3) | k1_xboole_0 = k2_relat_1(sK2) | k1_tarski(X3) = k2_relat_1(sK2)) )),
% 0.20/0.56    inference(resolution,[],[f616,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1] : ((sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f14,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.20/0.56  fof(f616,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | sK1 = X0) )),
% 0.20/0.56    inference(resolution,[],[f612,f63])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f612,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) )),
% 0.20/0.56    inference(superposition,[],[f608,f38])).
% 0.20/0.56  fof(f608,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X1 = X3) )),
% 0.20/0.56    inference(forward_demodulation,[],[f58,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.20/0.56    inference(flattening,[],[f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.20/0.56    inference(nnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sK10(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f582,plain,(
% 0.20/0.56    k1_tarski(sK0) = k1_relat_1(sK2)),
% 0.20/0.56    inference(equality_resolution,[],[f581])).
% 0.20/0.56  fof(f581,plain,(
% 0.20/0.56    ( ! [X0] : (sK0 != X0 | k1_tarski(X0) = k1_relat_1(sK2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f580,f87])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    k1_xboole_0 != k1_relat_1(sK2)),
% 0.20/0.56    inference(superposition,[],[f40,f83])).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    k1_relat_1(sK2) = k2_xboole_0(k1_tarski(sK0),k1_relat_1(sK2))),
% 0.20/0.56    inference(resolution,[],[f81,f42])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.56    inference(resolution,[],[f60,f69])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.56    inference(rectify,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.56  fof(f580,plain,(
% 0.20/0.56    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = k1_relat_1(sK2) | k1_tarski(X0) = k1_relat_1(sK2)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f577])).
% 0.20/0.56  fof(f577,plain,(
% 0.20/0.56    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = k1_relat_1(sK2) | k1_tarski(X0) = k1_relat_1(sK2) | k1_tarski(X0) = k1_relat_1(sK2)) )),
% 0.20/0.56    inference(superposition,[],[f56,f546])).
% 0.20/0.56  fof(f546,plain,(
% 0.20/0.56    ( ! [X3] : (sK0 = sK10(k1_relat_1(sK2),X3) | k1_tarski(X3) = k1_relat_1(sK2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f545,f87])).
% 0.20/0.56  fof(f545,plain,(
% 0.20/0.56    ( ! [X3] : (sK0 = sK10(k1_relat_1(sK2),X3) | k1_xboole_0 = k1_relat_1(sK2) | k1_tarski(X3) = k1_relat_1(sK2)) )),
% 0.20/0.56    inference(resolution,[],[f540,f55])).
% 0.20/0.56  fof(f540,plain,(
% 0.20/0.56    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | sK0 = X1) )),
% 0.20/0.56    inference(resolution,[],[f535,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f535,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) )),
% 0.20/0.56    inference(superposition,[],[f531,f38])).
% 0.20/0.56  fof(f531,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(k4_tarski(X2,X3))) | X0 = X2) )),
% 0.20/0.56    inference(forward_demodulation,[],[f57,f41])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (1092)------------------------------
% 0.20/0.56  % (1092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (1092)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (1092)Memory used [KB]: 7164
% 0.20/0.56  % (1092)Time elapsed: 0.163 s
% 0.20/0.56  % (1092)------------------------------
% 0.20/0.56  % (1092)------------------------------
% 0.20/0.57  % (1068)Success in time 0.222 s
%------------------------------------------------------------------------------
