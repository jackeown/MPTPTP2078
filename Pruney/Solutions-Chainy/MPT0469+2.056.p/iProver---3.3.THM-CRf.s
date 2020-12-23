%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:51 EST 2020

% Result     : Theorem 6.80s
% Output     : CNFRefutation 6.80s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 572 expanded)
%              Number of clauses        :  107 ( 228 expanded)
%              Number of leaves         :   28 ( 165 expanded)
%              Depth                    :   14
%              Number of atoms          :  475 (1670 expanded)
%              Number of equality atoms :  181 ( 519 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f49,f48,f47])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k1_tarski(X2)
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k1_tarski(X2)
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k2_tarski(X2,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)) ) ),
    inference(definition_unfolding,[],[f64,f60,f60])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f60])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f43,f42,f41])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f12,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f57])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f22])).

fof(f81,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_20438,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_20394,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19897,plain,
    ( m1_subset_1(X0,k1_relat_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(k1_xboole_0)))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_19899,plain,
    ( m1_subset_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0)))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_19897])).

cnf(c_19750,plain,
    ( m1_subset_1(X0,k2_relat_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_19752,plain,
    ( m1_subset_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_19750])).

cnf(c_25,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_8574,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_25,c_26])).

cnf(c_369,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_366,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5019,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_369,c_366])).

cnf(c_367,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1996,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_367,c_366])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2179,plain,
    ( ~ v1_xboole_0(X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1996,c_6])).

cnf(c_6125,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_5019,c_2179])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6307,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6125,c_4])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
    | k2_tarski(X2,X2) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1990,plain,
    ( ~ v1_xboole_0(X0)
    | X1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_367,c_6])).

cnf(c_3836,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
    | ~ v1_xboole_0(k2_tarski(X0,X1))
    | k1_xboole_0 = k2_tarski(X2,X2) ),
    inference(resolution,[status(thm)],[c_11,c_1990])).

cnf(c_8586,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X1))
    | k1_xboole_0 = k2_tarski(X2,X2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6307,c_3836])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2180,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1996,c_5])).

cnf(c_368,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2204,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2180,c_368])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2338,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2204,c_0])).

cnf(c_2339,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_2338])).

cnf(c_3650,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(resolution,[status(thm)],[c_8,c_2339])).

cnf(c_9123,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k1_xboole_0 = k2_tarski(X1,X1) ),
    inference(resolution,[status(thm)],[c_8586,c_3650])).

cnf(c_18727,plain,
    ( r2_hidden(sK4(X0,k1_xboole_0),k2_relat_1(X0))
    | k2_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 = k2_tarski(X1,X1) ),
    inference(resolution,[status(thm)],[c_8574,c_9123])).

cnf(c_18728,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 = k2_tarski(X1,X1)
    | r2_hidden(sK4(X0,k1_xboole_0),k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18727])).

cnf(c_18730,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_18728])).

cnf(c_22,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_21,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6898,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_22,c_21])).

cnf(c_15255,plain,
    ( r2_hidden(sK1(X0,k1_xboole_0),k1_relat_1(X0))
    | k1_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 = k2_tarski(X1,X1) ),
    inference(resolution,[status(thm)],[c_6898,c_9123])).

cnf(c_15257,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15255])).

cnf(c_9133,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | k1_relat_1(k1_xboole_0) = X0
    | k1_xboole_0 = k2_tarski(X1,X1) ),
    inference(resolution,[status(thm)],[c_9123,c_21])).

cnf(c_9135,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9133])).

cnf(c_1010,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1013,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2143,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK4(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_1013])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1012,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1027,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1032,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1938,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1032])).

cnf(c_1961,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1938])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1026,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2704,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1961,c_1026])).

cnf(c_2714,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_2704])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1025,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3169,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2714,c_1025])).

cnf(c_7786,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK4(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2143,c_3169])).

cnf(c_8059,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7786])).

cnf(c_20,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),X2),X0)
    | ~ r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1015,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4769,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_1015])).

cnf(c_4776,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | k1_relat_1(X0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4769])).

cnf(c_4778,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4776])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1008,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1820,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK6(X1,X0),k1_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1008,c_1013])).

cnf(c_3783,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_3169])).

cnf(c_3803,plain,
    ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3783])).

cnf(c_3805,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3803])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X2),k4_xboole_0(k2_tarski(X0,X2),X1)) != k2_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1023,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1)
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3612,plain,
    ( k2_tarski(X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1023])).

cnf(c_3622,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | k2_tarski(X0,X1) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3612])).

cnf(c_3624,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | k2_tarski(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3622])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1011,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3499,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) != iProver_top
    | r2_hidden(sK4(X0,X1),k2_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1008,c_1011])).

cnf(c_3507,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k2_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3499])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3481,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(k1_xboole_0))
    | r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3491,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3481])).

cnf(c_3189,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3169])).

cnf(c_3191,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3189])).

cnf(c_1391,plain,
    ( X0 != X1
    | k2_tarski(X2,X2) != X1
    | k2_tarski(X2,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1715,plain,
    ( X0 != k2_tarski(X1,X1)
    | k2_tarski(X1,X1) = X0
    | k2_tarski(X1,X1) != k2_tarski(X1,X1) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_1716,plain,
    ( k2_tarski(k1_xboole_0,k1_xboole_0) != k2_tarski(k1_xboole_0,k1_xboole_0)
    | k2_tarski(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1715])).

cnf(c_1488,plain,
    ( ~ m1_subset_1(X0,k2_relat_1(k1_xboole_0))
    | r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_1387,plain,
    ( k2_tarski(X0,X0) = k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_1390,plain,
    ( k2_tarski(k1_xboole_0,k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_1376,plain,
    ( k2_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1377,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1271,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

cnf(c_1254,plain,
    ( k1_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1255,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1234,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_95,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_92,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20438,c_20394,c_19899,c_19752,c_18730,c_15257,c_9135,c_8059,c_4778,c_3805,c_3624,c_3507,c_3491,c_3191,c_1716,c_1498,c_1390,c_1377,c_1271,c_1255,c_1234,c_95,c_92,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:48:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 6.80/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.80/1.48  
% 6.80/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.80/1.48  
% 6.80/1.48  ------  iProver source info
% 6.80/1.48  
% 6.80/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.80/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.80/1.48  git: non_committed_changes: false
% 6.80/1.48  git: last_make_outside_of_git: false
% 6.80/1.48  
% 6.80/1.48  ------ 
% 6.80/1.48  ------ Parsing...
% 6.80/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.80/1.48  
% 6.80/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.80/1.48  
% 6.80/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.80/1.48  
% 6.80/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.80/1.48  ------ Proving...
% 6.80/1.48  ------ Problem Properties 
% 6.80/1.48  
% 6.80/1.48  
% 6.80/1.48  clauses                                 29
% 6.80/1.48  conjectures                             1
% 6.80/1.48  EPR                                     10
% 6.80/1.48  Horn                                    24
% 6.80/1.48  unary                                   6
% 6.80/1.48  binary                                  12
% 6.80/1.48  lits                                    63
% 6.80/1.48  lits eq                                 12
% 6.80/1.48  fd_pure                                 0
% 6.80/1.48  fd_pseudo                               0
% 6.80/1.48  fd_cond                                 2
% 6.80/1.48  fd_pseudo_cond                          5
% 6.80/1.48  AC symbols                              0
% 6.80/1.48  
% 6.80/1.48  ------ Input Options Time Limit: Unbounded
% 6.80/1.48  
% 6.80/1.48  
% 6.80/1.48  ------ 
% 6.80/1.48  Current options:
% 6.80/1.48  ------ 
% 6.80/1.48  
% 6.80/1.48  
% 6.80/1.48  
% 6.80/1.48  
% 6.80/1.48  ------ Proving...
% 6.80/1.48  
% 6.80/1.48  
% 6.80/1.48  % SZS status Theorem for theBenchmark.p
% 6.80/1.48  
% 6.80/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.80/1.48  
% 6.80/1.48  fof(f17,axiom,(
% 6.80/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f71,plain,(
% 6.80/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 6.80/1.48    inference(cnf_transformation,[],[f17])).
% 6.80/1.48  
% 6.80/1.48  fof(f18,axiom,(
% 6.80/1.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f32,plain,(
% 6.80/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 6.80/1.48    inference(ennf_transformation,[],[f18])).
% 6.80/1.48  
% 6.80/1.48  fof(f33,plain,(
% 6.80/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 6.80/1.48    inference(flattening,[],[f32])).
% 6.80/1.48  
% 6.80/1.48  fof(f72,plain,(
% 6.80/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f33])).
% 6.80/1.48  
% 6.80/1.48  fof(f20,axiom,(
% 6.80/1.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f45,plain,(
% 6.80/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 6.80/1.48    inference(nnf_transformation,[],[f20])).
% 6.80/1.48  
% 6.80/1.48  fof(f46,plain,(
% 6.80/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.80/1.48    inference(rectify,[],[f45])).
% 6.80/1.48  
% 6.80/1.48  fof(f49,plain,(
% 6.80/1.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 6.80/1.48    introduced(choice_axiom,[])).
% 6.80/1.48  
% 6.80/1.48  fof(f48,plain,(
% 6.80/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 6.80/1.48    introduced(choice_axiom,[])).
% 6.80/1.48  
% 6.80/1.48  fof(f47,plain,(
% 6.80/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 6.80/1.48    introduced(choice_axiom,[])).
% 6.80/1.48  
% 6.80/1.48  fof(f50,plain,(
% 6.80/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 6.80/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f49,f48,f47])).
% 6.80/1.48  
% 6.80/1.48  fof(f79,plain,(
% 6.80/1.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f50])).
% 6.80/1.48  
% 6.80/1.48  fof(f78,plain,(
% 6.80/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 6.80/1.48    inference(cnf_transformation,[],[f50])).
% 6.80/1.48  
% 6.80/1.48  fof(f90,plain,(
% 6.80/1.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 6.80/1.48    inference(equality_resolution,[],[f78])).
% 6.80/1.48  
% 6.80/1.48  fof(f8,axiom,(
% 6.80/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f25,plain,(
% 6.80/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 6.80/1.48    inference(ennf_transformation,[],[f8])).
% 6.80/1.48  
% 6.80/1.48  fof(f58,plain,(
% 6.80/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f25])).
% 6.80/1.48  
% 6.80/1.48  fof(f5,axiom,(
% 6.80/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f55,plain,(
% 6.80/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f5])).
% 6.80/1.48  
% 6.80/1.48  fof(f13,axiom,(
% 6.80/1.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f27,plain,(
% 6.80/1.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k1_tarski(X2) | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 6.80/1.48    inference(ennf_transformation,[],[f13])).
% 6.80/1.48  
% 6.80/1.48  fof(f64,plain,(
% 6.80/1.48    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k1_tarski(X2) | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 6.80/1.48    inference(cnf_transformation,[],[f27])).
% 6.80/1.48  
% 6.80/1.48  fof(f10,axiom,(
% 6.80/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f60,plain,(
% 6.80/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f10])).
% 6.80/1.48  
% 6.80/1.48  fof(f86,plain,(
% 6.80/1.48    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X2,X2) | ~r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) )),
% 6.80/1.48    inference(definition_unfolding,[],[f64,f60,f60])).
% 6.80/1.48  
% 6.80/1.48  fof(f11,axiom,(
% 6.80/1.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f37,plain,(
% 6.80/1.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 6.80/1.48    inference(nnf_transformation,[],[f11])).
% 6.80/1.48  
% 6.80/1.48  fof(f62,plain,(
% 6.80/1.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f37])).
% 6.80/1.48  
% 6.80/1.48  fof(f84,plain,(
% 6.80/1.48    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.80/1.48    inference(definition_unfolding,[],[f62,f60])).
% 6.80/1.48  
% 6.80/1.48  fof(f6,axiom,(
% 6.80/1.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f24,plain,(
% 6.80/1.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 6.80/1.48    inference(ennf_transformation,[],[f6])).
% 6.80/1.48  
% 6.80/1.48  fof(f56,plain,(
% 6.80/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f24])).
% 6.80/1.48  
% 6.80/1.48  fof(f1,axiom,(
% 6.80/1.48    v1_xboole_0(k1_xboole_0)),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f51,plain,(
% 6.80/1.48    v1_xboole_0(k1_xboole_0)),
% 6.80/1.48    inference(cnf_transformation,[],[f1])).
% 6.80/1.48  
% 6.80/1.48  fof(f19,axiom,(
% 6.80/1.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f39,plain,(
% 6.80/1.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 6.80/1.48    inference(nnf_transformation,[],[f19])).
% 6.80/1.48  
% 6.80/1.48  fof(f40,plain,(
% 6.80/1.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.80/1.48    inference(rectify,[],[f39])).
% 6.80/1.48  
% 6.80/1.48  fof(f43,plain,(
% 6.80/1.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 6.80/1.48    introduced(choice_axiom,[])).
% 6.80/1.48  
% 6.80/1.48  fof(f42,plain,(
% 6.80/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 6.80/1.48    introduced(choice_axiom,[])).
% 6.80/1.48  
% 6.80/1.48  fof(f41,plain,(
% 6.80/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 6.80/1.48    introduced(choice_axiom,[])).
% 6.80/1.48  
% 6.80/1.48  fof(f44,plain,(
% 6.80/1.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 6.80/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f43,f42,f41])).
% 6.80/1.48  
% 6.80/1.48  fof(f74,plain,(
% 6.80/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 6.80/1.48    inference(cnf_transformation,[],[f44])).
% 6.80/1.48  
% 6.80/1.48  fof(f88,plain,(
% 6.80/1.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 6.80/1.48    inference(equality_resolution,[],[f74])).
% 6.80/1.48  
% 6.80/1.48  fof(f75,plain,(
% 6.80/1.48    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f44])).
% 6.80/1.48  
% 6.80/1.48  fof(f73,plain,(
% 6.80/1.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 6.80/1.48    inference(cnf_transformation,[],[f44])).
% 6.80/1.48  
% 6.80/1.48  fof(f89,plain,(
% 6.80/1.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 6.80/1.48    inference(equality_resolution,[],[f73])).
% 6.80/1.48  
% 6.80/1.48  fof(f4,axiom,(
% 6.80/1.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f54,plain,(
% 6.80/1.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f4])).
% 6.80/1.48  
% 6.80/1.48  fof(f7,axiom,(
% 6.80/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f57,plain,(
% 6.80/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.80/1.48    inference(cnf_transformation,[],[f7])).
% 6.80/1.48  
% 6.80/1.48  fof(f83,plain,(
% 6.80/1.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 6.80/1.48    inference(definition_unfolding,[],[f54,f57])).
% 6.80/1.48  
% 6.80/1.48  fof(f3,axiom,(
% 6.80/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f23,plain,(
% 6.80/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 6.80/1.48    inference(ennf_transformation,[],[f3])).
% 6.80/1.48  
% 6.80/1.48  fof(f53,plain,(
% 6.80/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 6.80/1.48    inference(cnf_transformation,[],[f23])).
% 6.80/1.48  
% 6.80/1.48  fof(f82,plain,(
% 6.80/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 6.80/1.48    inference(definition_unfolding,[],[f53,f57])).
% 6.80/1.48  
% 6.80/1.48  fof(f61,plain,(
% 6.80/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f37])).
% 6.80/1.48  
% 6.80/1.48  fof(f85,plain,(
% 6.80/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 6.80/1.48    inference(definition_unfolding,[],[f61,f60])).
% 6.80/1.48  
% 6.80/1.48  fof(f12,axiom,(
% 6.80/1.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f63,plain,(
% 6.80/1.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 6.80/1.48    inference(cnf_transformation,[],[f12])).
% 6.80/1.48  
% 6.80/1.48  fof(f76,plain,(
% 6.80/1.48    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f44])).
% 6.80/1.48  
% 6.80/1.48  fof(f77,plain,(
% 6.80/1.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 6.80/1.48    inference(cnf_transformation,[],[f50])).
% 6.80/1.48  
% 6.80/1.48  fof(f91,plain,(
% 6.80/1.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 6.80/1.48    inference(equality_resolution,[],[f77])).
% 6.80/1.48  
% 6.80/1.48  fof(f14,axiom,(
% 6.80/1.48    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f28,plain,(
% 6.80/1.48    ! [X0,X1,X2] : (r2_hidden(X0,X2) | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1))),
% 6.80/1.48    inference(ennf_transformation,[],[f14])).
% 6.80/1.48  
% 6.80/1.48  fof(f65,plain,(
% 6.80/1.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f28])).
% 6.80/1.48  
% 6.80/1.48  fof(f87,plain,(
% 6.80/1.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1)) )),
% 6.80/1.48    inference(definition_unfolding,[],[f65,f57])).
% 6.80/1.48  
% 6.80/1.48  fof(f80,plain,(
% 6.80/1.48    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f50])).
% 6.80/1.48  
% 6.80/1.48  fof(f15,axiom,(
% 6.80/1.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f29,plain,(
% 6.80/1.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 6.80/1.48    inference(ennf_transformation,[],[f15])).
% 6.80/1.48  
% 6.80/1.48  fof(f38,plain,(
% 6.80/1.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 6.80/1.48    inference(nnf_transformation,[],[f29])).
% 6.80/1.48  
% 6.80/1.48  fof(f66,plain,(
% 6.80/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 6.80/1.48    inference(cnf_transformation,[],[f38])).
% 6.80/1.48  
% 6.80/1.48  fof(f21,conjecture,(
% 6.80/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 6.80/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.80/1.48  
% 6.80/1.48  fof(f22,negated_conjecture,(
% 6.80/1.48    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 6.80/1.48    inference(negated_conjecture,[],[f21])).
% 6.80/1.48  
% 6.80/1.48  fof(f34,plain,(
% 6.80/1.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 6.80/1.48    inference(ennf_transformation,[],[f22])).
% 6.80/1.48  
% 6.80/1.48  fof(f81,plain,(
% 6.80/1.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 6.80/1.48    inference(cnf_transformation,[],[f34])).
% 6.80/1.48  
% 6.80/1.48  cnf(c_18,plain,
% 6.80/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 6.80/1.48      inference(cnf_transformation,[],[f71]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_20438,plain,
% 6.80/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_20394,plain,
% 6.80/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0))) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_19,plain,
% 6.80/1.48      ( m1_subset_1(X0,X1)
% 6.80/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.80/1.48      | ~ r2_hidden(X0,X2) ),
% 6.80/1.48      inference(cnf_transformation,[],[f72]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_19897,plain,
% 6.80/1.48      ( m1_subset_1(X0,k1_relat_1(k1_xboole_0))
% 6.80/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(k1_xboole_0)))
% 6.80/1.48      | ~ r2_hidden(X0,X1) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_19899,plain,
% 6.80/1.48      ( m1_subset_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
% 6.80/1.48      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0)))
% 6.80/1.48      | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_19897]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_19750,plain,
% 6.80/1.48      ( m1_subset_1(X0,k2_relat_1(k1_xboole_0))
% 6.80/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))
% 6.80/1.48      | ~ r2_hidden(X0,X1) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_19752,plain,
% 6.80/1.48      ( m1_subset_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
% 6.80/1.48      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))
% 6.80/1.48      | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_19750]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_25,plain,
% 6.80/1.48      ( r2_hidden(sK4(X0,X1),X1)
% 6.80/1.48      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
% 6.80/1.48      | k2_relat_1(X0) = X1 ),
% 6.80/1.48      inference(cnf_transformation,[],[f79]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_26,plain,
% 6.80/1.48      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f90]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_8574,plain,
% 6.80/1.48      ( r2_hidden(sK4(X0,X1),X1)
% 6.80/1.48      | r2_hidden(sK4(X0,X1),k2_relat_1(X0))
% 6.80/1.48      | k2_relat_1(X0) = X1 ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_25,c_26]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_369,plain,
% 6.80/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.80/1.48      theory(equality) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_366,plain,( X0 = X0 ),theory(equality) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_5019,plain,
% 6.80/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_369,c_366]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_367,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1996,plain,
% 6.80/1.48      ( X0 != X1 | X1 = X0 ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_367,c_366]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_6,plain,
% 6.80/1.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 6.80/1.48      inference(cnf_transformation,[],[f58]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2179,plain,
% 6.80/1.48      ( ~ v1_xboole_0(X0) | X0 = k1_xboole_0 ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_1996,c_6]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_6125,plain,
% 6.80/1.48      ( r1_tarski(X0,X1)
% 6.80/1.48      | ~ r1_tarski(k1_xboole_0,X1)
% 6.80/1.48      | ~ v1_xboole_0(X0) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_5019,c_2179]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_4,plain,
% 6.80/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 6.80/1.48      inference(cnf_transformation,[],[f55]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_6307,plain,
% 6.80/1.48      ( r1_tarski(X0,X1) | ~ v1_xboole_0(X0) ),
% 6.80/1.48      inference(forward_subsumption_resolution,
% 6.80/1.48                [status(thm)],
% 6.80/1.48                [c_6125,c_4]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_11,plain,
% 6.80/1.48      ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
% 6.80/1.48      | k2_tarski(X2,X2) = k2_tarski(X0,X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f86]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1990,plain,
% 6.80/1.48      ( ~ v1_xboole_0(X0) | X1 != X0 | k1_xboole_0 = X1 ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_367,c_6]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3836,plain,
% 6.80/1.48      ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
% 6.80/1.48      | ~ v1_xboole_0(k2_tarski(X0,X1))
% 6.80/1.48      | k1_xboole_0 = k2_tarski(X2,X2) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_11,c_1990]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_8586,plain,
% 6.80/1.48      ( ~ v1_xboole_0(k2_tarski(X0,X1))
% 6.80/1.48      | k1_xboole_0 = k2_tarski(X2,X2) ),
% 6.80/1.48      inference(backward_subsumption_resolution,
% 6.80/1.48                [status(thm)],
% 6.80/1.48                [c_6307,c_3836]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_8,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f84]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_5,plain,
% 6.80/1.48      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 6.80/1.48      inference(cnf_transformation,[],[f56]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2180,plain,
% 6.80/1.48      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k1_xboole_0 ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_1996,c_5]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_368,plain,
% 6.80/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.80/1.48      theory(equality) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2204,plain,
% 6.80/1.48      ( ~ r1_tarski(X0,k1_xboole_0)
% 6.80/1.48      | v1_xboole_0(X0)
% 6.80/1.48      | ~ v1_xboole_0(k1_xboole_0) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_2180,c_368]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_0,plain,
% 6.80/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 6.80/1.48      inference(cnf_transformation,[],[f51]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2338,plain,
% 6.80/1.48      ( v1_xboole_0(X0) | ~ r1_tarski(X0,k1_xboole_0) ),
% 6.80/1.48      inference(global_propositional_subsumption,
% 6.80/1.48                [status(thm)],
% 6.80/1.48                [c_2204,c_0]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2339,plain,
% 6.80/1.48      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 6.80/1.48      inference(renaming,[status(thm)],[c_2338]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3650,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,k1_xboole_0) | v1_xboole_0(k2_tarski(X0,X0)) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_8,c_2339]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_9123,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k2_tarski(X1,X1) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_8586,c_3650]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_18727,plain,
% 6.80/1.48      ( r2_hidden(sK4(X0,k1_xboole_0),k2_relat_1(X0))
% 6.80/1.48      | k2_relat_1(X0) = k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k2_tarski(X1,X1) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_8574,c_9123]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_18728,plain,
% 6.80/1.48      ( k2_relat_1(X0) = k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k2_tarski(X1,X1)
% 6.80/1.48      | r2_hidden(sK4(X0,k1_xboole_0),k2_relat_1(X0)) = iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_18727]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_18730,plain,
% 6.80/1.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)
% 6.80/1.48      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k2_relat_1(k1_xboole_0)) = iProver_top ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_18728]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_22,plain,
% 6.80/1.48      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f88]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_21,plain,
% 6.80/1.48      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 6.80/1.48      | r2_hidden(sK1(X0,X1),X1)
% 6.80/1.48      | k1_relat_1(X0) = X1 ),
% 6.80/1.48      inference(cnf_transformation,[],[f75]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_6898,plain,
% 6.80/1.48      ( r2_hidden(sK1(X0,X1),X1)
% 6.80/1.48      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 6.80/1.48      | k1_relat_1(X0) = X1 ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_22,c_21]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_15255,plain,
% 6.80/1.48      ( r2_hidden(sK1(X0,k1_xboole_0),k1_relat_1(X0))
% 6.80/1.48      | k1_relat_1(X0) = k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k2_tarski(X1,X1) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_6898,c_9123]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_15257,plain,
% 6.80/1.48      ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 6.80/1.48      | k1_relat_1(k1_xboole_0) = k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_15255]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_9133,plain,
% 6.80/1.48      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
% 6.80/1.48      | k1_relat_1(k1_xboole_0) = X0
% 6.80/1.48      | k1_xboole_0 = k2_tarski(X1,X1) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_9123,c_21]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_9135,plain,
% 6.80/1.48      ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 6.80/1.48      | k1_relat_1(k1_xboole_0) = k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_9133]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1010,plain,
% 6.80/1.48      ( k2_relat_1(X0) = X1
% 6.80/1.48      | r2_hidden(sK4(X0,X1),X1) = iProver_top
% 6.80/1.48      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1013,plain,
% 6.80/1.48      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 6.80/1.48      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2143,plain,
% 6.80/1.48      ( k2_relat_1(X0) = X1
% 6.80/1.48      | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) = iProver_top
% 6.80/1.48      | r2_hidden(sK4(X0,X1),X1) = iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1010,c_1013]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_23,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.80/1.48      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f89]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1012,plain,
% 6.80/1.48      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 6.80/1.48      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1027,plain,
% 6.80/1.48      ( r2_hidden(X0,X1) != iProver_top
% 6.80/1.48      | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3,plain,
% 6.80/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 6.80/1.48      inference(cnf_transformation,[],[f83]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2,plain,
% 6.80/1.48      ( r1_tarski(X0,X1)
% 6.80/1.48      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 6.80/1.48      inference(cnf_transformation,[],[f82]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1032,plain,
% 6.80/1.48      ( r1_tarski(X0,X1) = iProver_top
% 6.80/1.48      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1938,plain,
% 6.80/1.48      ( r1_tarski(X0,X1) = iProver_top
% 6.80/1.48      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_3,c_1032]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1961,plain,
% 6.80/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 6.80/1.48      | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1027,c_1938]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_9,plain,
% 6.80/1.48      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f85]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1026,plain,
% 6.80/1.48      ( r2_hidden(X0,X1) = iProver_top
% 6.80/1.48      | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2704,plain,
% 6.80/1.48      ( r2_hidden(X0,X1) = iProver_top
% 6.80/1.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1961,c_1026]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_2714,plain,
% 6.80/1.48      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 6.80/1.48      | r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),X1) = iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1012,c_2704]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_10,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 6.80/1.48      inference(cnf_transformation,[],[f63]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1025,plain,
% 6.80/1.48      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3169,plain,
% 6.80/1.48      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_2714,c_1025]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_7786,plain,
% 6.80/1.48      ( k2_relat_1(k1_xboole_0) = X0
% 6.80/1.48      | r2_hidden(sK4(k1_xboole_0,X0),X0) = iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_2143,c_3169]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_8059,plain,
% 6.80/1.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 6.80/1.48      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_7786]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_20,plain,
% 6.80/1.48      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),X2),X0)
% 6.80/1.48      | ~ r2_hidden(sK1(X0,X1),X1)
% 6.80/1.48      | k1_relat_1(X0) = X1 ),
% 6.80/1.48      inference(cnf_transformation,[],[f76]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1015,plain,
% 6.80/1.48      ( k1_relat_1(X0) = X1
% 6.80/1.48      | r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) != iProver_top
% 6.80/1.48      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_4769,plain,
% 6.80/1.48      ( k1_relat_1(X0) = X1
% 6.80/1.48      | r2_hidden(sK1(X0,X1),X1) != iProver_top
% 6.80/1.48      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) != iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1012,c_1015]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_4776,plain,
% 6.80/1.48      ( ~ r2_hidden(sK1(X0,X1),X1)
% 6.80/1.48      | ~ r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 6.80/1.48      | k1_relat_1(X0) = X1 ),
% 6.80/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_4769]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_4778,plain,
% 6.80/1.48      ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 6.80/1.48      | ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 6.80/1.48      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_4776]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_27,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 6.80/1.48      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f91]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1008,plain,
% 6.80/1.48      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 6.80/1.48      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1820,plain,
% 6.80/1.48      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 6.80/1.48      | r2_hidden(sK6(X1,X0),k1_relat_1(X1)) = iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1008,c_1013]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3783,plain,
% 6.80/1.48      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1820,c_3169]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3803,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_3783]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3805,plain,
% 6.80/1.48      ( ~ r2_hidden(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_3803]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_12,plain,
% 6.80/1.48      ( r2_hidden(X0,X1)
% 6.80/1.48      | k4_xboole_0(k2_tarski(X0,X2),k4_xboole_0(k2_tarski(X0,X2),X1)) != k2_tarski(X0,X2) ),
% 6.80/1.48      inference(cnf_transformation,[],[f87]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1023,plain,
% 6.80/1.48      ( k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1)
% 6.80/1.48      | r2_hidden(X0,X2) = iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3612,plain,
% 6.80/1.48      ( k2_tarski(X0,X1) != k1_xboole_0
% 6.80/1.48      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_3,c_1023]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3622,plain,
% 6.80/1.48      ( r2_hidden(X0,k1_xboole_0) | k2_tarski(X0,X1) != k1_xboole_0 ),
% 6.80/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_3612]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3624,plain,
% 6.80/1.48      ( r2_hidden(k1_xboole_0,k1_xboole_0)
% 6.80/1.48      | k2_tarski(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_3622]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_24,plain,
% 6.80/1.48      ( ~ r2_hidden(sK4(X0,X1),X1)
% 6.80/1.48      | ~ r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0)
% 6.80/1.48      | k2_relat_1(X0) = X1 ),
% 6.80/1.48      inference(cnf_transformation,[],[f80]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1011,plain,
% 6.80/1.48      ( k2_relat_1(X0) = X1
% 6.80/1.48      | r2_hidden(sK4(X0,X1),X1) != iProver_top
% 6.80/1.48      | r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) != iProver_top ),
% 6.80/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3499,plain,
% 6.80/1.48      ( k2_relat_1(X0) = X1
% 6.80/1.48      | r2_hidden(sK4(X0,X1),X1) != iProver_top
% 6.80/1.48      | r2_hidden(sK4(X0,X1),k2_relat_1(X0)) != iProver_top ),
% 6.80/1.48      inference(superposition,[status(thm)],[c_1008,c_1011]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3507,plain,
% 6.80/1.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 6.80/1.48      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k2_relat_1(k1_xboole_0)) != iProver_top
% 6.80/1.48      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_3499]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_16,plain,
% 6.80/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.80/1.48      inference(cnf_transformation,[],[f66]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3481,plain,
% 6.80/1.48      ( ~ m1_subset_1(X0,k1_relat_1(k1_xboole_0))
% 6.80/1.48      | r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 6.80/1.48      | v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3491,plain,
% 6.80/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
% 6.80/1.48      | r2_hidden(k1_xboole_0,k1_relat_1(k1_xboole_0))
% 6.80/1.48      | v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_3481]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3189,plain,
% 6.80/1.48      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_3169]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_3191,plain,
% 6.80/1.48      ( ~ r2_hidden(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_3189]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1391,plain,
% 6.80/1.48      ( X0 != X1 | k2_tarski(X2,X2) != X1 | k2_tarski(X2,X2) = X0 ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_367]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1715,plain,
% 6.80/1.48      ( X0 != k2_tarski(X1,X1)
% 6.80/1.48      | k2_tarski(X1,X1) = X0
% 6.80/1.48      | k2_tarski(X1,X1) != k2_tarski(X1,X1) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_1391]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1716,plain,
% 6.80/1.48      ( k2_tarski(k1_xboole_0,k1_xboole_0) != k2_tarski(k1_xboole_0,k1_xboole_0)
% 6.80/1.48      | k2_tarski(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 6.80/1.48      | k1_xboole_0 != k2_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_1715]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1488,plain,
% 6.80/1.48      ( ~ m1_subset_1(X0,k2_relat_1(k1_xboole_0))
% 6.80/1.48      | r2_hidden(X0,k2_relat_1(k1_xboole_0))
% 6.80/1.48      | v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1498,plain,
% 6.80/1.48      ( ~ m1_subset_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
% 6.80/1.48      | r2_hidden(k1_xboole_0,k2_relat_1(k1_xboole_0))
% 6.80/1.48      | v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_1488]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1387,plain,
% 6.80/1.48      ( k2_tarski(X0,X0) = k2_tarski(X0,X0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_366]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1390,plain,
% 6.80/1.48      ( k2_tarski(k1_xboole_0,k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_1387]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1376,plain,
% 6.80/1.48      ( k2_relat_1(k1_xboole_0) != X0
% 6.80/1.48      | k1_xboole_0 != X0
% 6.80/1.48      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_367]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1377,plain,
% 6.80/1.48      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 6.80/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_1376]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_28,negated_conjecture,
% 6.80/1.48      ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 6.80/1.48      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 6.80/1.48      inference(cnf_transformation,[],[f81]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1271,plain,
% 6.80/1.48      ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
% 6.80/1.48      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 6.80/1.48      inference(resolution,[status(thm)],[c_6,c_28]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1254,plain,
% 6.80/1.48      ( k1_relat_1(k1_xboole_0) != X0
% 6.80/1.48      | k1_xboole_0 != X0
% 6.80/1.48      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_367]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1255,plain,
% 6.80/1.48      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 6.80/1.48      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 6.80/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_1254]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_1234,plain,
% 6.80/1.48      ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
% 6.80/1.48      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_95,plain,
% 6.80/1.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(c_92,plain,
% 6.80/1.48      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 6.80/1.48      | k1_xboole_0 = k1_xboole_0 ),
% 6.80/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 6.80/1.48  
% 6.80/1.48  cnf(contradiction,plain,
% 6.80/1.48      ( $false ),
% 6.80/1.48      inference(minisat,
% 6.80/1.48                [status(thm)],
% 6.80/1.48                [c_20438,c_20394,c_19899,c_19752,c_18730,c_15257,c_9135,
% 6.80/1.48                 c_8059,c_4778,c_3805,c_3624,c_3507,c_3491,c_3191,c_1716,
% 6.80/1.48                 c_1498,c_1390,c_1377,c_1271,c_1255,c_1234,c_95,c_92,
% 6.80/1.48                 c_28]) ).
% 6.80/1.48  
% 6.80/1.48  
% 6.80/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.80/1.48  
% 6.80/1.48  ------                               Statistics
% 6.80/1.48  
% 6.80/1.48  ------ Selected
% 6.80/1.48  
% 6.80/1.48  total_time:                             0.713
% 6.80/1.48  
%------------------------------------------------------------------------------
