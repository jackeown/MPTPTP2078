%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:03 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 296 expanded)
%              Number of clauses        :   65 ( 115 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   20
%              Number of atoms          :  328 ( 682 expanded)
%              Number of equality atoms :  166 ( 327 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f53,f61,f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f43])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f48])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f77])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f76,f65])).

fof(f102,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f95])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    ! [X0] : r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f78,f65])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f23,conjecture,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(negated_conjecture,[],[f23])).

fof(f40,plain,(
    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(ennf_transformation,[],[f24])).

fof(f51,plain,
    ( ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))
   => k2_subset_1(sK2) != k3_subset_1(sK2,k1_subset_1(sK2)) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    k2_subset_1(sK2) != k3_subset_1(sK2,k1_subset_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f51])).

fof(f88,plain,(
    k2_subset_1(sK2) != k3_subset_1(sK2,k1_subset_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    k2_subset_1(sK2) != k3_subset_1(sK2,k1_xboole_0) ),
    inference(definition_unfolding,[],[f88,f83])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_725,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_721,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_719,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1585,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_721,c_719])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1586,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1585,c_7])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1648,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1586,c_0])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_723,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2914,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_723])).

cnf(c_78,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2924,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_723])).

cnf(c_3387,plain,
    ( r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2914,c_78,c_2924])).

cnf(c_3388,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3387])).

cnf(c_3394,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_3388])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X3)
    | X2 = X1
    | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_720,plain,
    ( X0 = X1
    | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10216,plain,
    ( X0 = X1
    | k2_xboole_0(X2,X0) != X1
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_720])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_724,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3397,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_3388])).

cnf(c_3425,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_724,c_3397])).

cnf(c_12064,plain,
    ( r1_xboole_0(X1,X2) != iProver_top
    | k2_xboole_0(X2,X0) != X1
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10216,c_3425])).

cnf(c_12065,plain,
    ( X0 = X1
    | k2_xboole_0(X2,X0) != X1
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12064])).

cnf(c_12071,plain,
    ( X0 != X1
    | k1_xboole_0 = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_12065])).

cnf(c_12097,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_12071])).

cnf(c_12294,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3394,c_12097])).

cnf(c_19,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X2),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_715,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1279,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_715])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_262,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_tarski(X3,X3) != X1
    | k1_zfmisc_1(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_714,plain,
    ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_2425,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_714])).

cnf(c_26,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_281,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,k3_subset_1(X3,X2)) = X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_282,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_282,c_30])).

cnf(c_713,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_2448,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2425,c_713])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_298,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_309,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_299,c_30])).

cnf(c_712,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_2449,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2425,c_712])).

cnf(c_2452,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2448,c_2449])).

cnf(c_12341,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_12294,c_2452])).

cnf(c_32,negated_conjecture,
    ( k2_subset_1(sK2) != k3_subset_1(sK2,k1_xboole_0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_28,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_733,plain,
    ( k3_subset_1(sK2,k1_xboole_0) != sK2 ),
    inference(demodulation,[status(thm)],[c_32,c_28])).

cnf(c_12614,plain,
    ( sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_12341,c_733])).

cnf(c_438,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2418,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12614,c_2418])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:59:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.84/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.99  
% 3.84/0.99  ------  iProver source info
% 3.84/0.99  
% 3.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.99  git: non_committed_changes: false
% 3.84/0.99  git: last_make_outside_of_git: false
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    true
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     num_symb
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       true
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    passive
% 3.84/0.99  --sup_prop_simpl_new                    true
% 3.84/0.99  --sup_prop_simpl_given                  true
% 3.84/0.99  --sup_fun_splitting                     false
% 3.84/0.99  --sup_smt_interval                      50000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   []
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_full_bw                           [BwDemod]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         3
% 3.84/0.99  --comb_sup_mult                         2
% 3.84/0.99  --comb_inst_mult                        10
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  ------ Parsing...
% 3.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/0.99  ------ Proving...
% 3.84/0.99  ------ Problem Properties 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  clauses                                 27
% 3.84/0.99  conjectures                             1
% 3.84/0.99  EPR                                     2
% 3.84/0.99  Horn                                    21
% 3.84/0.99  unary                                   10
% 3.84/0.99  binary                                  13
% 3.84/0.99  lits                                    51
% 3.84/0.99  lits eq                                 27
% 3.84/0.99  fd_pure                                 0
% 3.84/0.99  fd_pseudo                               0
% 3.84/0.99  fd_cond                                 0
% 3.84/0.99  fd_pseudo_cond                          5
% 3.84/0.99  AC symbols                              0
% 3.84/0.99  
% 3.84/0.99  ------ Schedule dynamic 5 is on 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  Current options:
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    true
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     none
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       false
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    passive
% 3.84/0.99  --sup_prop_simpl_new                    true
% 3.84/0.99  --sup_prop_simpl_given                  true
% 3.84/0.99  --sup_fun_splitting                     false
% 3.84/0.99  --sup_smt_interval                      50000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   []
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_full_bw                           [BwDemod]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         3
% 3.84/0.99  --comb_sup_mult                         2
% 3.84/0.99  --comb_inst_mult                        10
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ Proving...
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS status Theorem for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  fof(f3,axiom,(
% 3.84/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f25,plain,(
% 3.84/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.84/0.99    inference(rectify,[],[f3])).
% 3.84/0.99  
% 3.84/0.99  fof(f29,plain,(
% 3.84/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.84/0.99    inference(ennf_transformation,[],[f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f41,plain,(
% 3.84/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f42,plain,(
% 3.84/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f41])).
% 3.84/0.99  
% 3.84/0.99  fof(f56,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f42])).
% 3.84/0.99  
% 3.84/0.99  fof(f7,axiom,(
% 3.84/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f62,plain,(
% 3.84/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f7])).
% 3.84/0.99  
% 3.84/0.99  fof(f9,axiom,(
% 3.84/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f33,plain,(
% 3.84/0.99    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.84/0.99    inference(ennf_transformation,[],[f9])).
% 3.84/0.99  
% 3.84/0.99  fof(f64,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f5,axiom,(
% 3.84/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f60,plain,(
% 3.84/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.84/0.99    inference(cnf_transformation,[],[f5])).
% 3.84/0.99  
% 3.84/0.99  fof(f1,axiom,(
% 3.84/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f53,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f1])).
% 3.84/0.99  
% 3.84/0.99  fof(f6,axiom,(
% 3.84/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f61,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f6])).
% 3.84/0.99  
% 3.84/0.99  fof(f89,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f53,f61,f61])).
% 3.84/0.99  
% 3.84/0.99  fof(f4,axiom,(
% 3.84/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f26,plain,(
% 3.84/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.84/0.99    inference(rectify,[],[f4])).
% 3.84/0.99  
% 3.84/0.99  fof(f30,plain,(
% 3.84/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.84/0.99    inference(ennf_transformation,[],[f26])).
% 3.84/0.99  
% 3.84/0.99  fof(f43,plain,(
% 3.84/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f44,plain,(
% 3.84/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f43])).
% 3.84/0.99  
% 3.84/0.99  fof(f59,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f44])).
% 3.84/0.99  
% 3.84/0.99  fof(f90,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f59,f61])).
% 3.84/0.99  
% 3.84/0.99  fof(f8,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f31,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 3.84/0.99    inference(ennf_transformation,[],[f8])).
% 3.84/0.99  
% 3.84/0.99  fof(f32,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 3.84/0.99    inference(flattening,[],[f31])).
% 3.84/0.99  
% 3.84/0.99  fof(f63,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f32])).
% 3.84/0.99  
% 3.84/0.99  fof(f55,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f42])).
% 3.84/0.99  
% 3.84/0.99  fof(f15,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f36,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f15])).
% 3.84/0.99  
% 3.84/0.99  fof(f48,plain,(
% 3.84/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 3.84/0.99    inference(nnf_transformation,[],[f36])).
% 3.84/0.99  
% 3.84/0.99  fof(f49,plain,(
% 3.84/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 3.84/0.99    inference(flattening,[],[f48])).
% 3.84/0.99  
% 3.84/0.99  fof(f77,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 3.84/0.99    inference(cnf_transformation,[],[f49])).
% 3.84/0.99  
% 3.84/0.99  fof(f101,plain,(
% 3.84/0.99    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 3.84/0.99    inference(equality_resolution,[],[f77])).
% 3.84/0.99  
% 3.84/0.99  fof(f76,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 3.84/0.99    inference(cnf_transformation,[],[f49])).
% 3.84/0.99  
% 3.84/0.99  fof(f10,axiom,(
% 3.84/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f65,plain,(
% 3.84/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f10])).
% 3.84/0.99  
% 3.84/0.99  fof(f95,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) != X0) )),
% 3.84/0.99    inference(definition_unfolding,[],[f76,f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f102,plain,(
% 3.84/0.99    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 3.84/0.99    inference(equality_resolution,[],[f95])).
% 3.84/0.99  
% 3.84/0.99  fof(f14,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f46,plain,(
% 3.84/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.84/0.99    inference(nnf_transformation,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f47,plain,(
% 3.84/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.84/0.99    inference(flattening,[],[f46])).
% 3.84/0.99  
% 3.84/0.99  fof(f70,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f2,axiom,(
% 3.84/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f27,plain,(
% 3.84/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.84/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.84/0.99  
% 3.84/0.99  fof(f28,plain,(
% 3.84/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.84/0.99    inference(ennf_transformation,[],[f27])).
% 3.84/0.99  
% 3.84/0.99  fof(f54,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f28])).
% 3.84/0.99  
% 3.84/0.99  fof(f16,axiom,(
% 3.84/0.99    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f78,plain,(
% 3.84/0.99    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f16])).
% 3.84/0.99  
% 3.84/0.99  fof(f98,plain,(
% 3.84/0.99    ( ! [X0] : (r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f78,f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f17,axiom,(
% 3.84/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f37,plain,(
% 3.84/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f17])).
% 3.84/0.99  
% 3.84/0.99  fof(f50,plain,(
% 3.84/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.84/0.99    inference(nnf_transformation,[],[f37])).
% 3.84/0.99  
% 3.84/0.99  fof(f80,plain,(
% 3.84/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f50])).
% 3.84/0.99  
% 3.84/0.99  fof(f22,axiom,(
% 3.84/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f39,plain,(
% 3.84/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f22])).
% 3.84/0.99  
% 3.84/0.99  fof(f87,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f39])).
% 3.84/0.99  
% 3.84/0.99  fof(f21,axiom,(
% 3.84/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f86,plain,(
% 3.84/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f21])).
% 3.84/0.99  
% 3.84/0.99  fof(f20,axiom,(
% 3.84/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f38,plain,(
% 3.84/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f20])).
% 3.84/0.99  
% 3.84/0.99  fof(f85,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f38])).
% 3.84/0.99  
% 3.84/0.99  fof(f23,conjecture,(
% 3.84/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f24,negated_conjecture,(
% 3.84/0.99    ~! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.84/0.99    inference(negated_conjecture,[],[f23])).
% 3.84/0.99  
% 3.84/0.99  fof(f40,plain,(
% 3.84/0.99    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f24])).
% 3.84/0.99  
% 3.84/0.99  fof(f51,plain,(
% 3.84/0.99    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) => k2_subset_1(sK2) != k3_subset_1(sK2,k1_subset_1(sK2))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f52,plain,(
% 3.84/0.99    k2_subset_1(sK2) != k3_subset_1(sK2,k1_subset_1(sK2))),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f51])).
% 3.84/0.99  
% 3.84/0.99  fof(f88,plain,(
% 3.84/0.99    k2_subset_1(sK2) != k3_subset_1(sK2,k1_subset_1(sK2))),
% 3.84/0.99    inference(cnf_transformation,[],[f52])).
% 3.84/0.99  
% 3.84/0.99  fof(f18,axiom,(
% 3.84/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f83,plain,(
% 3.84/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f18])).
% 3.84/0.99  
% 3.84/0.99  fof(f99,plain,(
% 3.84/0.99    k2_subset_1(sK2) != k3_subset_1(sK2,k1_xboole_0)),
% 3.84/0.99    inference(definition_unfolding,[],[f88,f83])).
% 3.84/0.99  
% 3.84/0.99  fof(f19,axiom,(
% 3.84/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f84,plain,(
% 3.84/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.84/0.99    inference(cnf_transformation,[],[f19])).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3,plain,
% 3.84/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK0(X0,X1),X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_725,plain,
% 3.84/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.84/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8,plain,
% 3.84/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_721,plain,
% 3.84/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10,plain,
% 3.84/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_719,plain,
% 3.84/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
% 3.84/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1585,plain,
% 3.84/0.99      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_721,c_719]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7,plain,
% 3.84/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1586,plain,
% 3.84/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_1585,c_7]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_0,plain,
% 3.84/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1648,plain,
% 3.84/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1586,c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5,plain,
% 3.84/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.84/0.99      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_723,plain,
% 3.84/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.84/0.99      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2914,plain,
% 3.84/0.99      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 3.84/0.99      | r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1648,c_723]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_78,plain,
% 3.84/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2924,plain,
% 3.84/0.99      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 3.84/0.99      | r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1586,c_723]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3387,plain,
% 3.84/0.99      ( r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2914,c_78,c_2924]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3388,plain,
% 3.84/0.99      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_3387]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3394,plain,
% 3.84/0.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X1)) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_725,c_3388]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9,plain,
% 3.84/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.84/0.99      | ~ r1_xboole_0(X2,X3)
% 3.84/0.99      | X2 = X1
% 3.84/0.99      | k2_xboole_0(X2,X0) != k2_xboole_0(X3,X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_720,plain,
% 3.84/0.99      ( X0 = X1
% 3.84/0.99      | k2_xboole_0(X0,X2) != k2_xboole_0(X3,X1)
% 3.84/0.99      | r1_xboole_0(X2,X1) != iProver_top
% 3.84/0.99      | r1_xboole_0(X0,X3) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10216,plain,
% 3.84/0.99      ( X0 = X1
% 3.84/0.99      | k2_xboole_0(X2,X0) != X1
% 3.84/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 3.84/0.99      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_7,c_720]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4,plain,
% 3.84/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_724,plain,
% 3.84/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.84/0.99      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_18,plain,
% 3.84/0.99      ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X1)) = k1_xboole_0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3397,plain,
% 3.84/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_18,c_3388]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3425,plain,
% 3.84/0.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_724,c_3397]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12064,plain,
% 3.84/0.99      ( r1_xboole_0(X1,X2) != iProver_top
% 3.84/0.99      | k2_xboole_0(X2,X0) != X1
% 3.84/0.99      | X0 = X1 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_10216,c_3425]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12065,plain,
% 3.84/0.99      ( X0 = X1
% 3.84/0.99      | k2_xboole_0(X2,X0) != X1
% 3.84/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_12064]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12071,plain,
% 3.84/0.99      ( X0 != X1 | k1_xboole_0 = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_7,c_12065]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12097,plain,
% 3.84/0.99      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 3.84/0.99      inference(equality_resolution,[status(thm)],[c_12071]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12294,plain,
% 3.84/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3394,c_12097]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_19,plain,
% 3.84/0.99      ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X0)) = k1_xboole_0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_17,plain,
% 3.84/0.99      ( r2_hidden(X0,X1)
% 3.84/0.99      | k4_xboole_0(k2_tarski(X0,X2),X1) != k1_xboole_0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_715,plain,
% 3.84/0.99      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0
% 3.84/0.99      | r2_hidden(X0,X2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1279,plain,
% 3.84/0.99      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_19,c_715]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1,plain,
% 3.84/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_23,plain,
% 3.84/0.99      ( r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_262,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,X1)
% 3.84/0.99      | r2_hidden(X0,X2)
% 3.84/0.99      | k2_tarski(X3,X3) != X1
% 3.84/0.99      | k1_zfmisc_1(X3) != X2 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_263,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,k2_tarski(X1,X1))
% 3.84/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_262]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_714,plain,
% 3.84/0.99      ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
% 3.84/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2425,plain,
% 3.84/0.99      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1279,c_714]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_26,plain,
% 3.84/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_31,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_281,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,X1)
% 3.84/0.99      | v1_xboole_0(X1)
% 3.84/0.99      | X2 != X0
% 3.84/0.99      | k3_subset_1(X3,k3_subset_1(X3,X2)) = X2
% 3.84/0.99      | k1_zfmisc_1(X3) != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_282,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.84/0.99      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.84/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_281]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_30,plain,
% 3.84/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_292,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.84/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.84/0.99      inference(forward_subsumption_resolution,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_282,c_30]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_713,plain,
% 3.84/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.84/0.99      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2448,plain,
% 3.84/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2425,c_713]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_29,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_298,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,X1)
% 3.84/0.99      | v1_xboole_0(X1)
% 3.84/0.99      | X2 != X0
% 3.84/0.99      | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
% 3.84/0.99      | k1_zfmisc_1(X3) != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_299,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.84/0.99      | v1_xboole_0(k1_zfmisc_1(X1))
% 3.84/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_298]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_309,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 3.84/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.84/0.99      inference(forward_subsumption_resolution,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_299,c_30]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_712,plain,
% 3.84/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.84/0.99      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2449,plain,
% 3.84/0.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2425,c_712]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2452,plain,
% 3.84/0.99      ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_2448,c_2449]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12341,plain,
% 3.84/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_12294,c_2452]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_32,negated_conjecture,
% 3.84/0.99      ( k2_subset_1(sK2) != k3_subset_1(sK2,k1_xboole_0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_28,plain,
% 3.84/0.99      ( k2_subset_1(X0) = X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_733,plain,
% 3.84/0.99      ( k3_subset_1(sK2,k1_xboole_0) != sK2 ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_32,c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12614,plain,
% 3.84/0.99      ( sK2 != sK2 ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_12341,c_733]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_438,plain,( X0 = X0 ),theory(equality) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2418,plain,
% 3.84/0.99      ( sK2 = sK2 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_438]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(contradiction,plain,
% 3.84/0.99      ( $false ),
% 3.84/0.99      inference(minisat,[status(thm)],[c_12614,c_2418]) ).
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  ------                               Statistics
% 3.84/0.99  
% 3.84/0.99  ------ General
% 3.84/0.99  
% 3.84/0.99  abstr_ref_over_cycles:                  0
% 3.84/0.99  abstr_ref_under_cycles:                 0
% 3.84/0.99  gc_basic_clause_elim:                   0
% 3.84/0.99  forced_gc_time:                         0
% 3.84/0.99  parsing_time:                           0.011
% 3.84/0.99  unif_index_cands_time:                  0.
% 3.84/0.99  unif_index_add_time:                    0.
% 3.84/0.99  orderings_time:                         0.
% 3.84/0.99  out_proof_time:                         0.009
% 3.84/0.99  total_time:                             0.365
% 3.84/0.99  num_of_symbols:                         47
% 3.84/0.99  num_of_terms:                           17560
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing
% 3.84/0.99  
% 3.84/0.99  num_of_splits:                          0
% 3.84/0.99  num_of_split_atoms:                     0
% 3.84/0.99  num_of_reused_defs:                     0
% 3.84/0.99  num_eq_ax_congr_red:                    31
% 3.84/0.99  num_of_sem_filtered_clauses:            1
% 3.84/0.99  num_of_subtypes:                        0
% 3.84/0.99  monotx_restored_types:                  0
% 3.84/0.99  sat_num_of_epr_types:                   0
% 3.84/0.99  sat_num_of_non_cyclic_types:            0
% 3.84/0.99  sat_guarded_non_collapsed_types:        0
% 3.84/0.99  num_pure_diseq_elim:                    0
% 3.84/0.99  simp_replaced_by:                       0
% 3.84/0.99  res_preprocessed:                       131
% 3.84/0.99  prep_upred:                             0
% 3.84/0.99  prep_unflattend:                        10
% 3.84/0.99  smt_new_axioms:                         0
% 3.84/0.99  pred_elim_cands:                        2
% 3.84/0.99  pred_elim:                              3
% 3.84/0.99  pred_elim_cl:                           6
% 3.84/0.99  pred_elim_cycles:                       5
% 3.84/0.99  merged_defs:                            0
% 3.84/0.99  merged_defs_ncl:                        0
% 3.84/0.99  bin_hyper_res:                          0
% 3.84/0.99  prep_cycles:                            4
% 3.84/0.99  pred_elim_time:                         0.002
% 3.84/0.99  splitting_time:                         0.
% 3.84/0.99  sem_filter_time:                        0.
% 3.84/0.99  monotx_time:                            0.
% 3.84/0.99  subtype_inf_time:                       0.
% 3.84/0.99  
% 3.84/0.99  ------ Problem properties
% 3.84/0.99  
% 3.84/0.99  clauses:                                27
% 3.84/0.99  conjectures:                            1
% 3.84/0.99  epr:                                    2
% 3.84/0.99  horn:                                   21
% 3.84/0.99  ground:                                 1
% 3.84/0.99  unary:                                  10
% 3.84/0.99  binary:                                 13
% 3.84/0.99  lits:                                   51
% 3.84/0.99  lits_eq:                                27
% 3.84/0.99  fd_pure:                                0
% 3.84/0.99  fd_pseudo:                              0
% 3.84/0.99  fd_cond:                                0
% 3.84/0.99  fd_pseudo_cond:                         5
% 3.84/0.99  ac_symbols:                             0
% 3.84/0.99  
% 3.84/0.99  ------ Propositional Solver
% 3.84/0.99  
% 3.84/0.99  prop_solver_calls:                      27
% 3.84/0.99  prop_fast_solver_calls:                 710
% 3.84/0.99  smt_solver_calls:                       0
% 3.84/0.99  smt_fast_solver_calls:                  0
% 3.84/0.99  prop_num_of_clauses:                    4475
% 3.84/0.99  prop_preprocess_simplified:             8992
% 3.84/0.99  prop_fo_subsumed:                       3
% 3.84/0.99  prop_solver_time:                       0.
% 3.84/0.99  smt_solver_time:                        0.
% 3.84/0.99  smt_fast_solver_time:                   0.
% 3.84/0.99  prop_fast_solver_time:                  0.
% 3.84/0.99  prop_unsat_core_time:                   0.
% 3.84/0.99  
% 3.84/0.99  ------ QBF
% 3.84/0.99  
% 3.84/0.99  qbf_q_res:                              0
% 3.84/0.99  qbf_num_tautologies:                    0
% 3.84/0.99  qbf_prep_cycles:                        0
% 3.84/0.99  
% 3.84/0.99  ------ BMC1
% 3.84/0.99  
% 3.84/0.99  bmc1_current_bound:                     -1
% 3.84/0.99  bmc1_last_solved_bound:                 -1
% 3.84/0.99  bmc1_unsat_core_size:                   -1
% 3.84/0.99  bmc1_unsat_core_parents_size:           -1
% 3.84/0.99  bmc1_merge_next_fun:                    0
% 3.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation
% 3.84/0.99  
% 3.84/0.99  inst_num_of_clauses:                    1195
% 3.84/0.99  inst_num_in_passive:                    262
% 3.84/0.99  inst_num_in_active:                     391
% 3.84/0.99  inst_num_in_unprocessed:                542
% 3.84/0.99  inst_num_of_loops:                      520
% 3.84/0.99  inst_num_of_learning_restarts:          0
% 3.84/0.99  inst_num_moves_active_passive:          128
% 3.84/0.99  inst_lit_activity:                      0
% 3.84/0.99  inst_lit_activity_moves:                0
% 3.84/0.99  inst_num_tautologies:                   0
% 3.84/0.99  inst_num_prop_implied:                  0
% 3.84/0.99  inst_num_existing_simplified:           0
% 3.84/0.99  inst_num_eq_res_simplified:             0
% 3.84/0.99  inst_num_child_elim:                    0
% 3.84/0.99  inst_num_of_dismatching_blockings:      474
% 3.84/0.99  inst_num_of_non_proper_insts:           1143
% 3.84/0.99  inst_num_of_duplicates:                 0
% 3.84/0.99  inst_inst_num_from_inst_to_res:         0
% 3.84/0.99  inst_dismatching_checking_time:         0.
% 3.84/0.99  
% 3.84/0.99  ------ Resolution
% 3.84/0.99  
% 3.84/0.99  res_num_of_clauses:                     0
% 3.84/0.99  res_num_in_passive:                     0
% 3.84/0.99  res_num_in_active:                      0
% 3.84/0.99  res_num_of_loops:                       135
% 3.84/0.99  res_forward_subset_subsumed:            87
% 3.84/0.99  res_backward_subset_subsumed:           2
% 3.84/0.99  res_forward_subsumed:                   2
% 3.84/0.99  res_backward_subsumed:                  0
% 3.84/0.99  res_forward_subsumption_resolution:     2
% 3.84/0.99  res_backward_subsumption_resolution:    0
% 3.84/0.99  res_clause_to_clause_subsumption:       3470
% 3.84/0.99  res_orphan_elimination:                 0
% 3.84/0.99  res_tautology_del:                      20
% 3.84/0.99  res_num_eq_res_simplified:              0
% 3.84/0.99  res_num_sel_changes:                    0
% 3.84/0.99  res_moves_from_active_to_pass:          0
% 3.84/0.99  
% 3.84/0.99  ------ Superposition
% 3.84/0.99  
% 3.84/0.99  sup_time_total:                         0.
% 3.84/0.99  sup_time_generating:                    0.
% 3.84/0.99  sup_time_sim_full:                      0.
% 3.84/0.99  sup_time_sim_immed:                     0.
% 3.84/0.99  
% 3.84/0.99  sup_num_of_clauses:                     416
% 3.84/0.99  sup_num_in_active:                      68
% 3.84/0.99  sup_num_in_passive:                     348
% 3.84/0.99  sup_num_of_loops:                       102
% 3.84/0.99  sup_fw_superposition:                   1049
% 3.84/0.99  sup_bw_superposition:                   597
% 3.84/0.99  sup_immediate_simplified:               682
% 3.84/0.99  sup_given_eliminated:                   0
% 3.84/0.99  comparisons_done:                       0
% 3.84/0.99  comparisons_avoided:                    3
% 3.84/0.99  
% 3.84/0.99  ------ Simplifications
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  sim_fw_subset_subsumed:                 14
% 3.84/0.99  sim_bw_subset_subsumed:                 1
% 3.84/0.99  sim_fw_subsumed:                        226
% 3.84/0.99  sim_bw_subsumed:                        1
% 3.84/0.99  sim_fw_subsumption_res:                 0
% 3.84/0.99  sim_bw_subsumption_res:                 0
% 3.84/0.99  sim_tautology_del:                      9
% 3.84/0.99  sim_eq_tautology_del:                   174
% 3.84/0.99  sim_eq_res_simp:                        7
% 3.84/0.99  sim_fw_demodulated:                     378
% 3.84/0.99  sim_bw_demodulated:                     37
% 3.84/0.99  sim_light_normalised:                   243
% 3.84/0.99  sim_joinable_taut:                      0
% 3.84/0.99  sim_joinable_simp:                      0
% 3.84/0.99  sim_ac_normalised:                      0
% 3.84/0.99  sim_smt_subsumption:                    0
% 3.84/0.99  
%------------------------------------------------------------------------------
