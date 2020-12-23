%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:47 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 749 expanded)
%              Number of clauses        :  109 ( 278 expanded)
%              Number of leaves         :   22 ( 144 expanded)
%              Depth                    :   22
%              Number of atoms          :  520 (2570 expanded)
%              Number of equality atoms :  220 ( 599 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12))
      & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
      & v1_funct_1(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ~ r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12))
    & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    & v1_funct_1(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f35,f70])).

fof(f131,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
    inference(cnf_transformation,[],[f71])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f130,plain,(
    v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f71])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f132,plain,(
    ~ r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(cnf_transformation,[],[f71])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f136,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f144,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f126])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_52,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_7367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_12633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_7367])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_193,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17596,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12633,c_193])).

cnf(c_17597,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_17596])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK4(X0,X1),X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7406,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK4(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_59,negated_conjecture,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_7363,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_56,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_54,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_56,c_54])).

cnf(c_57,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_55,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_779,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_775,c_57,c_55])).

cnf(c_780,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_779])).

cnf(c_7358,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_8502,plain,
    ( sK12 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK11,sK12,sK13)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK11,sK12)) = iProver_top
    | v1_funct_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_7363,c_7358])).

cnf(c_60,negated_conjecture,
    ( v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_61,plain,
    ( v1_funct_1(sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_8678,plain,
    ( r2_hidden(X0,k1_funct_2(sK11,sK12)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK11,sK12,sK13)) != iProver_top
    | sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8502,c_61])).

cnf(c_8679,plain,
    ( sK12 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK11,sK12,sK13)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8678])).

cnf(c_8685,plain,
    ( sK12 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK11,sK12,sK13),X0) = iProver_top
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),X0),k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7406,c_8679])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK4(X0,X1),X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7407,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK4(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9175,plain,
    ( sK12 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8685,c_7407])).

cnf(c_58,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_63,plain,
    ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_9484,plain,
    ( sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9175,c_63])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7408,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8675,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7406,c_7408])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7398,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8450,plain,
    ( r1_tarski(sK13,k2_zfmisc_1(sK11,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7363,c_7398])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7402,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9342,plain,
    ( k2_zfmisc_1(sK11,sK12) = sK13
    | r1_tarski(k2_zfmisc_1(sK11,sK12),sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_8450,c_7402])).

cnf(c_9449,plain,
    ( k2_zfmisc_1(sK11,sK12) = sK13
    | v1_xboole_0(k2_zfmisc_1(sK11,sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8675,c_9342])).

cnf(c_9486,plain,
    ( k2_zfmisc_1(sK11,k1_xboole_0) = sK13
    | v1_xboole_0(k2_zfmisc_1(sK11,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9484,c_9449])).

cnf(c_9496,plain,
    ( sK13 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9486,c_11])).

cnf(c_9897,plain,
    ( sK13 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9496,c_193])).

cnf(c_7364,plain,
    ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_8933,plain,
    ( v1_xboole_0(k5_partfun1(sK11,sK12,sK13)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8675,c_7364])).

cnf(c_9489,plain,
    ( v1_xboole_0(k5_partfun1(sK11,k1_xboole_0,sK13)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9484,c_8933])).

cnf(c_9901,plain,
    ( v1_xboole_0(k5_partfun1(sK11,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9897,c_9489])).

cnf(c_17612,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_17597,c_9901])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_179,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_180,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_181,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_182,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_184,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_6235,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_8044,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK13)
    | X0 != sK13 ),
    inference(instantiation,[status(thm)],[c_6235])).

cnf(c_8045,plain,
    ( X0 != sK13
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8044])).

cnf(c_8047,plain,
    ( k1_xboole_0 != sK13
    | v1_funct_1(sK13) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8045])).

cnf(c_6223,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8585,plain,
    ( X0 != X1
    | X0 = sK13
    | sK13 != X1 ),
    inference(instantiation,[status(thm)],[c_6223])).

cnf(c_8586,plain,
    ( sK13 != k1_xboole_0
    | k1_xboole_0 = sK13
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8585])).

cnf(c_17770,plain,
    ( v1_xboole_0(sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17612,c_61,c_179,c_180,c_181,c_184,c_193,c_8047,c_8586,c_9496])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7403,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17774,plain,
    ( sK11 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17770,c_7403])).

cnf(c_6226,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_16128,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_6226])).

cnf(c_16130,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16128])).

cnf(c_15912,plain,
    ( X0 != X1
    | X0 = sK11
    | sK11 != X1 ),
    inference(instantiation,[status(thm)],[c_6223])).

cnf(c_15913,plain,
    ( sK11 != k1_xboole_0
    | k1_xboole_0 = sK11
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15912])).

cnf(c_6225,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7813,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X2)
    | X2 != X1
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != X0 ),
    inference(instantiation,[status(thm)],[c_6225])).

cnf(c_8263,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X0)
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X1)
    | X1 != X0
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_7813])).

cnf(c_11948,plain,
    ( r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X0)
    | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13))
    | X0 != k5_partfun1(sK11,sK12,sK13)
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_8263])).

cnf(c_14398,plain,
    ( r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(X0,X1,X2))
    | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13))
    | k5_partfun1(X0,X1,X2) != k5_partfun1(sK11,sK12,sK13)
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_11948])).

cnf(c_14400,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13))
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK11,sK12,sK13)
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_14398])).

cnf(c_13224,plain,
    ( X0 != X1
    | X0 = sK12
    | sK12 != X1 ),
    inference(instantiation,[status(thm)],[c_6223])).

cnf(c_13225,plain,
    ( sK12 != k1_xboole_0
    | k1_xboole_0 = sK12
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13224])).

cnf(c_10514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_10516,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_10514])).

cnf(c_6237,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
    theory(equality)).

cnf(c_10096,plain,
    ( X0 != sK13
    | X1 != sK12
    | X2 != sK11
    | k5_partfun1(X2,X1,X0) = k5_partfun1(sK11,sK12,sK13) ),
    inference(instantiation,[status(thm)],[c_6237])).

cnf(c_10097,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(sK11,sK12,sK13)
    | k1_xboole_0 != sK13
    | k1_xboole_0 != sK12
    | k1_xboole_0 != sK11 ),
    inference(instantiation,[status(thm)],[c_10096])).

cnf(c_53,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_799,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X5 != X3
    | X2 != X4
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_53,c_56])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_800,c_57,c_55])).

cnf(c_9533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(k1_xboole_0,X1,X0))
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_9535,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9533])).

cnf(c_6236,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
    theory(equality)).

cnf(c_8317,plain,
    ( k1_funct_2(sK11,sK12) = k1_funct_2(X0,X1)
    | sK12 != X1
    | sK11 != X0 ),
    inference(instantiation,[status(thm)],[c_6236])).

cnf(c_8318,plain,
    ( k1_funct_2(sK11,sK12) = k1_funct_2(k1_xboole_0,k1_xboole_0)
    | sK12 != k1_xboole_0
    | sK11 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8317])).

cnf(c_7498,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
    | k1_funct_2(sK11,sK12) != X1
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != X0 ),
    inference(instantiation,[status(thm)],[c_6225])).

cnf(c_7675,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
    | k1_funct_2(sK11,sK12) != k1_funct_2(X1,X2)
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != X0 ),
    inference(instantiation,[status(thm)],[c_7498])).

cnf(c_8230,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(X0,X1))
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
    | k1_funct_2(sK11,sK12) != k1_funct_2(X0,X1)
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_7675])).

cnf(c_8232,plain,
    ( r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(k1_xboole_0,k1_xboole_0))
    | k1_funct_2(sK11,sK12) != k1_funct_2(k1_xboole_0,k1_xboole_0)
    | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_8230])).

cnf(c_6222,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8109,plain,
    ( sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) = sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_6222])).

cnf(c_8046,plain,
    ( ~ v1_funct_1(sK13)
    | v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK13 ),
    inference(instantiation,[status(thm)],[c_8044])).

cnf(c_7469,plain,
    ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7470,plain,
    ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12))
    | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_183,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17774,c_16130,c_15913,c_14400,c_13225,c_10516,c_10097,c_9535,c_9496,c_9175,c_8586,c_8318,c_8232,c_8109,c_8046,c_7469,c_7470,c_193,c_183,c_181,c_180,c_63,c_58,c_60])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.83/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.98  
% 3.83/0.98  ------  iProver source info
% 3.83/0.98  
% 3.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.98  git: non_committed_changes: false
% 3.83/0.98  git: last_make_outside_of_git: false
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options
% 3.83/0.98  
% 3.83/0.98  --out_options                           all
% 3.83/0.98  --tptp_safe_out                         true
% 3.83/0.98  --problem_path                          ""
% 3.83/0.98  --include_path                          ""
% 3.83/0.98  --clausifier                            res/vclausify_rel
% 3.83/0.98  --clausifier_options                    ""
% 3.83/0.98  --stdin                                 false
% 3.83/0.98  --stats_out                             all
% 3.83/0.98  
% 3.83/0.98  ------ General Options
% 3.83/0.98  
% 3.83/0.98  --fof                                   false
% 3.83/0.98  --time_out_real                         305.
% 3.83/0.98  --time_out_virtual                      -1.
% 3.83/0.98  --symbol_type_check                     false
% 3.83/0.98  --clausify_out                          false
% 3.83/0.98  --sig_cnt_out                           false
% 3.83/0.98  --trig_cnt_out                          false
% 3.83/0.98  --trig_cnt_out_tolerance                1.
% 3.83/0.98  --trig_cnt_out_sk_spl                   false
% 3.83/0.98  --abstr_cl_out                          false
% 3.83/0.98  
% 3.83/0.98  ------ Global Options
% 3.83/0.98  
% 3.83/0.98  --schedule                              default
% 3.83/0.98  --add_important_lit                     false
% 3.83/0.98  --prop_solver_per_cl                    1000
% 3.83/0.98  --min_unsat_core                        false
% 3.83/0.98  --soft_assumptions                      false
% 3.83/0.98  --soft_lemma_size                       3
% 3.83/0.98  --prop_impl_unit_size                   0
% 3.83/0.98  --prop_impl_unit                        []
% 3.83/0.98  --share_sel_clauses                     true
% 3.83/0.98  --reset_solvers                         false
% 3.83/0.98  --bc_imp_inh                            [conj_cone]
% 3.83/0.98  --conj_cone_tolerance                   3.
% 3.83/0.98  --extra_neg_conj                        none
% 3.83/0.98  --large_theory_mode                     true
% 3.83/0.98  --prolific_symb_bound                   200
% 3.83/0.98  --lt_threshold                          2000
% 3.83/0.98  --clause_weak_htbl                      true
% 3.83/0.98  --gc_record_bc_elim                     false
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing Options
% 3.83/0.98  
% 3.83/0.98  --preprocessing_flag                    true
% 3.83/0.98  --time_out_prep_mult                    0.1
% 3.83/0.98  --splitting_mode                        input
% 3.83/0.98  --splitting_grd                         true
% 3.83/0.98  --splitting_cvd                         false
% 3.83/0.98  --splitting_cvd_svl                     false
% 3.83/0.98  --splitting_nvd                         32
% 3.83/0.98  --sub_typing                            true
% 3.83/0.98  --prep_gs_sim                           true
% 3.83/0.98  --prep_unflatten                        true
% 3.83/0.98  --prep_res_sim                          true
% 3.83/0.98  --prep_upred                            true
% 3.83/0.98  --prep_sem_filter                       exhaustive
% 3.83/0.98  --prep_sem_filter_out                   false
% 3.83/0.98  --pred_elim                             true
% 3.83/0.98  --res_sim_input                         true
% 3.83/0.98  --eq_ax_congr_red                       true
% 3.83/0.98  --pure_diseq_elim                       true
% 3.83/0.98  --brand_transform                       false
% 3.83/0.98  --non_eq_to_eq                          false
% 3.83/0.98  --prep_def_merge                        true
% 3.83/0.98  --prep_def_merge_prop_impl              false
% 3.83/0.98  --prep_def_merge_mbd                    true
% 3.83/0.98  --prep_def_merge_tr_red                 false
% 3.83/0.98  --prep_def_merge_tr_cl                  false
% 3.83/0.98  --smt_preprocessing                     true
% 3.83/0.98  --smt_ac_axioms                         fast
% 3.83/0.98  --preprocessed_out                      false
% 3.83/0.98  --preprocessed_stats                    false
% 3.83/0.98  
% 3.83/0.98  ------ Abstraction refinement Options
% 3.83/0.98  
% 3.83/0.98  --abstr_ref                             []
% 3.83/0.98  --abstr_ref_prep                        false
% 3.83/0.98  --abstr_ref_until_sat                   false
% 3.83/0.98  --abstr_ref_sig_restrict                funpre
% 3.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.98  --abstr_ref_under                       []
% 3.83/0.98  
% 3.83/0.98  ------ SAT Options
% 3.83/0.98  
% 3.83/0.98  --sat_mode                              false
% 3.83/0.98  --sat_fm_restart_options                ""
% 3.83/0.98  --sat_gr_def                            false
% 3.83/0.98  --sat_epr_types                         true
% 3.83/0.98  --sat_non_cyclic_types                  false
% 3.83/0.98  --sat_finite_models                     false
% 3.83/0.98  --sat_fm_lemmas                         false
% 3.83/0.98  --sat_fm_prep                           false
% 3.83/0.98  --sat_fm_uc_incr                        true
% 3.83/0.98  --sat_out_model                         small
% 3.83/0.98  --sat_out_clauses                       false
% 3.83/0.98  
% 3.83/0.98  ------ QBF Options
% 3.83/0.98  
% 3.83/0.98  --qbf_mode                              false
% 3.83/0.98  --qbf_elim_univ                         false
% 3.83/0.98  --qbf_dom_inst                          none
% 3.83/0.98  --qbf_dom_pre_inst                      false
% 3.83/0.98  --qbf_sk_in                             false
% 3.83/0.98  --qbf_pred_elim                         true
% 3.83/0.98  --qbf_split                             512
% 3.83/0.98  
% 3.83/0.98  ------ BMC1 Options
% 3.83/0.98  
% 3.83/0.98  --bmc1_incremental                      false
% 3.83/0.98  --bmc1_axioms                           reachable_all
% 3.83/0.98  --bmc1_min_bound                        0
% 3.83/0.98  --bmc1_max_bound                        -1
% 3.83/0.98  --bmc1_max_bound_default                -1
% 3.83/0.98  --bmc1_symbol_reachability              true
% 3.83/0.98  --bmc1_property_lemmas                  false
% 3.83/0.98  --bmc1_k_induction                      false
% 3.83/0.98  --bmc1_non_equiv_states                 false
% 3.83/0.98  --bmc1_deadlock                         false
% 3.83/0.98  --bmc1_ucm                              false
% 3.83/0.98  --bmc1_add_unsat_core                   none
% 3.83/0.98  --bmc1_unsat_core_children              false
% 3.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.98  --bmc1_out_stat                         full
% 3.83/0.98  --bmc1_ground_init                      false
% 3.83/0.98  --bmc1_pre_inst_next_state              false
% 3.83/0.98  --bmc1_pre_inst_state                   false
% 3.83/0.98  --bmc1_pre_inst_reach_state             false
% 3.83/0.98  --bmc1_out_unsat_core                   false
% 3.83/0.98  --bmc1_aig_witness_out                  false
% 3.83/0.98  --bmc1_verbose                          false
% 3.83/0.98  --bmc1_dump_clauses_tptp                false
% 3.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.98  --bmc1_dump_file                        -
% 3.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.98  --bmc1_ucm_extend_mode                  1
% 3.83/0.98  --bmc1_ucm_init_mode                    2
% 3.83/0.98  --bmc1_ucm_cone_mode                    none
% 3.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.98  --bmc1_ucm_relax_model                  4
% 3.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.98  --bmc1_ucm_layered_model                none
% 3.83/0.98  --bmc1_ucm_max_lemma_size               10
% 3.83/0.98  
% 3.83/0.98  ------ AIG Options
% 3.83/0.98  
% 3.83/0.98  --aig_mode                              false
% 3.83/0.98  
% 3.83/0.98  ------ Instantiation Options
% 3.83/0.98  
% 3.83/0.98  --instantiation_flag                    true
% 3.83/0.98  --inst_sos_flag                         true
% 3.83/0.98  --inst_sos_phase                        true
% 3.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel_side                     num_symb
% 3.83/0.98  --inst_solver_per_active                1400
% 3.83/0.98  --inst_solver_calls_frac                1.
% 3.83/0.98  --inst_passive_queue_type               priority_queues
% 3.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.98  --inst_passive_queues_freq              [25;2]
% 3.83/0.98  --inst_dismatching                      true
% 3.83/0.98  --inst_eager_unprocessed_to_passive     true
% 3.83/0.98  --inst_prop_sim_given                   true
% 3.83/0.98  --inst_prop_sim_new                     false
% 3.83/0.98  --inst_subs_new                         false
% 3.83/0.98  --inst_eq_res_simp                      false
% 3.83/0.98  --inst_subs_given                       false
% 3.83/0.98  --inst_orphan_elimination               true
% 3.83/0.98  --inst_learning_loop_flag               true
% 3.83/0.98  --inst_learning_start                   3000
% 3.83/0.98  --inst_learning_factor                  2
% 3.83/0.98  --inst_start_prop_sim_after_learn       3
% 3.83/0.98  --inst_sel_renew                        solver
% 3.83/0.98  --inst_lit_activity_flag                true
% 3.83/0.98  --inst_restr_to_given                   false
% 3.83/0.98  --inst_activity_threshold               500
% 3.83/0.98  --inst_out_proof                        true
% 3.83/0.98  
% 3.83/0.98  ------ Resolution Options
% 3.83/0.98  
% 3.83/0.98  --resolution_flag                       true
% 3.83/0.98  --res_lit_sel                           adaptive
% 3.83/0.98  --res_lit_sel_side                      none
% 3.83/0.98  --res_ordering                          kbo
% 3.83/0.98  --res_to_prop_solver                    active
% 3.83/0.98  --res_prop_simpl_new                    false
% 3.83/0.98  --res_prop_simpl_given                  true
% 3.83/0.98  --res_passive_queue_type                priority_queues
% 3.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.98  --res_passive_queues_freq               [15;5]
% 3.83/0.98  --res_forward_subs                      full
% 3.83/0.98  --res_backward_subs                     full
% 3.83/0.98  --res_forward_subs_resolution           true
% 3.83/0.98  --res_backward_subs_resolution          true
% 3.83/0.98  --res_orphan_elimination                true
% 3.83/0.98  --res_time_limit                        2.
% 3.83/0.98  --res_out_proof                         true
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Options
% 3.83/0.98  
% 3.83/0.98  --superposition_flag                    true
% 3.83/0.98  --sup_passive_queue_type                priority_queues
% 3.83/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.83/0.98  --demod_completeness_check              fast
% 3.83/0.98  --demod_use_ground                      true
% 3.83/0.98  --sup_to_prop_solver                    passive
% 3.83/0.98  --sup_prop_simpl_new                    true
% 3.83/0.98  --sup_prop_simpl_given                  true
% 3.83/0.98  --sup_fun_splitting                     true
% 3.83/0.98  --sup_smt_interval                      50000
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Simplification Setup
% 3.83/0.98  
% 3.83/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_immed_triv                        [TrivRules]
% 3.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_bw_main                     []
% 3.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_input_bw                          []
% 3.83/0.98  
% 3.83/0.98  ------ Combination Options
% 3.83/0.98  
% 3.83/0.98  --comb_res_mult                         3
% 3.83/0.98  --comb_sup_mult                         2
% 3.83/0.98  --comb_inst_mult                        10
% 3.83/0.98  
% 3.83/0.98  ------ Debug Options
% 3.83/0.98  
% 3.83/0.98  --dbg_backtrace                         false
% 3.83/0.98  --dbg_dump_prop_clauses                 false
% 3.83/0.98  --dbg_dump_prop_clauses_file            -
% 3.83/0.98  --dbg_out_stat                          false
% 3.83/0.98  ------ Parsing...
% 3.83/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.98  ------ Proving...
% 3.83/0.98  ------ Problem Properties 
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  clauses                                 58
% 3.83/0.98  conjectures                             3
% 3.83/0.98  EPR                                     9
% 3.83/0.98  Horn                                    43
% 3.83/0.98  unary                                   12
% 3.83/0.98  binary                                  8
% 3.83/0.98  lits                                    161
% 3.83/0.98  lits eq                                 23
% 3.83/0.98  fd_pure                                 0
% 3.83/0.98  fd_pseudo                               0
% 3.83/0.98  fd_cond                                 3
% 3.83/0.98  fd_pseudo_cond                          3
% 3.83/0.98  AC symbols                              0
% 3.83/0.98  
% 3.83/0.98  ------ Schedule dynamic 5 is on 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  Current options:
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options
% 3.83/0.98  
% 3.83/0.98  --out_options                           all
% 3.83/0.98  --tptp_safe_out                         true
% 3.83/0.98  --problem_path                          ""
% 3.83/0.98  --include_path                          ""
% 3.83/0.98  --clausifier                            res/vclausify_rel
% 3.83/0.98  --clausifier_options                    ""
% 3.83/0.98  --stdin                                 false
% 3.83/0.98  --stats_out                             all
% 3.83/0.98  
% 3.83/0.98  ------ General Options
% 3.83/0.98  
% 3.83/0.98  --fof                                   false
% 3.83/0.98  --time_out_real                         305.
% 3.83/0.98  --time_out_virtual                      -1.
% 3.83/0.98  --symbol_type_check                     false
% 3.83/0.98  --clausify_out                          false
% 3.83/0.98  --sig_cnt_out                           false
% 3.83/0.98  --trig_cnt_out                          false
% 3.83/0.98  --trig_cnt_out_tolerance                1.
% 3.83/0.98  --trig_cnt_out_sk_spl                   false
% 3.83/0.98  --abstr_cl_out                          false
% 3.83/0.98  
% 3.83/0.98  ------ Global Options
% 3.83/0.98  
% 3.83/0.98  --schedule                              default
% 3.83/0.98  --add_important_lit                     false
% 3.83/0.98  --prop_solver_per_cl                    1000
% 3.83/0.98  --min_unsat_core                        false
% 3.83/0.98  --soft_assumptions                      false
% 3.83/0.98  --soft_lemma_size                       3
% 3.83/0.98  --prop_impl_unit_size                   0
% 3.83/0.98  --prop_impl_unit                        []
% 3.83/0.98  --share_sel_clauses                     true
% 3.83/0.98  --reset_solvers                         false
% 3.83/0.98  --bc_imp_inh                            [conj_cone]
% 3.83/0.98  --conj_cone_tolerance                   3.
% 3.83/0.98  --extra_neg_conj                        none
% 3.83/0.98  --large_theory_mode                     true
% 3.83/0.98  --prolific_symb_bound                   200
% 3.83/0.98  --lt_threshold                          2000
% 3.83/0.98  --clause_weak_htbl                      true
% 3.83/0.98  --gc_record_bc_elim                     false
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing Options
% 3.83/0.98  
% 3.83/0.98  --preprocessing_flag                    true
% 3.83/0.98  --time_out_prep_mult                    0.1
% 3.83/0.98  --splitting_mode                        input
% 3.83/0.98  --splitting_grd                         true
% 3.83/0.98  --splitting_cvd                         false
% 3.83/0.98  --splitting_cvd_svl                     false
% 3.83/0.98  --splitting_nvd                         32
% 3.83/0.98  --sub_typing                            true
% 3.83/0.98  --prep_gs_sim                           true
% 3.83/0.98  --prep_unflatten                        true
% 3.83/0.98  --prep_res_sim                          true
% 3.83/0.98  --prep_upred                            true
% 3.83/0.98  --prep_sem_filter                       exhaustive
% 3.83/0.98  --prep_sem_filter_out                   false
% 3.83/0.98  --pred_elim                             true
% 3.83/0.98  --res_sim_input                         true
% 3.83/0.98  --eq_ax_congr_red                       true
% 3.83/0.98  --pure_diseq_elim                       true
% 3.83/0.98  --brand_transform                       false
% 3.83/0.98  --non_eq_to_eq                          false
% 3.83/0.98  --prep_def_merge                        true
% 3.83/0.98  --prep_def_merge_prop_impl              false
% 3.83/0.98  --prep_def_merge_mbd                    true
% 3.83/0.98  --prep_def_merge_tr_red                 false
% 3.83/0.98  --prep_def_merge_tr_cl                  false
% 3.83/0.98  --smt_preprocessing                     true
% 3.83/0.98  --smt_ac_axioms                         fast
% 3.83/0.98  --preprocessed_out                      false
% 3.83/0.98  --preprocessed_stats                    false
% 3.83/0.98  
% 3.83/0.98  ------ Abstraction refinement Options
% 3.83/0.98  
% 3.83/0.98  --abstr_ref                             []
% 3.83/0.98  --abstr_ref_prep                        false
% 3.83/0.98  --abstr_ref_until_sat                   false
% 3.83/0.98  --abstr_ref_sig_restrict                funpre
% 3.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.98  --abstr_ref_under                       []
% 3.83/0.98  
% 3.83/0.98  ------ SAT Options
% 3.83/0.98  
% 3.83/0.98  --sat_mode                              false
% 3.83/0.98  --sat_fm_restart_options                ""
% 3.83/0.98  --sat_gr_def                            false
% 3.83/0.98  --sat_epr_types                         true
% 3.83/0.98  --sat_non_cyclic_types                  false
% 3.83/0.98  --sat_finite_models                     false
% 3.83/0.98  --sat_fm_lemmas                         false
% 3.83/0.98  --sat_fm_prep                           false
% 3.83/0.98  --sat_fm_uc_incr                        true
% 3.83/0.98  --sat_out_model                         small
% 3.83/0.98  --sat_out_clauses                       false
% 3.83/0.98  
% 3.83/0.98  ------ QBF Options
% 3.83/0.98  
% 3.83/0.98  --qbf_mode                              false
% 3.83/0.98  --qbf_elim_univ                         false
% 3.83/0.98  --qbf_dom_inst                          none
% 3.83/0.98  --qbf_dom_pre_inst                      false
% 3.83/0.98  --qbf_sk_in                             false
% 3.83/0.98  --qbf_pred_elim                         true
% 3.83/0.98  --qbf_split                             512
% 3.83/0.98  
% 3.83/0.98  ------ BMC1 Options
% 3.83/0.98  
% 3.83/0.98  --bmc1_incremental                      false
% 3.83/0.98  --bmc1_axioms                           reachable_all
% 3.83/0.98  --bmc1_min_bound                        0
% 3.83/0.98  --bmc1_max_bound                        -1
% 3.83/0.98  --bmc1_max_bound_default                -1
% 3.83/0.98  --bmc1_symbol_reachability              true
% 3.83/0.98  --bmc1_property_lemmas                  false
% 3.83/0.98  --bmc1_k_induction                      false
% 3.83/0.98  --bmc1_non_equiv_states                 false
% 3.83/0.98  --bmc1_deadlock                         false
% 3.83/0.98  --bmc1_ucm                              false
% 3.83/0.98  --bmc1_add_unsat_core                   none
% 3.83/0.98  --bmc1_unsat_core_children              false
% 3.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.98  --bmc1_out_stat                         full
% 3.83/0.98  --bmc1_ground_init                      false
% 3.83/0.98  --bmc1_pre_inst_next_state              false
% 3.83/0.98  --bmc1_pre_inst_state                   false
% 3.83/0.98  --bmc1_pre_inst_reach_state             false
% 3.83/0.98  --bmc1_out_unsat_core                   false
% 3.83/0.98  --bmc1_aig_witness_out                  false
% 3.83/0.98  --bmc1_verbose                          false
% 3.83/0.98  --bmc1_dump_clauses_tptp                false
% 3.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.98  --bmc1_dump_file                        -
% 3.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.98  --bmc1_ucm_extend_mode                  1
% 3.83/0.98  --bmc1_ucm_init_mode                    2
% 3.83/0.98  --bmc1_ucm_cone_mode                    none
% 3.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.98  --bmc1_ucm_relax_model                  4
% 3.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.98  --bmc1_ucm_layered_model                none
% 3.83/0.98  --bmc1_ucm_max_lemma_size               10
% 3.83/0.98  
% 3.83/0.98  ------ AIG Options
% 3.83/0.98  
% 3.83/0.98  --aig_mode                              false
% 3.83/0.98  
% 3.83/0.98  ------ Instantiation Options
% 3.83/0.98  
% 3.83/0.98  --instantiation_flag                    true
% 3.83/0.98  --inst_sos_flag                         true
% 3.83/0.98  --inst_sos_phase                        true
% 3.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel_side                     none
% 3.83/0.98  --inst_solver_per_active                1400
% 3.83/0.98  --inst_solver_calls_frac                1.
% 3.83/0.98  --inst_passive_queue_type               priority_queues
% 3.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.98  --inst_passive_queues_freq              [25;2]
% 3.83/0.98  --inst_dismatching                      true
% 3.83/0.98  --inst_eager_unprocessed_to_passive     true
% 3.83/0.98  --inst_prop_sim_given                   true
% 3.83/0.98  --inst_prop_sim_new                     false
% 3.83/0.98  --inst_subs_new                         false
% 3.83/0.98  --inst_eq_res_simp                      false
% 3.83/0.98  --inst_subs_given                       false
% 3.83/0.98  --inst_orphan_elimination               true
% 3.83/0.98  --inst_learning_loop_flag               true
% 3.83/0.98  --inst_learning_start                   3000
% 3.83/0.98  --inst_learning_factor                  2
% 3.83/0.98  --inst_start_prop_sim_after_learn       3
% 3.83/0.98  --inst_sel_renew                        solver
% 3.83/0.98  --inst_lit_activity_flag                true
% 3.83/0.98  --inst_restr_to_given                   false
% 3.83/0.98  --inst_activity_threshold               500
% 3.83/0.98  --inst_out_proof                        true
% 3.83/0.98  
% 3.83/0.98  ------ Resolution Options
% 3.83/0.98  
% 3.83/0.98  --resolution_flag                       false
% 3.83/0.98  --res_lit_sel                           adaptive
% 3.83/0.98  --res_lit_sel_side                      none
% 3.83/0.98  --res_ordering                          kbo
% 3.83/0.98  --res_to_prop_solver                    active
% 3.83/0.98  --res_prop_simpl_new                    false
% 3.83/0.98  --res_prop_simpl_given                  true
% 3.83/0.98  --res_passive_queue_type                priority_queues
% 3.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.98  --res_passive_queues_freq               [15;5]
% 3.83/0.98  --res_forward_subs                      full
% 3.83/0.98  --res_backward_subs                     full
% 3.83/0.98  --res_forward_subs_resolution           true
% 3.83/0.98  --res_backward_subs_resolution          true
% 3.83/0.98  --res_orphan_elimination                true
% 3.83/0.98  --res_time_limit                        2.
% 3.83/0.98  --res_out_proof                         true
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Options
% 3.83/0.98  
% 3.83/0.98  --superposition_flag                    true
% 3.83/0.98  --sup_passive_queue_type                priority_queues
% 3.83/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.83/0.98  --demod_completeness_check              fast
% 3.83/0.98  --demod_use_ground                      true
% 3.83/0.98  --sup_to_prop_solver                    passive
% 3.83/0.98  --sup_prop_simpl_new                    true
% 3.83/0.98  --sup_prop_simpl_given                  true
% 3.83/0.98  --sup_fun_splitting                     true
% 3.83/0.98  --sup_smt_interval                      50000
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Simplification Setup
% 3.83/0.98  
% 3.83/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_immed_triv                        [TrivRules]
% 3.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_bw_main                     []
% 3.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_input_bw                          []
% 3.83/0.98  
% 3.83/0.98  ------ Combination Options
% 3.83/0.98  
% 3.83/0.98  --comb_res_mult                         3
% 3.83/0.98  --comb_sup_mult                         2
% 3.83/0.98  --comb_inst_mult                        10
% 3.83/0.98  
% 3.83/0.98  ------ Debug Options
% 3.83/0.98  
% 3.83/0.98  --dbg_backtrace                         false
% 3.83/0.98  --dbg_dump_prop_clauses                 false
% 3.83/0.98  --dbg_dump_prop_clauses_file            -
% 3.83/0.98  --dbg_out_stat                          false
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ Proving...
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  % SZS status Theorem for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  fof(f7,axiom,(
% 3.83/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f51,plain,(
% 3.83/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.83/0.98    inference(nnf_transformation,[],[f7])).
% 3.83/0.98  
% 3.83/0.98  fof(f52,plain,(
% 3.83/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.83/0.98    inference(flattening,[],[f51])).
% 3.83/0.98  
% 3.83/0.98  fof(f85,plain,(
% 3.83/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.83/0.98    inference(cnf_transformation,[],[f52])).
% 3.83/0.98  
% 3.83/0.98  fof(f135,plain,(
% 3.83/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.83/0.98    inference(equality_resolution,[],[f85])).
% 3.83/0.98  
% 3.83/0.98  fof(f16,axiom,(
% 3.83/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f28,plain,(
% 3.83/0.98    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.83/0.98    inference(ennf_transformation,[],[f16])).
% 3.83/0.98  
% 3.83/0.98  fof(f29,plain,(
% 3.83/0.98    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.83/0.98    inference(flattening,[],[f28])).
% 3.83/0.98  
% 3.83/0.98  fof(f124,plain,(
% 3.83/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f29])).
% 3.83/0.98  
% 3.83/0.98  fof(f3,axiom,(
% 3.83/0.98    v1_xboole_0(k1_xboole_0)),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f77,plain,(
% 3.83/0.98    v1_xboole_0(k1_xboole_0)),
% 3.83/0.98    inference(cnf_transformation,[],[f3])).
% 3.83/0.98  
% 3.83/0.98  fof(f2,axiom,(
% 3.83/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f21,plain,(
% 3.83/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.83/0.98    inference(ennf_transformation,[],[f2])).
% 3.83/0.98  
% 3.83/0.98  fof(f45,plain,(
% 3.83/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.83/0.98    inference(nnf_transformation,[],[f21])).
% 3.83/0.98  
% 3.83/0.98  fof(f46,plain,(
% 3.83/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.83/0.98    inference(rectify,[],[f45])).
% 3.83/0.98  
% 3.83/0.98  fof(f47,plain,(
% 3.83/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f48,plain,(
% 3.83/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 3.83/0.98  
% 3.83/0.98  fof(f75,plain,(
% 3.83/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f48])).
% 3.83/0.98  
% 3.83/0.98  fof(f19,conjecture,(
% 3.83/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f20,negated_conjecture,(
% 3.83/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.83/0.98    inference(negated_conjecture,[],[f19])).
% 3.83/0.98  
% 3.83/0.98  fof(f34,plain,(
% 3.83/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.83/0.98    inference(ennf_transformation,[],[f20])).
% 3.83/0.98  
% 3.83/0.98  fof(f35,plain,(
% 3.83/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.83/0.98    inference(flattening,[],[f34])).
% 3.83/0.98  
% 3.83/0.98  fof(f70,plain,(
% 3.83/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) & v1_funct_1(sK13))),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f71,plain,(
% 3.83/0.98    ~r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) & m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) & v1_funct_1(sK13)),
% 3.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f35,f70])).
% 3.83/0.98  
% 3.83/0.98  fof(f131,plain,(
% 3.83/0.98    m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))),
% 3.83/0.98    inference(cnf_transformation,[],[f71])).
% 3.83/0.98  
% 3.83/0.98  fof(f18,axiom,(
% 3.83/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f32,plain,(
% 3.83/0.98    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.83/0.98    inference(ennf_transformation,[],[f18])).
% 3.83/0.98  
% 3.83/0.98  fof(f33,plain,(
% 3.83/0.98    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.83/0.98    inference(flattening,[],[f32])).
% 3.83/0.98  
% 3.83/0.98  fof(f128,plain,(
% 3.83/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f33])).
% 3.83/0.98  
% 3.83/0.98  fof(f17,axiom,(
% 3.83/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f30,plain,(
% 3.83/0.98    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.83/0.98    inference(ennf_transformation,[],[f17])).
% 3.83/0.98  
% 3.83/0.98  fof(f31,plain,(
% 3.83/0.98    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.83/0.98    inference(flattening,[],[f30])).
% 3.83/0.98  
% 3.83/0.98  fof(f125,plain,(
% 3.83/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f31])).
% 3.83/0.98  
% 3.83/0.98  fof(f127,plain,(
% 3.83/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f33])).
% 3.83/0.98  
% 3.83/0.98  fof(f129,plain,(
% 3.83/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f33])).
% 3.83/0.98  
% 3.83/0.98  fof(f130,plain,(
% 3.83/0.98    v1_funct_1(sK13)),
% 3.83/0.98    inference(cnf_transformation,[],[f71])).
% 3.83/0.98  
% 3.83/0.98  fof(f76,plain,(
% 3.83/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f48])).
% 3.83/0.98  
% 3.83/0.98  fof(f132,plain,(
% 3.83/0.98    ~r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12))),
% 3.83/0.98    inference(cnf_transformation,[],[f71])).
% 3.83/0.98  
% 3.83/0.98  fof(f1,axiom,(
% 3.83/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f41,plain,(
% 3.83/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.83/0.98    inference(nnf_transformation,[],[f1])).
% 3.83/0.98  
% 3.83/0.98  fof(f42,plain,(
% 3.83/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.83/0.98    inference(rectify,[],[f41])).
% 3.83/0.98  
% 3.83/0.98  fof(f43,plain,(
% 3.83/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f44,plain,(
% 3.83/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 3.83/0.98  
% 3.83/0.98  fof(f72,plain,(
% 3.83/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f44])).
% 3.83/0.98  
% 3.83/0.98  fof(f8,axiom,(
% 3.83/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f53,plain,(
% 3.83/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.83/0.98    inference(nnf_transformation,[],[f8])).
% 3.83/0.98  
% 3.83/0.98  fof(f86,plain,(
% 3.83/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.83/0.98    inference(cnf_transformation,[],[f53])).
% 3.83/0.98  
% 3.83/0.98  fof(f5,axiom,(
% 3.83/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f49,plain,(
% 3.83/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.98    inference(nnf_transformation,[],[f5])).
% 3.83/0.98  
% 3.83/0.98  fof(f50,plain,(
% 3.83/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.98    inference(flattening,[],[f49])).
% 3.83/0.98  
% 3.83/0.98  fof(f81,plain,(
% 3.83/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f50])).
% 3.83/0.98  
% 3.83/0.98  fof(f87,plain,(
% 3.83/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f53])).
% 3.83/0.98  
% 3.83/0.98  fof(f83,plain,(
% 3.83/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f52])).
% 3.83/0.98  
% 3.83/0.98  fof(f84,plain,(
% 3.83/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.83/0.98    inference(cnf_transformation,[],[f52])).
% 3.83/0.98  
% 3.83/0.98  fof(f136,plain,(
% 3.83/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.83/0.98    inference(equality_resolution,[],[f84])).
% 3.83/0.98  
% 3.83/0.98  fof(f6,axiom,(
% 3.83/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f82,plain,(
% 3.83/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f6])).
% 3.83/0.98  
% 3.83/0.98  fof(f4,axiom,(
% 3.83/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f22,plain,(
% 3.83/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.83/0.98    inference(ennf_transformation,[],[f4])).
% 3.83/0.98  
% 3.83/0.98  fof(f78,plain,(
% 3.83/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f22])).
% 3.83/0.98  
% 3.83/0.98  fof(f126,plain,(
% 3.83/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f31])).
% 3.83/0.98  
% 3.83/0.98  fof(f144,plain,(
% 3.83/0.98    ( ! [X2,X1] : (r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 3.83/0.98    inference(equality_resolution,[],[f126])).
% 3.83/0.98  
% 3.83/0.98  cnf(c_11,plain,
% 3.83/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.83/0.98      inference(cnf_transformation,[],[f135]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_52,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ v1_funct_1(X0)
% 3.83/0.98      | ~ v1_xboole_0(X2)
% 3.83/0.98      | v1_xboole_0(X1)
% 3.83/0.98      | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
% 3.83/0.98      inference(cnf_transformation,[],[f124]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7367,plain,
% 3.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top
% 3.83/0.98      | v1_xboole_0(X2) != iProver_top
% 3.83/0.98      | v1_xboole_0(X1) = iProver_top
% 3.83/0.98      | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_12633,plain,
% 3.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top
% 3.83/0.98      | v1_xboole_0(X1) = iProver_top
% 3.83/0.98      | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
% 3.83/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_11,c_7367]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_5,plain,
% 3.83/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.83/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_193,plain,
% 3.83/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17596,plain,
% 3.83/0.98      ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
% 3.83/0.98      | v1_xboole_0(X1) = iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top
% 3.83/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.83/0.98      inference(global_propositional_subsumption,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_12633,c_193]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17597,plain,
% 3.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.83/0.98      | v1_funct_1(X0) != iProver_top
% 3.83/0.98      | v1_xboole_0(X1) = iProver_top
% 3.83/0.98      | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top ),
% 3.83/0.98      inference(renaming,[status(thm)],[c_17596]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_3,plain,
% 3.83/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0) ),
% 3.83/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7406,plain,
% 3.83/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.83/0.98      | r2_hidden(sK4(X0,X1),X0) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_59,negated_conjecture,
% 3.83/0.98      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) ),
% 3.83/0.98      inference(cnf_transformation,[],[f131]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7363,plain,
% 3.83/0.98      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_56,plain,
% 3.83/0.98      ( v1_funct_2(X0,X1,X2)
% 3.83/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 3.83/0.98      | ~ v1_funct_1(X3) ),
% 3.83/0.98      inference(cnf_transformation,[],[f128]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_54,plain,
% 3.83/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.83/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | r2_hidden(X0,k1_funct_2(X1,X2))
% 3.83/0.98      | ~ v1_funct_1(X0)
% 3.83/0.98      | k1_xboole_0 = X2 ),
% 3.83/0.98      inference(cnf_transformation,[],[f125]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_775,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.83/0.98      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.83/0.98      | ~ v1_funct_1(X0)
% 3.83/0.98      | ~ v1_funct_1(X3)
% 3.83/0.98      | k1_xboole_0 = X2 ),
% 3.83/0.98      inference(resolution,[status(thm)],[c_56,c_54]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_57,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.83/0.98      | ~ v1_funct_1(X0)
% 3.83/0.98      | v1_funct_1(X3) ),
% 3.83/0.98      inference(cnf_transformation,[],[f127]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_55,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.83/0.98      | ~ v1_funct_1(X0) ),
% 3.83/0.98      inference(cnf_transformation,[],[f129]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_779,plain,
% 3.83/0.98      ( ~ v1_funct_1(X0)
% 3.83/0.98      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.83/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.83/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | k1_xboole_0 = X2 ),
% 3.83/0.98      inference(global_propositional_subsumption,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_775,c_57,c_55]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_780,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.83/0.98      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.83/0.98      | ~ v1_funct_1(X0)
% 3.83/0.98      | k1_xboole_0 = X2 ),
% 3.83/0.98      inference(renaming,[status(thm)],[c_779]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7358,plain,
% 3.83/0.98      ( k1_xboole_0 = X0
% 3.83/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.83/0.98      | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
% 3.83/0.98      | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
% 3.83/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8502,plain,
% 3.83/0.98      ( sK12 = k1_xboole_0
% 3.83/0.98      | r2_hidden(X0,k5_partfun1(sK11,sK12,sK13)) != iProver_top
% 3.83/0.98      | r2_hidden(X0,k1_funct_2(sK11,sK12)) = iProver_top
% 3.83/0.98      | v1_funct_1(sK13) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_7363,c_7358]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_60,negated_conjecture,
% 3.83/0.98      ( v1_funct_1(sK13) ),
% 3.83/0.98      inference(cnf_transformation,[],[f130]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_61,plain,
% 3.83/0.98      ( v1_funct_1(sK13) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8678,plain,
% 3.83/0.98      ( r2_hidden(X0,k1_funct_2(sK11,sK12)) = iProver_top
% 3.83/0.98      | r2_hidden(X0,k5_partfun1(sK11,sK12,sK13)) != iProver_top
% 3.83/0.98      | sK12 = k1_xboole_0 ),
% 3.83/0.98      inference(global_propositional_subsumption,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_8502,c_61]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8679,plain,
% 3.83/0.98      ( sK12 = k1_xboole_0
% 3.83/0.98      | r2_hidden(X0,k5_partfun1(sK11,sK12,sK13)) != iProver_top
% 3.83/0.98      | r2_hidden(X0,k1_funct_2(sK11,sK12)) = iProver_top ),
% 3.83/0.98      inference(renaming,[status(thm)],[c_8678]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8685,plain,
% 3.83/0.98      ( sK12 = k1_xboole_0
% 3.83/0.98      | r1_tarski(k5_partfun1(sK11,sK12,sK13),X0) = iProver_top
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),X0),k1_funct_2(sK11,sK12)) = iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_7406,c_8679]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_2,plain,
% 3.83/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(sK4(X0,X1),X1) ),
% 3.83/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7407,plain,
% 3.83/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.83/0.98      | r2_hidden(sK4(X0,X1),X1) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9175,plain,
% 3.83/0.98      ( sK12 = k1_xboole_0
% 3.83/0.98      | r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) = iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_8685,c_7407]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_58,negated_conjecture,
% 3.83/0.98      ( ~ r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(cnf_transformation,[],[f132]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_63,plain,
% 3.83/0.98      ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9484,plain,
% 3.83/0.98      ( sK12 = k1_xboole_0 ),
% 3.83/0.98      inference(global_propositional_subsumption,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_9175,c_63]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_1,plain,
% 3.83/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.83/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7408,plain,
% 3.83/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.83/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8675,plain,
% 3.83/0.98      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_7406,c_7408]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_15,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.83/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7398,plain,
% 3.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.83/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8450,plain,
% 3.83/0.98      ( r1_tarski(sK13,k2_zfmisc_1(sK11,sK12)) = iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_7363,c_7398]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7,plain,
% 3.83/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.83/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7402,plain,
% 3.83/0.98      ( X0 = X1
% 3.83/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.83/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9342,plain,
% 3.83/0.98      ( k2_zfmisc_1(sK11,sK12) = sK13
% 3.83/0.98      | r1_tarski(k2_zfmisc_1(sK11,sK12),sK13) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_8450,c_7402]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9449,plain,
% 3.83/0.98      ( k2_zfmisc_1(sK11,sK12) = sK13
% 3.83/0.98      | v1_xboole_0(k2_zfmisc_1(sK11,sK12)) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_8675,c_9342]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9486,plain,
% 3.83/0.98      ( k2_zfmisc_1(sK11,k1_xboole_0) = sK13
% 3.83/0.98      | v1_xboole_0(k2_zfmisc_1(sK11,k1_xboole_0)) != iProver_top ),
% 3.83/0.98      inference(demodulation,[status(thm)],[c_9484,c_9449]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9496,plain,
% 3.83/0.98      ( sK13 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.83/0.98      inference(demodulation,[status(thm)],[c_9486,c_11]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9897,plain,
% 3.83/0.98      ( sK13 = k1_xboole_0 ),
% 3.83/0.98      inference(global_propositional_subsumption,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_9496,c_193]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7364,plain,
% 3.83/0.98      ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8933,plain,
% 3.83/0.98      ( v1_xboole_0(k5_partfun1(sK11,sK12,sK13)) != iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_8675,c_7364]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9489,plain,
% 3.83/0.98      ( v1_xboole_0(k5_partfun1(sK11,k1_xboole_0,sK13)) != iProver_top ),
% 3.83/0.98      inference(demodulation,[status(thm)],[c_9484,c_8933]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9901,plain,
% 3.83/0.98      ( v1_xboole_0(k5_partfun1(sK11,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.83/0.98      inference(demodulation,[status(thm)],[c_9897,c_9489]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17612,plain,
% 3.83/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.83/0.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.83/0.98      | v1_xboole_0(sK11) = iProver_top ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_17597,c_9901]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_14,plain,
% 3.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.83/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_177,plain,
% 3.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.83/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_179,plain,
% 3.83/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.83/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_177]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_13,plain,
% 3.83/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.83/0.98      | k1_xboole_0 = X0
% 3.83/0.98      | k1_xboole_0 = X1 ),
% 3.83/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_180,plain,
% 3.83/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.83/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_12,plain,
% 3.83/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.83/0.98      inference(cnf_transformation,[],[f136]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_181,plain,
% 3.83/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_10,plain,
% 3.83/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.83/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_182,plain,
% 3.83/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_184,plain,
% 3.83/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_182]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6235,plain,
% 3.83/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.83/0.98      theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8044,plain,
% 3.83/0.98      ( v1_funct_1(X0) | ~ v1_funct_1(sK13) | X0 != sK13 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6235]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8045,plain,
% 3.83/0.98      ( X0 != sK13
% 3.83/0.98      | v1_funct_1(X0) = iProver_top
% 3.83/0.98      | v1_funct_1(sK13) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_8044]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8047,plain,
% 3.83/0.98      ( k1_xboole_0 != sK13
% 3.83/0.98      | v1_funct_1(sK13) != iProver_top
% 3.83/0.98      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_8045]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6223,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8585,plain,
% 3.83/0.98      ( X0 != X1 | X0 = sK13 | sK13 != X1 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6223]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8586,plain,
% 3.83/0.98      ( sK13 != k1_xboole_0
% 3.83/0.98      | k1_xboole_0 = sK13
% 3.83/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_8585]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17770,plain,
% 3.83/0.98      ( v1_xboole_0(sK11) = iProver_top ),
% 3.83/0.98      inference(global_propositional_subsumption,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_17612,c_61,c_179,c_180,c_181,c_184,c_193,c_8047,
% 3.83/0.98                 c_8586,c_9496]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6,plain,
% 3.83/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.83/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7403,plain,
% 3.83/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.83/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_17774,plain,
% 3.83/0.98      ( sK11 = k1_xboole_0 ),
% 3.83/0.98      inference(superposition,[status(thm)],[c_17770,c_7403]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6226,plain,
% 3.83/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.83/0.98      theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_16128,plain,
% 3.83/0.98      ( ~ r1_tarski(X0,X1)
% 3.83/0.98      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 3.83/0.98      | X2 != X0
% 3.83/0.98      | k2_zfmisc_1(X3,X4) != X1 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6226]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_16130,plain,
% 3.83/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 3.83/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.83/0.98      | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.83/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_16128]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_15912,plain,
% 3.83/0.98      ( X0 != X1 | X0 = sK11 | sK11 != X1 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6223]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_15913,plain,
% 3.83/0.98      ( sK11 != k1_xboole_0
% 3.83/0.98      | k1_xboole_0 = sK11
% 3.83/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_15912]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6225,plain,
% 3.83/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.83/0.98      theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7813,plain,
% 3.83/0.98      ( ~ r2_hidden(X0,X1)
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X2)
% 3.83/0.98      | X2 != X1
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != X0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6225]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8263,plain,
% 3.83/0.98      ( ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X0)
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X1)
% 3.83/0.98      | X1 != X0
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_7813]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_11948,plain,
% 3.83/0.98      ( r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),X0)
% 3.83/0.98      | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13))
% 3.83/0.98      | X0 != k5_partfun1(sK11,sK12,sK13)
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_8263]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_14398,plain,
% 3.83/0.98      ( r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(X0,X1,X2))
% 3.83/0.98      | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13))
% 3.83/0.98      | k5_partfun1(X0,X1,X2) != k5_partfun1(sK11,sK12,sK13)
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_11948]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_14400,plain,
% 3.83/0.98      ( ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13))
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.83/0.98      | k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK11,sK12,sK13)
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_14398]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_13224,plain,
% 3.83/0.98      ( X0 != X1 | X0 = sK12 | sK12 != X1 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6223]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_13225,plain,
% 3.83/0.98      ( sK12 != k1_xboole_0
% 3.83/0.98      | k1_xboole_0 = sK12
% 3.83/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_13224]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_10514,plain,
% 3.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_10516,plain,
% 3.83/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.83/0.98      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_10514]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6237,plain,
% 3.83/0.98      ( X0 != X1
% 3.83/0.98      | X2 != X3
% 3.83/0.98      | X4 != X5
% 3.83/0.98      | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
% 3.83/0.98      theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_10096,plain,
% 3.83/0.98      ( X0 != sK13
% 3.83/0.98      | X1 != sK12
% 3.83/0.98      | X2 != sK11
% 3.83/0.98      | k5_partfun1(X2,X1,X0) = k5_partfun1(sK11,sK12,sK13) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6237]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_10097,plain,
% 3.83/0.98      ( k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(sK11,sK12,sK13)
% 3.83/0.98      | k1_xboole_0 != sK13
% 3.83/0.98      | k1_xboole_0 != sK12
% 3.83/0.98      | k1_xboole_0 != sK11 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_10096]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_53,plain,
% 3.83/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.83/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.83/0.98      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 3.83/0.98      | ~ v1_funct_1(X0) ),
% 3.83/0.98      inference(cnf_transformation,[],[f144]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_799,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 3.83/0.98      | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
% 3.83/0.98      | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
% 3.83/0.98      | ~ v1_funct_1(X0)
% 3.83/0.98      | ~ v1_funct_1(X3)
% 3.83/0.98      | X5 != X3
% 3.83/0.98      | X2 != X4
% 3.83/0.98      | k1_xboole_0 != X1 ),
% 3.83/0.98      inference(resolution_lifted,[status(thm)],[c_53,c_56]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_800,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.83/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.83/0.98      | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
% 3.83/0.98      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 3.83/0.98      | ~ v1_funct_1(X2)
% 3.83/0.98      | ~ v1_funct_1(X0) ),
% 3.83/0.98      inference(unflattening,[status(thm)],[c_799]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_816,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.83/0.98      | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
% 3.83/0.98      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
% 3.83/0.98      | ~ v1_funct_1(X0) ),
% 3.83/0.98      inference(forward_subsumption_resolution,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_800,c_57,c_55]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9533,plain,
% 3.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.83/0.98      | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(k1_xboole_0,X1,X0))
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(k1_xboole_0,X1))
% 3.83/0.98      | ~ v1_funct_1(X0) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_816]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_9535,plain,
% 3.83/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.83/0.98      | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(k1_xboole_0,k1_xboole_0))
% 3.83/0.98      | ~ v1_funct_1(k1_xboole_0) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_9533]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6236,plain,
% 3.83/0.98      ( X0 != X1 | X2 != X3 | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
% 3.83/0.98      theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8317,plain,
% 3.83/0.98      ( k1_funct_2(sK11,sK12) = k1_funct_2(X0,X1)
% 3.83/0.98      | sK12 != X1
% 3.83/0.98      | sK11 != X0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6236]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8318,plain,
% 3.83/0.98      ( k1_funct_2(sK11,sK12) = k1_funct_2(k1_xboole_0,k1_xboole_0)
% 3.83/0.98      | sK12 != k1_xboole_0
% 3.83/0.98      | sK11 != k1_xboole_0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_8317]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7498,plain,
% 3.83/0.98      ( ~ r2_hidden(X0,X1)
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
% 3.83/0.98      | k1_funct_2(sK11,sK12) != X1
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != X0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6225]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7675,plain,
% 3.83/0.98      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
% 3.83/0.98      | k1_funct_2(sK11,sK12) != k1_funct_2(X1,X2)
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != X0 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_7498]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8230,plain,
% 3.83/0.98      ( ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(X0,X1))
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
% 3.83/0.98      | k1_funct_2(sK11,sK12) != k1_funct_2(X0,X1)
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_7675]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8232,plain,
% 3.83/0.98      ( r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12))
% 3.83/0.98      | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(k1_xboole_0,k1_xboole_0))
% 3.83/0.98      | k1_funct_2(sK11,sK12) != k1_funct_2(k1_xboole_0,k1_xboole_0)
% 3.83/0.98      | sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) != sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_8230]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_6222,plain,( X0 = X0 ),theory(equality) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8109,plain,
% 3.83/0.98      ( sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) = sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_6222]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_8046,plain,
% 3.83/0.98      ( ~ v1_funct_1(sK13)
% 3.83/0.98      | v1_funct_1(k1_xboole_0)
% 3.83/0.98      | k1_xboole_0 != sK13 ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_8044]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7469,plain,
% 3.83/0.98      ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12))
% 3.83/0.98      | ~ r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k1_funct_2(sK11,sK12)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_7470,plain,
% 3.83/0.98      ( r1_tarski(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12))
% 3.83/0.98      | r2_hidden(sK4(k5_partfun1(sK11,sK12,sK13),k1_funct_2(sK11,sK12)),k5_partfun1(sK11,sK12,sK13)) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(c_183,plain,
% 3.83/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.83/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.83/0.98  
% 3.83/0.98  cnf(contradiction,plain,
% 3.83/0.98      ( $false ),
% 3.83/0.98      inference(minisat,
% 3.83/0.98                [status(thm)],
% 3.83/0.98                [c_17774,c_16130,c_15913,c_14400,c_13225,c_10516,c_10097,
% 3.83/0.98                 c_9535,c_9496,c_9175,c_8586,c_8318,c_8232,c_8109,c_8046,
% 3.83/0.98                 c_7469,c_7470,c_193,c_183,c_181,c_180,c_63,c_58,c_60]) ).
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  ------                               Statistics
% 3.83/0.98  
% 3.83/0.98  ------ General
% 3.83/0.98  
% 3.83/0.98  abstr_ref_over_cycles:                  0
% 3.83/0.98  abstr_ref_under_cycles:                 0
% 3.83/0.98  gc_basic_clause_elim:                   0
% 3.83/0.98  forced_gc_time:                         0
% 3.83/0.98  parsing_time:                           0.008
% 3.83/0.98  unif_index_cands_time:                  0.
% 3.83/0.98  unif_index_add_time:                    0.
% 3.83/0.98  orderings_time:                         0.
% 3.83/0.98  out_proof_time:                         0.019
% 3.83/0.98  total_time:                             0.413
% 3.83/0.98  num_of_symbols:                         61
% 3.83/0.98  num_of_terms:                           16067
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing
% 3.83/0.98  
% 3.83/0.98  num_of_splits:                          0
% 3.83/0.98  num_of_split_atoms:                     0
% 3.83/0.98  num_of_reused_defs:                     0
% 3.83/0.98  num_eq_ax_congr_red:                    92
% 3.83/0.98  num_of_sem_filtered_clauses:            1
% 3.83/0.98  num_of_subtypes:                        0
% 3.83/0.98  monotx_restored_types:                  0
% 3.83/0.98  sat_num_of_epr_types:                   0
% 3.83/0.98  sat_num_of_non_cyclic_types:            0
% 3.83/0.98  sat_guarded_non_collapsed_types:        0
% 3.83/0.98  num_pure_diseq_elim:                    0
% 3.83/0.98  simp_replaced_by:                       0
% 3.83/0.98  res_preprocessed:                       273
% 3.83/0.98  prep_upred:                             0
% 3.83/0.98  prep_unflattend:                        197
% 3.83/0.98  smt_new_axioms:                         0
% 3.83/0.98  pred_elim_cands:                        10
% 3.83/0.98  pred_elim:                              2
% 3.83/0.98  pred_elim_cl:                           2
% 3.83/0.98  pred_elim_cycles:                       10
% 3.83/0.98  merged_defs:                            8
% 3.83/0.98  merged_defs_ncl:                        0
% 3.83/0.98  bin_hyper_res:                          9
% 3.83/0.98  prep_cycles:                            4
% 3.83/0.98  pred_elim_time:                         0.054
% 3.83/0.98  splitting_time:                         0.
% 3.83/0.98  sem_filter_time:                        0.
% 3.83/0.98  monotx_time:                            0.
% 3.83/0.98  subtype_inf_time:                       0.
% 3.83/0.98  
% 3.83/0.98  ------ Problem properties
% 3.83/0.98  
% 3.83/0.98  clauses:                                58
% 3.83/0.98  conjectures:                            3
% 3.83/0.98  epr:                                    9
% 3.83/0.98  horn:                                   43
% 3.83/0.98  ground:                                 6
% 3.83/0.98  unary:                                  12
% 3.83/0.98  binary:                                 8
% 3.83/0.98  lits:                                   161
% 3.83/0.98  lits_eq:                                23
% 3.83/0.98  fd_pure:                                0
% 3.83/0.98  fd_pseudo:                              0
% 3.83/0.98  fd_cond:                                3
% 3.83/0.98  fd_pseudo_cond:                         3
% 3.83/0.98  ac_symbols:                             0
% 3.83/0.98  
% 3.83/0.98  ------ Propositional Solver
% 3.83/0.98  
% 3.83/0.98  prop_solver_calls:                      31
% 3.83/0.98  prop_fast_solver_calls:                 3001
% 3.83/0.98  smt_solver_calls:                       0
% 3.83/0.98  smt_fast_solver_calls:                  0
% 3.83/0.98  prop_num_of_clauses:                    6284
% 3.83/0.98  prop_preprocess_simplified:             15814
% 3.83/0.98  prop_fo_subsumed:                       18
% 3.83/0.98  prop_solver_time:                       0.
% 3.83/0.98  smt_solver_time:                        0.
% 3.83/0.98  smt_fast_solver_time:                   0.
% 3.83/0.98  prop_fast_solver_time:                  0.
% 3.83/0.98  prop_unsat_core_time:                   0.
% 3.83/0.98  
% 3.83/0.98  ------ QBF
% 3.83/0.98  
% 3.83/0.98  qbf_q_res:                              0
% 3.83/0.98  qbf_num_tautologies:                    0
% 3.83/0.98  qbf_prep_cycles:                        0
% 3.83/0.98  
% 3.83/0.98  ------ BMC1
% 3.83/0.98  
% 3.83/0.98  bmc1_current_bound:                     -1
% 3.83/0.98  bmc1_last_solved_bound:                 -1
% 3.83/0.98  bmc1_unsat_core_size:                   -1
% 3.83/0.98  bmc1_unsat_core_parents_size:           -1
% 3.83/0.98  bmc1_merge_next_fun:                    0
% 3.83/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.83/0.98  
% 3.83/0.98  ------ Instantiation
% 3.83/0.98  
% 3.83/0.98  inst_num_of_clauses:                    1184
% 3.83/0.98  inst_num_in_passive:                    322
% 3.83/0.98  inst_num_in_active:                     532
% 3.83/0.98  inst_num_in_unprocessed:                330
% 3.83/0.98  inst_num_of_loops:                      750
% 3.83/0.98  inst_num_of_learning_restarts:          0
% 3.83/0.98  inst_num_moves_active_passive:          216
% 3.83/0.98  inst_lit_activity:                      0
% 3.83/0.98  inst_lit_activity_moves:                0
% 3.83/0.98  inst_num_tautologies:                   0
% 3.83/0.98  inst_num_prop_implied:                  0
% 3.83/0.98  inst_num_existing_simplified:           0
% 3.83/0.98  inst_num_eq_res_simplified:             0
% 3.83/0.98  inst_num_child_elim:                    0
% 3.83/0.98  inst_num_of_dismatching_blockings:      654
% 3.83/0.98  inst_num_of_non_proper_insts:           1578
% 3.83/0.98  inst_num_of_duplicates:                 0
% 3.83/0.98  inst_inst_num_from_inst_to_res:         0
% 3.83/0.98  inst_dismatching_checking_time:         0.
% 3.83/0.98  
% 3.83/0.98  ------ Resolution
% 3.83/0.98  
% 3.83/0.98  res_num_of_clauses:                     0
% 3.83/0.98  res_num_in_passive:                     0
% 3.83/0.98  res_num_in_active:                      0
% 3.83/0.98  res_num_of_loops:                       277
% 3.83/0.98  res_forward_subset_subsumed:            242
% 3.83/0.98  res_backward_subset_subsumed:           0
% 3.83/0.98  res_forward_subsumed:                   0
% 3.83/0.98  res_backward_subsumed:                  0
% 3.83/0.98  res_forward_subsumption_resolution:     6
% 3.83/0.98  res_backward_subsumption_resolution:    0
% 3.83/0.98  res_clause_to_clause_subsumption:       2194
% 3.83/0.98  res_orphan_elimination:                 0
% 3.83/0.98  res_tautology_del:                      106
% 3.83/0.98  res_num_eq_res_simplified:              0
% 3.83/0.98  res_num_sel_changes:                    0
% 3.83/0.98  res_moves_from_active_to_pass:          0
% 3.83/0.98  
% 3.83/0.98  ------ Superposition
% 3.83/0.98  
% 3.83/0.98  sup_time_total:                         0.
% 3.83/0.98  sup_time_generating:                    0.
% 3.83/0.98  sup_time_sim_full:                      0.
% 3.83/0.98  sup_time_sim_immed:                     0.
% 3.83/0.98  
% 3.83/0.98  sup_num_of_clauses:                     638
% 3.83/0.98  sup_num_in_active:                      131
% 3.83/0.98  sup_num_in_passive:                     507
% 3.83/0.98  sup_num_of_loops:                       149
% 3.83/0.98  sup_fw_superposition:                   414
% 3.83/0.98  sup_bw_superposition:                   270
% 3.83/0.98  sup_immediate_simplified:               48
% 3.83/0.98  sup_given_eliminated:                   3
% 3.83/0.98  comparisons_done:                       0
% 3.83/0.98  comparisons_avoided:                    0
% 3.83/0.98  
% 3.83/0.98  ------ Simplifications
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  sim_fw_subset_subsumed:                 7
% 3.83/0.98  sim_bw_subset_subsumed:                 5
% 3.83/0.98  sim_fw_subsumed:                        16
% 3.83/0.98  sim_bw_subsumed:                        2
% 3.83/0.98  sim_fw_subsumption_res:                 0
% 3.83/0.98  sim_bw_subsumption_res:                 0
% 3.83/0.98  sim_tautology_del:                      7
% 3.83/0.98  sim_eq_tautology_del:                   10
% 3.83/0.98  sim_eq_res_simp:                        0
% 3.83/0.98  sim_fw_demodulated:                     38
% 3.83/0.98  sim_bw_demodulated:                     27
% 3.83/0.98  sim_light_normalised:                   5
% 3.83/0.98  sim_joinable_taut:                      0
% 3.83/0.98  sim_joinable_simp:                      0
% 3.83/0.98  sim_ac_normalised:                      0
% 3.83/0.98  sim_smt_subsumption:                    0
% 3.83/0.98  
%------------------------------------------------------------------------------
