%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:01 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 524 expanded)
%              Number of clauses        :   70 ( 200 expanded)
%              Number of leaves         :   15 (  88 expanded)
%              Depth                    :   22
%              Number of atoms          :  356 (1923 expanded)
%              Number of equality atoms :  177 ( 642 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f29,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
        | ~ v1_funct_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
      | ~ v1_funct_1(sK1) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_637,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_246,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_247,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK1),X1)
    | ~ r1_tarski(k1_relat_1(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_634,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_804,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_634])).

cnf(c_65,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_67,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_452,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_752,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK1),X1)
    | k2_relat_1(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_753,plain,
    ( k2_relat_1(sK1) != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_755,plain,
    ( k2_relat_1(sK1) != k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_117,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    inference(renaming,[status(thm)],[c_116])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_relat_1(sK1) != X2
    | k1_relat_1(sK1) != X1
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_117])).

cnf(c_354,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_362,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_354,c_9])).

cnf(c_630,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_742,plain,
    ( k2_relat_1(sK1) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_630])).

cnf(c_728,plain,
    ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_733,plain,
    ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_758,plain,
    ( k2_relat_1(sK1) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_733])).

cnf(c_760,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | k2_relat_1(sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_758])).

cnf(c_787,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_886,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_804,c_67,c_755,c_760,c_787])).

cnf(c_973,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_886])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_636,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_231,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_13,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X1 != X0
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_232,c_13])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_633,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_1541,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_633])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1544,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1541,c_5])).

cnf(c_1583,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_973,c_1544])).

cnf(c_1591,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_635,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1008,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_635])).

cnf(c_1148,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_973,c_1008])).

cnf(c_1537,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_636])).

cnf(c_1563,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1537,c_4])).

cnf(c_1577,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_974,plain,
    ( k2_relat_1(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_637,c_758])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_relat_1(sK1) != X1
    | k1_relat_1(sK1) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_117])).

cnf(c_338,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_631,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_687,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_631,c_5])).

cnf(c_1058,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_974,c_687])).

cnf(c_1071,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1058,c_4])).

cnf(c_874,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_875,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_874])).

cnf(c_450,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_812,plain,
    ( k1_relat_1(sK1) = k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_450])).

cnf(c_451,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_751,plain,
    ( k1_relat_1(sK1) != X0
    | k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_811,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1591,c_1577,c_1071,c_973,c_875,c_812,c_811])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.07/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.07/1.03  
% 1.07/1.03  ------  iProver source info
% 1.07/1.03  
% 1.07/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.07/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.07/1.03  git: non_committed_changes: false
% 1.07/1.03  git: last_make_outside_of_git: false
% 1.07/1.03  
% 1.07/1.03  ------ 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options
% 1.07/1.03  
% 1.07/1.03  --out_options                           all
% 1.07/1.03  --tptp_safe_out                         true
% 1.07/1.03  --problem_path                          ""
% 1.07/1.03  --include_path                          ""
% 1.07/1.03  --clausifier                            res/vclausify_rel
% 1.07/1.03  --clausifier_options                    --mode clausify
% 1.07/1.03  --stdin                                 false
% 1.07/1.03  --stats_out                             all
% 1.07/1.03  
% 1.07/1.03  ------ General Options
% 1.07/1.03  
% 1.07/1.03  --fof                                   false
% 1.07/1.03  --time_out_real                         305.
% 1.07/1.03  --time_out_virtual                      -1.
% 1.07/1.03  --symbol_type_check                     false
% 1.07/1.03  --clausify_out                          false
% 1.07/1.03  --sig_cnt_out                           false
% 1.07/1.03  --trig_cnt_out                          false
% 1.07/1.03  --trig_cnt_out_tolerance                1.
% 1.07/1.03  --trig_cnt_out_sk_spl                   false
% 1.07/1.03  --abstr_cl_out                          false
% 1.07/1.03  
% 1.07/1.03  ------ Global Options
% 1.07/1.03  
% 1.07/1.03  --schedule                              default
% 1.07/1.03  --add_important_lit                     false
% 1.07/1.03  --prop_solver_per_cl                    1000
% 1.07/1.03  --min_unsat_core                        false
% 1.07/1.03  --soft_assumptions                      false
% 1.07/1.03  --soft_lemma_size                       3
% 1.07/1.03  --prop_impl_unit_size                   0
% 1.07/1.03  --prop_impl_unit                        []
% 1.07/1.03  --share_sel_clauses                     true
% 1.07/1.03  --reset_solvers                         false
% 1.07/1.03  --bc_imp_inh                            [conj_cone]
% 1.07/1.03  --conj_cone_tolerance                   3.
% 1.07/1.03  --extra_neg_conj                        none
% 1.07/1.03  --large_theory_mode                     true
% 1.07/1.03  --prolific_symb_bound                   200
% 1.07/1.03  --lt_threshold                          2000
% 1.07/1.03  --clause_weak_htbl                      true
% 1.07/1.03  --gc_record_bc_elim                     false
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing Options
% 1.07/1.03  
% 1.07/1.03  --preprocessing_flag                    true
% 1.07/1.03  --time_out_prep_mult                    0.1
% 1.07/1.03  --splitting_mode                        input
% 1.07/1.03  --splitting_grd                         true
% 1.07/1.03  --splitting_cvd                         false
% 1.07/1.03  --splitting_cvd_svl                     false
% 1.07/1.03  --splitting_nvd                         32
% 1.07/1.03  --sub_typing                            true
% 1.07/1.03  --prep_gs_sim                           true
% 1.07/1.03  --prep_unflatten                        true
% 1.07/1.03  --prep_res_sim                          true
% 1.07/1.03  --prep_upred                            true
% 1.07/1.03  --prep_sem_filter                       exhaustive
% 1.07/1.03  --prep_sem_filter_out                   false
% 1.07/1.03  --pred_elim                             true
% 1.07/1.03  --res_sim_input                         true
% 1.07/1.03  --eq_ax_congr_red                       true
% 1.07/1.03  --pure_diseq_elim                       true
% 1.07/1.03  --brand_transform                       false
% 1.07/1.03  --non_eq_to_eq                          false
% 1.07/1.03  --prep_def_merge                        true
% 1.07/1.03  --prep_def_merge_prop_impl              false
% 1.07/1.03  --prep_def_merge_mbd                    true
% 1.07/1.03  --prep_def_merge_tr_red                 false
% 1.07/1.03  --prep_def_merge_tr_cl                  false
% 1.07/1.03  --smt_preprocessing                     true
% 1.07/1.03  --smt_ac_axioms                         fast
% 1.07/1.03  --preprocessed_out                      false
% 1.07/1.03  --preprocessed_stats                    false
% 1.07/1.03  
% 1.07/1.03  ------ Abstraction refinement Options
% 1.07/1.03  
% 1.07/1.03  --abstr_ref                             []
% 1.07/1.03  --abstr_ref_prep                        false
% 1.07/1.03  --abstr_ref_until_sat                   false
% 1.07/1.03  --abstr_ref_sig_restrict                funpre
% 1.07/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.03  --abstr_ref_under                       []
% 1.07/1.03  
% 1.07/1.03  ------ SAT Options
% 1.07/1.03  
% 1.07/1.03  --sat_mode                              false
% 1.07/1.03  --sat_fm_restart_options                ""
% 1.07/1.03  --sat_gr_def                            false
% 1.07/1.03  --sat_epr_types                         true
% 1.07/1.03  --sat_non_cyclic_types                  false
% 1.07/1.03  --sat_finite_models                     false
% 1.07/1.03  --sat_fm_lemmas                         false
% 1.07/1.03  --sat_fm_prep                           false
% 1.07/1.03  --sat_fm_uc_incr                        true
% 1.07/1.03  --sat_out_model                         small
% 1.07/1.03  --sat_out_clauses                       false
% 1.07/1.03  
% 1.07/1.03  ------ QBF Options
% 1.07/1.03  
% 1.07/1.03  --qbf_mode                              false
% 1.07/1.03  --qbf_elim_univ                         false
% 1.07/1.03  --qbf_dom_inst                          none
% 1.07/1.03  --qbf_dom_pre_inst                      false
% 1.07/1.03  --qbf_sk_in                             false
% 1.07/1.03  --qbf_pred_elim                         true
% 1.07/1.03  --qbf_split                             512
% 1.07/1.03  
% 1.07/1.03  ------ BMC1 Options
% 1.07/1.03  
% 1.07/1.03  --bmc1_incremental                      false
% 1.07/1.03  --bmc1_axioms                           reachable_all
% 1.07/1.03  --bmc1_min_bound                        0
% 1.07/1.03  --bmc1_max_bound                        -1
% 1.07/1.03  --bmc1_max_bound_default                -1
% 1.07/1.03  --bmc1_symbol_reachability              true
% 1.07/1.03  --bmc1_property_lemmas                  false
% 1.07/1.03  --bmc1_k_induction                      false
% 1.07/1.03  --bmc1_non_equiv_states                 false
% 1.07/1.03  --bmc1_deadlock                         false
% 1.07/1.03  --bmc1_ucm                              false
% 1.07/1.03  --bmc1_add_unsat_core                   none
% 1.07/1.03  --bmc1_unsat_core_children              false
% 1.07/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.03  --bmc1_out_stat                         full
% 1.07/1.03  --bmc1_ground_init                      false
% 1.07/1.03  --bmc1_pre_inst_next_state              false
% 1.07/1.03  --bmc1_pre_inst_state                   false
% 1.07/1.03  --bmc1_pre_inst_reach_state             false
% 1.07/1.03  --bmc1_out_unsat_core                   false
% 1.07/1.03  --bmc1_aig_witness_out                  false
% 1.07/1.03  --bmc1_verbose                          false
% 1.07/1.03  --bmc1_dump_clauses_tptp                false
% 1.07/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.03  --bmc1_dump_file                        -
% 1.07/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.03  --bmc1_ucm_extend_mode                  1
% 1.07/1.03  --bmc1_ucm_init_mode                    2
% 1.07/1.03  --bmc1_ucm_cone_mode                    none
% 1.07/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.03  --bmc1_ucm_relax_model                  4
% 1.07/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.03  --bmc1_ucm_layered_model                none
% 1.07/1.03  --bmc1_ucm_max_lemma_size               10
% 1.07/1.03  
% 1.07/1.03  ------ AIG Options
% 1.07/1.03  
% 1.07/1.03  --aig_mode                              false
% 1.07/1.03  
% 1.07/1.03  ------ Instantiation Options
% 1.07/1.03  
% 1.07/1.03  --instantiation_flag                    true
% 1.07/1.03  --inst_sos_flag                         false
% 1.07/1.03  --inst_sos_phase                        true
% 1.07/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel_side                     num_symb
% 1.07/1.03  --inst_solver_per_active                1400
% 1.07/1.03  --inst_solver_calls_frac                1.
% 1.07/1.03  --inst_passive_queue_type               priority_queues
% 1.07/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.03  --inst_passive_queues_freq              [25;2]
% 1.07/1.03  --inst_dismatching                      true
% 1.07/1.03  --inst_eager_unprocessed_to_passive     true
% 1.07/1.03  --inst_prop_sim_given                   true
% 1.07/1.03  --inst_prop_sim_new                     false
% 1.07/1.03  --inst_subs_new                         false
% 1.07/1.03  --inst_eq_res_simp                      false
% 1.07/1.03  --inst_subs_given                       false
% 1.07/1.03  --inst_orphan_elimination               true
% 1.07/1.03  --inst_learning_loop_flag               true
% 1.07/1.03  --inst_learning_start                   3000
% 1.07/1.03  --inst_learning_factor                  2
% 1.07/1.03  --inst_start_prop_sim_after_learn       3
% 1.07/1.03  --inst_sel_renew                        solver
% 1.07/1.03  --inst_lit_activity_flag                true
% 1.07/1.03  --inst_restr_to_given                   false
% 1.07/1.03  --inst_activity_threshold               500
% 1.07/1.03  --inst_out_proof                        true
% 1.07/1.03  
% 1.07/1.03  ------ Resolution Options
% 1.07/1.03  
% 1.07/1.03  --resolution_flag                       true
% 1.07/1.03  --res_lit_sel                           adaptive
% 1.07/1.03  --res_lit_sel_side                      none
% 1.07/1.03  --res_ordering                          kbo
% 1.07/1.03  --res_to_prop_solver                    active
% 1.07/1.03  --res_prop_simpl_new                    false
% 1.07/1.03  --res_prop_simpl_given                  true
% 1.07/1.03  --res_passive_queue_type                priority_queues
% 1.07/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.03  --res_passive_queues_freq               [15;5]
% 1.07/1.03  --res_forward_subs                      full
% 1.07/1.03  --res_backward_subs                     full
% 1.07/1.03  --res_forward_subs_resolution           true
% 1.07/1.03  --res_backward_subs_resolution          true
% 1.07/1.03  --res_orphan_elimination                true
% 1.07/1.03  --res_time_limit                        2.
% 1.07/1.03  --res_out_proof                         true
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Options
% 1.07/1.03  
% 1.07/1.03  --superposition_flag                    true
% 1.07/1.03  --sup_passive_queue_type                priority_queues
% 1.07/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.03  --demod_completeness_check              fast
% 1.07/1.03  --demod_use_ground                      true
% 1.07/1.03  --sup_to_prop_solver                    passive
% 1.07/1.03  --sup_prop_simpl_new                    true
% 1.07/1.03  --sup_prop_simpl_given                  true
% 1.07/1.03  --sup_fun_splitting                     false
% 1.07/1.03  --sup_smt_interval                      50000
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Simplification Setup
% 1.07/1.03  
% 1.07/1.03  --sup_indices_passive                   []
% 1.07/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_full_bw                           [BwDemod]
% 1.07/1.03  --sup_immed_triv                        [TrivRules]
% 1.07/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_immed_bw_main                     []
% 1.07/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  
% 1.07/1.03  ------ Combination Options
% 1.07/1.03  
% 1.07/1.03  --comb_res_mult                         3
% 1.07/1.03  --comb_sup_mult                         2
% 1.07/1.03  --comb_inst_mult                        10
% 1.07/1.03  
% 1.07/1.03  ------ Debug Options
% 1.07/1.03  
% 1.07/1.03  --dbg_backtrace                         false
% 1.07/1.03  --dbg_dump_prop_clauses                 false
% 1.07/1.03  --dbg_dump_prop_clauses_file            -
% 1.07/1.03  --dbg_out_stat                          false
% 1.07/1.03  ------ Parsing...
% 1.07/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.07/1.03  ------ Proving...
% 1.07/1.03  ------ Problem Properties 
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  clauses                                 14
% 1.07/1.03  conjectures                             0
% 1.07/1.03  EPR                                     2
% 1.07/1.03  Horn                                    13
% 1.07/1.03  unary                                   3
% 1.07/1.03  binary                                  6
% 1.07/1.03  lits                                    33
% 1.07/1.03  lits eq                                 18
% 1.07/1.03  fd_pure                                 0
% 1.07/1.03  fd_pseudo                               0
% 1.07/1.03  fd_cond                                 4
% 1.07/1.03  fd_pseudo_cond                          1
% 1.07/1.03  AC symbols                              0
% 1.07/1.03  
% 1.07/1.03  ------ Schedule dynamic 5 is on 
% 1.07/1.03  
% 1.07/1.03  ------ no conjectures: strip conj schedule 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  ------ 
% 1.07/1.03  Current options:
% 1.07/1.03  ------ 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options
% 1.07/1.03  
% 1.07/1.03  --out_options                           all
% 1.07/1.03  --tptp_safe_out                         true
% 1.07/1.03  --problem_path                          ""
% 1.07/1.03  --include_path                          ""
% 1.07/1.03  --clausifier                            res/vclausify_rel
% 1.07/1.03  --clausifier_options                    --mode clausify
% 1.07/1.03  --stdin                                 false
% 1.07/1.03  --stats_out                             all
% 1.07/1.03  
% 1.07/1.03  ------ General Options
% 1.07/1.03  
% 1.07/1.03  --fof                                   false
% 1.07/1.03  --time_out_real                         305.
% 1.07/1.03  --time_out_virtual                      -1.
% 1.07/1.03  --symbol_type_check                     false
% 1.07/1.03  --clausify_out                          false
% 1.07/1.03  --sig_cnt_out                           false
% 1.07/1.03  --trig_cnt_out                          false
% 1.07/1.03  --trig_cnt_out_tolerance                1.
% 1.07/1.03  --trig_cnt_out_sk_spl                   false
% 1.07/1.03  --abstr_cl_out                          false
% 1.07/1.03  
% 1.07/1.03  ------ Global Options
% 1.07/1.03  
% 1.07/1.03  --schedule                              default
% 1.07/1.03  --add_important_lit                     false
% 1.07/1.03  --prop_solver_per_cl                    1000
% 1.07/1.03  --min_unsat_core                        false
% 1.07/1.03  --soft_assumptions                      false
% 1.07/1.03  --soft_lemma_size                       3
% 1.07/1.03  --prop_impl_unit_size                   0
% 1.07/1.03  --prop_impl_unit                        []
% 1.07/1.03  --share_sel_clauses                     true
% 1.07/1.03  --reset_solvers                         false
% 1.07/1.03  --bc_imp_inh                            [conj_cone]
% 1.07/1.03  --conj_cone_tolerance                   3.
% 1.07/1.03  --extra_neg_conj                        none
% 1.07/1.03  --large_theory_mode                     true
% 1.07/1.03  --prolific_symb_bound                   200
% 1.07/1.03  --lt_threshold                          2000
% 1.07/1.03  --clause_weak_htbl                      true
% 1.07/1.03  --gc_record_bc_elim                     false
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing Options
% 1.07/1.03  
% 1.07/1.03  --preprocessing_flag                    true
% 1.07/1.03  --time_out_prep_mult                    0.1
% 1.07/1.03  --splitting_mode                        input
% 1.07/1.03  --splitting_grd                         true
% 1.07/1.03  --splitting_cvd                         false
% 1.07/1.03  --splitting_cvd_svl                     false
% 1.07/1.03  --splitting_nvd                         32
% 1.07/1.03  --sub_typing                            true
% 1.07/1.03  --prep_gs_sim                           true
% 1.07/1.03  --prep_unflatten                        true
% 1.07/1.03  --prep_res_sim                          true
% 1.07/1.03  --prep_upred                            true
% 1.07/1.03  --prep_sem_filter                       exhaustive
% 1.07/1.03  --prep_sem_filter_out                   false
% 1.07/1.04  --pred_elim                             true
% 1.07/1.04  --res_sim_input                         true
% 1.07/1.04  --eq_ax_congr_red                       true
% 1.07/1.04  --pure_diseq_elim                       true
% 1.07/1.04  --brand_transform                       false
% 1.07/1.04  --non_eq_to_eq                          false
% 1.07/1.04  --prep_def_merge                        true
% 1.07/1.04  --prep_def_merge_prop_impl              false
% 1.07/1.04  --prep_def_merge_mbd                    true
% 1.07/1.04  --prep_def_merge_tr_red                 false
% 1.07/1.04  --prep_def_merge_tr_cl                  false
% 1.07/1.04  --smt_preprocessing                     true
% 1.07/1.04  --smt_ac_axioms                         fast
% 1.07/1.04  --preprocessed_out                      false
% 1.07/1.04  --preprocessed_stats                    false
% 1.07/1.04  
% 1.07/1.04  ------ Abstraction refinement Options
% 1.07/1.04  
% 1.07/1.04  --abstr_ref                             []
% 1.07/1.04  --abstr_ref_prep                        false
% 1.07/1.04  --abstr_ref_until_sat                   false
% 1.07/1.04  --abstr_ref_sig_restrict                funpre
% 1.07/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.04  --abstr_ref_under                       []
% 1.07/1.04  
% 1.07/1.04  ------ SAT Options
% 1.07/1.04  
% 1.07/1.04  --sat_mode                              false
% 1.07/1.04  --sat_fm_restart_options                ""
% 1.07/1.04  --sat_gr_def                            false
% 1.07/1.04  --sat_epr_types                         true
% 1.07/1.04  --sat_non_cyclic_types                  false
% 1.07/1.04  --sat_finite_models                     false
% 1.07/1.04  --sat_fm_lemmas                         false
% 1.07/1.04  --sat_fm_prep                           false
% 1.07/1.04  --sat_fm_uc_incr                        true
% 1.07/1.04  --sat_out_model                         small
% 1.07/1.04  --sat_out_clauses                       false
% 1.07/1.04  
% 1.07/1.04  ------ QBF Options
% 1.07/1.04  
% 1.07/1.04  --qbf_mode                              false
% 1.07/1.04  --qbf_elim_univ                         false
% 1.07/1.04  --qbf_dom_inst                          none
% 1.07/1.04  --qbf_dom_pre_inst                      false
% 1.07/1.04  --qbf_sk_in                             false
% 1.07/1.04  --qbf_pred_elim                         true
% 1.07/1.04  --qbf_split                             512
% 1.07/1.04  
% 1.07/1.04  ------ BMC1 Options
% 1.07/1.04  
% 1.07/1.04  --bmc1_incremental                      false
% 1.07/1.04  --bmc1_axioms                           reachable_all
% 1.07/1.04  --bmc1_min_bound                        0
% 1.07/1.04  --bmc1_max_bound                        -1
% 1.07/1.04  --bmc1_max_bound_default                -1
% 1.07/1.04  --bmc1_symbol_reachability              true
% 1.07/1.04  --bmc1_property_lemmas                  false
% 1.07/1.04  --bmc1_k_induction                      false
% 1.07/1.04  --bmc1_non_equiv_states                 false
% 1.07/1.04  --bmc1_deadlock                         false
% 1.07/1.04  --bmc1_ucm                              false
% 1.07/1.04  --bmc1_add_unsat_core                   none
% 1.07/1.04  --bmc1_unsat_core_children              false
% 1.07/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.04  --bmc1_out_stat                         full
% 1.07/1.04  --bmc1_ground_init                      false
% 1.07/1.04  --bmc1_pre_inst_next_state              false
% 1.07/1.04  --bmc1_pre_inst_state                   false
% 1.07/1.04  --bmc1_pre_inst_reach_state             false
% 1.07/1.04  --bmc1_out_unsat_core                   false
% 1.07/1.04  --bmc1_aig_witness_out                  false
% 1.07/1.04  --bmc1_verbose                          false
% 1.07/1.04  --bmc1_dump_clauses_tptp                false
% 1.07/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.04  --bmc1_dump_file                        -
% 1.07/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.04  --bmc1_ucm_extend_mode                  1
% 1.07/1.04  --bmc1_ucm_init_mode                    2
% 1.07/1.04  --bmc1_ucm_cone_mode                    none
% 1.07/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.04  --bmc1_ucm_relax_model                  4
% 1.07/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.04  --bmc1_ucm_layered_model                none
% 1.07/1.04  --bmc1_ucm_max_lemma_size               10
% 1.07/1.04  
% 1.07/1.04  ------ AIG Options
% 1.07/1.04  
% 1.07/1.04  --aig_mode                              false
% 1.07/1.04  
% 1.07/1.04  ------ Instantiation Options
% 1.07/1.04  
% 1.07/1.04  --instantiation_flag                    true
% 1.07/1.04  --inst_sos_flag                         false
% 1.07/1.04  --inst_sos_phase                        true
% 1.07/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.04  --inst_lit_sel_side                     none
% 1.07/1.04  --inst_solver_per_active                1400
% 1.07/1.04  --inst_solver_calls_frac                1.
% 1.07/1.04  --inst_passive_queue_type               priority_queues
% 1.07/1.04  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.07/1.04  --inst_passive_queues_freq              [25;2]
% 1.07/1.04  --inst_dismatching                      true
% 1.07/1.04  --inst_eager_unprocessed_to_passive     true
% 1.07/1.04  --inst_prop_sim_given                   true
% 1.07/1.04  --inst_prop_sim_new                     false
% 1.07/1.04  --inst_subs_new                         false
% 1.07/1.04  --inst_eq_res_simp                      false
% 1.07/1.04  --inst_subs_given                       false
% 1.07/1.04  --inst_orphan_elimination               true
% 1.07/1.04  --inst_learning_loop_flag               true
% 1.07/1.04  --inst_learning_start                   3000
% 1.07/1.04  --inst_learning_factor                  2
% 1.07/1.04  --inst_start_prop_sim_after_learn       3
% 1.07/1.04  --inst_sel_renew                        solver
% 1.07/1.04  --inst_lit_activity_flag                true
% 1.07/1.04  --inst_restr_to_given                   false
% 1.07/1.04  --inst_activity_threshold               500
% 1.07/1.04  --inst_out_proof                        true
% 1.07/1.04  
% 1.07/1.04  ------ Resolution Options
% 1.07/1.04  
% 1.07/1.04  --resolution_flag                       false
% 1.07/1.04  --res_lit_sel                           adaptive
% 1.07/1.04  --res_lit_sel_side                      none
% 1.07/1.04  --res_ordering                          kbo
% 1.07/1.04  --res_to_prop_solver                    active
% 1.07/1.04  --res_prop_simpl_new                    false
% 1.07/1.04  --res_prop_simpl_given                  true
% 1.07/1.04  --res_passive_queue_type                priority_queues
% 1.07/1.04  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.07/1.04  --res_passive_queues_freq               [15;5]
% 1.07/1.04  --res_forward_subs                      full
% 1.07/1.04  --res_backward_subs                     full
% 1.07/1.04  --res_forward_subs_resolution           true
% 1.07/1.04  --res_backward_subs_resolution          true
% 1.07/1.04  --res_orphan_elimination                true
% 1.07/1.04  --res_time_limit                        2.
% 1.07/1.04  --res_out_proof                         true
% 1.07/1.04  
% 1.07/1.04  ------ Superposition Options
% 1.07/1.04  
% 1.07/1.04  --superposition_flag                    true
% 1.07/1.04  --sup_passive_queue_type                priority_queues
% 1.07/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.04  --demod_completeness_check              fast
% 1.07/1.04  --demod_use_ground                      true
% 1.07/1.04  --sup_to_prop_solver                    passive
% 1.07/1.04  --sup_prop_simpl_new                    true
% 1.07/1.04  --sup_prop_simpl_given                  true
% 1.07/1.04  --sup_fun_splitting                     false
% 1.07/1.04  --sup_smt_interval                      50000
% 1.07/1.04  
% 1.07/1.04  ------ Superposition Simplification Setup
% 1.07/1.04  
% 1.07/1.04  --sup_indices_passive                   []
% 1.07/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.04  --sup_full_bw                           [BwDemod]
% 1.07/1.04  --sup_immed_triv                        [TrivRules]
% 1.07/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.04  --sup_immed_bw_main                     []
% 1.07/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.04  
% 1.07/1.04  ------ Combination Options
% 1.07/1.04  
% 1.07/1.04  --comb_res_mult                         3
% 1.07/1.04  --comb_sup_mult                         2
% 1.07/1.04  --comb_inst_mult                        10
% 1.07/1.04  
% 1.07/1.04  ------ Debug Options
% 1.07/1.04  
% 1.07/1.04  --dbg_backtrace                         false
% 1.07/1.04  --dbg_dump_prop_clauses                 false
% 1.07/1.04  --dbg_dump_prop_clauses_file            -
% 1.07/1.04  --dbg_out_stat                          false
% 1.07/1.04  
% 1.07/1.04  
% 1.07/1.04  
% 1.07/1.04  
% 1.07/1.04  ------ Proving...
% 1.07/1.04  
% 1.07/1.04  
% 1.07/1.04  % SZS status Theorem for theBenchmark.p
% 1.07/1.04  
% 1.07/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.07/1.04  
% 1.07/1.04  fof(f2,axiom,(
% 1.07/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f22,plain,(
% 1.07/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.07/1.04    inference(nnf_transformation,[],[f2])).
% 1.07/1.04  
% 1.07/1.04  fof(f23,plain,(
% 1.07/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.07/1.04    inference(flattening,[],[f22])).
% 1.07/1.04  
% 1.07/1.04  fof(f32,plain,(
% 1.07/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.07/1.04    inference(cnf_transformation,[],[f23])).
% 1.07/1.04  
% 1.07/1.04  fof(f55,plain,(
% 1.07/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.07/1.04    inference(equality_resolution,[],[f32])).
% 1.07/1.04  
% 1.07/1.04  fof(f3,axiom,(
% 1.07/1.04    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f24,plain,(
% 1.07/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.07/1.04    inference(nnf_transformation,[],[f3])).
% 1.07/1.04  
% 1.07/1.04  fof(f25,plain,(
% 1.07/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.07/1.04    inference(flattening,[],[f24])).
% 1.07/1.04  
% 1.07/1.04  fof(f37,plain,(
% 1.07/1.04    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.07/1.04    inference(cnf_transformation,[],[f25])).
% 1.07/1.04  
% 1.07/1.04  fof(f56,plain,(
% 1.07/1.04    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.07/1.04    inference(equality_resolution,[],[f37])).
% 1.07/1.04  
% 1.07/1.04  fof(f7,axiom,(
% 1.07/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f15,plain,(
% 1.07/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.07/1.04    inference(ennf_transformation,[],[f7])).
% 1.07/1.04  
% 1.07/1.04  fof(f16,plain,(
% 1.07/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.07/1.04    inference(flattening,[],[f15])).
% 1.07/1.04  
% 1.07/1.04  fof(f41,plain,(
% 1.07/1.04    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.07/1.04    inference(cnf_transformation,[],[f16])).
% 1.07/1.04  
% 1.07/1.04  fof(f10,conjecture,(
% 1.07/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f11,negated_conjecture,(
% 1.07/1.04    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.07/1.04    inference(negated_conjecture,[],[f10])).
% 1.07/1.04  
% 1.07/1.04  fof(f20,plain,(
% 1.07/1.04    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.07/1.04    inference(ennf_transformation,[],[f11])).
% 1.07/1.04  
% 1.07/1.04  fof(f21,plain,(
% 1.07/1.04    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.07/1.04    inference(flattening,[],[f20])).
% 1.07/1.04  
% 1.07/1.04  fof(f29,plain,(
% 1.07/1.04    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.07/1.04    introduced(choice_axiom,[])).
% 1.07/1.04  
% 1.07/1.04  fof(f30,plain,(
% 1.07/1.04    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.07/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).
% 1.07/1.04  
% 1.07/1.04  fof(f51,plain,(
% 1.07/1.04    v1_relat_1(sK1)),
% 1.07/1.04    inference(cnf_transformation,[],[f30])).
% 1.07/1.04  
% 1.07/1.04  fof(f9,axiom,(
% 1.07/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f18,plain,(
% 1.07/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.04    inference(ennf_transformation,[],[f9])).
% 1.07/1.04  
% 1.07/1.04  fof(f19,plain,(
% 1.07/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.04    inference(flattening,[],[f18])).
% 1.07/1.04  
% 1.07/1.04  fof(f28,plain,(
% 1.07/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.04    inference(nnf_transformation,[],[f19])).
% 1.07/1.04  
% 1.07/1.04  fof(f47,plain,(
% 1.07/1.04    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.07/1.04    inference(cnf_transformation,[],[f28])).
% 1.07/1.04  
% 1.07/1.04  fof(f53,plain,(
% 1.07/1.04    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 1.07/1.04    inference(cnf_transformation,[],[f30])).
% 1.07/1.04  
% 1.07/1.04  fof(f52,plain,(
% 1.07/1.04    v1_funct_1(sK1)),
% 1.07/1.04    inference(cnf_transformation,[],[f30])).
% 1.07/1.04  
% 1.07/1.04  fof(f6,axiom,(
% 1.07/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f14,plain,(
% 1.07/1.04    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.04    inference(ennf_transformation,[],[f6])).
% 1.07/1.04  
% 1.07/1.04  fof(f40,plain,(
% 1.07/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.07/1.04    inference(cnf_transformation,[],[f14])).
% 1.07/1.04  
% 1.07/1.04  fof(f5,axiom,(
% 1.07/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f13,plain,(
% 1.07/1.04    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.07/1.04    inference(ennf_transformation,[],[f5])).
% 1.07/1.04  
% 1.07/1.04  fof(f39,plain,(
% 1.07/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.07/1.04    inference(cnf_transformation,[],[f13])).
% 1.07/1.04  
% 1.07/1.04  fof(f1,axiom,(
% 1.07/1.04    v1_xboole_0(k1_xboole_0)),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f31,plain,(
% 1.07/1.04    v1_xboole_0(k1_xboole_0)),
% 1.07/1.04    inference(cnf_transformation,[],[f1])).
% 1.07/1.04  
% 1.07/1.04  fof(f4,axiom,(
% 1.07/1.04    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f12,plain,(
% 1.07/1.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.07/1.04    inference(ennf_transformation,[],[f4])).
% 1.07/1.04  
% 1.07/1.04  fof(f38,plain,(
% 1.07/1.04    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.07/1.04    inference(cnf_transformation,[],[f12])).
% 1.07/1.04  
% 1.07/1.04  fof(f8,axiom,(
% 1.07/1.04    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.07/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.04  
% 1.07/1.04  fof(f17,plain,(
% 1.07/1.04    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.07/1.04    inference(ennf_transformation,[],[f8])).
% 1.07/1.04  
% 1.07/1.04  fof(f26,plain,(
% 1.07/1.04    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 1.07/1.04    introduced(choice_axiom,[])).
% 1.07/1.04  
% 1.07/1.04  fof(f27,plain,(
% 1.07/1.04    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 1.07/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).
% 1.07/1.04  
% 1.07/1.04  fof(f42,plain,(
% 1.07/1.04    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.07/1.04    inference(cnf_transformation,[],[f27])).
% 1.07/1.04  
% 1.07/1.04  fof(f36,plain,(
% 1.07/1.04    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.07/1.04    inference(cnf_transformation,[],[f25])).
% 1.07/1.04  
% 1.07/1.04  fof(f57,plain,(
% 1.07/1.04    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.07/1.04    inference(equality_resolution,[],[f36])).
% 1.07/1.04  
% 1.07/1.04  fof(f48,plain,(
% 1.07/1.04    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.07/1.04    inference(cnf_transformation,[],[f28])).
% 1.07/1.04  
% 1.07/1.04  fof(f61,plain,(
% 1.07/1.04    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.07/1.04    inference(equality_resolution,[],[f48])).
% 1.07/1.04  
% 1.07/1.04  cnf(c_3,plain,
% 1.07/1.04      ( r1_tarski(X0,X0) ),
% 1.07/1.04      inference(cnf_transformation,[],[f55]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_637,plain,
% 1.07/1.04      ( r1_tarski(X0,X0) = iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_4,plain,
% 1.07/1.04      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.07/1.04      inference(cnf_transformation,[],[f56]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_10,plain,
% 1.07/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.04      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.07/1.04      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.07/1.04      | ~ v1_relat_1(X0) ),
% 1.07/1.04      inference(cnf_transformation,[],[f41]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_22,negated_conjecture,
% 1.07/1.04      ( v1_relat_1(sK1) ),
% 1.07/1.04      inference(cnf_transformation,[],[f51]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_246,plain,
% 1.07/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.04      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.07/1.04      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.07/1.04      | sK1 != X0 ),
% 1.07/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_247,plain,
% 1.07/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.07/1.04      | ~ r1_tarski(k2_relat_1(sK1),X1)
% 1.07/1.04      | ~ r1_tarski(k1_relat_1(sK1),X0) ),
% 1.07/1.04      inference(unflattening,[status(thm)],[c_246]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_634,plain,
% 1.07/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 1.07/1.04      | r1_tarski(k2_relat_1(sK1),X1) != iProver_top
% 1.07/1.04      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_804,plain,
% 1.07/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.07/1.04      | r1_tarski(k2_relat_1(sK1),k1_xboole_0) != iProver_top
% 1.07/1.04      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_4,c_634]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_65,plain,
% 1.07/1.04      ( r1_tarski(X0,X0) = iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_67,plain,
% 1.07/1.04      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_65]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_452,plain,
% 1.07/1.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 1.07/1.04      theory(equality) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_752,plain,
% 1.07/1.04      ( ~ r1_tarski(X0,X1)
% 1.07/1.04      | r1_tarski(k2_relat_1(sK1),X1)
% 1.07/1.04      | k2_relat_1(sK1) != X0 ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_452]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_753,plain,
% 1.07/1.04      ( k2_relat_1(sK1) != X0
% 1.07/1.04      | r1_tarski(X0,X1) != iProver_top
% 1.07/1.04      | r1_tarski(k2_relat_1(sK1),X1) = iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_755,plain,
% 1.07/1.04      ( k2_relat_1(sK1) != k1_xboole_0
% 1.07/1.04      | r1_tarski(k2_relat_1(sK1),k1_xboole_0) = iProver_top
% 1.07/1.04      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_753]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_17,plain,
% 1.07/1.04      ( v1_funct_2(X0,X1,X2)
% 1.07/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.04      | k1_relset_1(X1,X2,X0) != X1
% 1.07/1.04      | k1_xboole_0 = X2 ),
% 1.07/1.04      inference(cnf_transformation,[],[f47]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_20,negated_conjecture,
% 1.07/1.04      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
% 1.07/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.07/1.04      | ~ v1_funct_1(sK1) ),
% 1.07/1.04      inference(cnf_transformation,[],[f53]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_21,negated_conjecture,
% 1.07/1.04      ( v1_funct_1(sK1) ),
% 1.07/1.04      inference(cnf_transformation,[],[f52]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_116,plain,
% 1.07/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.07/1.04      | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
% 1.07/1.04      inference(global_propositional_subsumption,
% 1.07/1.04                [status(thm)],
% 1.07/1.04                [c_20,c_21]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_117,negated_conjecture,
% 1.07/1.04      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
% 1.07/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
% 1.07/1.04      inference(renaming,[status(thm)],[c_116]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_353,plain,
% 1.07/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.07/1.04      | k1_relset_1(X1,X2,X0) != X1
% 1.07/1.04      | k2_relat_1(sK1) != X2
% 1.07/1.04      | k1_relat_1(sK1) != X1
% 1.07/1.04      | sK1 != X0
% 1.07/1.04      | k1_xboole_0 = X2 ),
% 1.07/1.04      inference(resolution_lifted,[status(thm)],[c_17,c_117]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_354,plain,
% 1.07/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.07/1.04      | k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) != k1_relat_1(sK1)
% 1.07/1.04      | k1_xboole_0 = k2_relat_1(sK1) ),
% 1.07/1.04      inference(unflattening,[status(thm)],[c_353]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_9,plain,
% 1.07/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.07/1.04      inference(cnf_transformation,[],[f40]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_362,plain,
% 1.07/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.07/1.04      | k1_xboole_0 = k2_relat_1(sK1) ),
% 1.07/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_354,c_9]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_630,plain,
% 1.07/1.04      ( k1_xboole_0 = k2_relat_1(sK1)
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_742,plain,
% 1.07/1.04      ( k2_relat_1(sK1) = k1_xboole_0
% 1.07/1.04      | r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) != iProver_top
% 1.07/1.04      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_634,c_630]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_728,plain,
% 1.07/1.04      ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_733,plain,
% 1.07/1.04      ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) = iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_758,plain,
% 1.07/1.04      ( k2_relat_1(sK1) = k1_xboole_0
% 1.07/1.04      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
% 1.07/1.04      inference(global_propositional_subsumption,
% 1.07/1.04                [status(thm)],
% 1.07/1.04                [c_742,c_733]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_760,plain,
% 1.07/1.04      ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
% 1.07/1.04      | k2_relat_1(sK1) = k1_xboole_0 ),
% 1.07/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_758]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_787,plain,
% 1.07/1.04      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_886,plain,
% 1.07/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.07/1.04      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 1.07/1.04      inference(global_propositional_subsumption,
% 1.07/1.04                [status(thm)],
% 1.07/1.04                [c_804,c_67,c_755,c_760,c_787]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_973,plain,
% 1.07/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_637,c_886]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_8,plain,
% 1.07/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.07/1.04      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.07/1.04      inference(cnf_transformation,[],[f39]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_636,plain,
% 1.07/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.07/1.04      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_0,plain,
% 1.07/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 1.07/1.04      inference(cnf_transformation,[],[f31]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_7,plain,
% 1.07/1.04      ( ~ r2_hidden(X0,X1)
% 1.07/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.07/1.04      | ~ v1_xboole_0(X2) ),
% 1.07/1.04      inference(cnf_transformation,[],[f38]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_231,plain,
% 1.07/1.04      ( ~ r2_hidden(X0,X1)
% 1.07/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.07/1.04      | k1_xboole_0 != X2 ),
% 1.07/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_232,plain,
% 1.07/1.04      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 1.07/1.04      inference(unflattening,[status(thm)],[c_231]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_13,plain,
% 1.07/1.04      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.07/1.04      inference(cnf_transformation,[],[f42]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_265,plain,
% 1.07/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 1.07/1.04      | X1 != X0
% 1.07/1.04      | sK0(X1) != X2
% 1.07/1.04      | k1_xboole_0 = X1 ),
% 1.07/1.04      inference(resolution_lifted,[status(thm)],[c_232,c_13]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_266,plain,
% 1.07/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 1.07/1.04      inference(unflattening,[status(thm)],[c_265]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_633,plain,
% 1.07/1.04      ( k1_xboole_0 = X0
% 1.07/1.04      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1541,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 1.07/1.04      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_636,c_633]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_5,plain,
% 1.07/1.04      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.07/1.04      inference(cnf_transformation,[],[f57]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1544,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 1.07/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(light_normalisation,[status(thm)],[c_1541,c_5]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1583,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,X0,sK1) = k1_xboole_0 ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_973,c_1544]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1591,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_1583]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_635,plain,
% 1.07/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.07/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1008,plain,
% 1.07/1.04      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 1.07/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_4,c_635]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1148,plain,
% 1.07/1.04      ( k1_relset_1(X0,k1_xboole_0,sK1) = k1_relat_1(sK1) ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_973,c_1008]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1537,plain,
% 1.07/1.04      ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X0)) = iProver_top
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_1148,c_636]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1563,plain,
% 1.07/1.04      ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X0)) = iProver_top
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(light_normalisation,[status(thm)],[c_1537,c_4]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1577,plain,
% 1.07/1.04      ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_1563]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_974,plain,
% 1.07/1.04      ( k2_relat_1(sK1) = k1_xboole_0 ),
% 1.07/1.04      inference(superposition,[status(thm)],[c_637,c_758]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_16,plain,
% 1.07/1.04      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.07/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.07/1.04      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.07/1.04      inference(cnf_transformation,[],[f61]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_337,plain,
% 1.07/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.07/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.07/1.04      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.07/1.04      | k2_relat_1(sK1) != X1
% 1.07/1.04      | k1_relat_1(sK1) != k1_xboole_0
% 1.07/1.04      | sK1 != X0 ),
% 1.07/1.04      inference(resolution_lifted,[status(thm)],[c_16,c_117]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_338,plain,
% 1.07/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
% 1.07/1.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1))))
% 1.07/1.04      | k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 1.07/1.04      | k1_relat_1(sK1) != k1_xboole_0 ),
% 1.07/1.04      inference(unflattening,[status(thm)],[c_337]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_631,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 1.07/1.04      | k1_relat_1(sK1) != k1_xboole_0
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1)))) != iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_687,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK1),sK1) != k1_xboole_0
% 1.07/1.04      | k1_relat_1(sK1) != k1_xboole_0
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) != iProver_top
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(demodulation,[status(thm)],[c_631,c_5]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1058,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.07/1.04      | k1_relat_1(sK1) != k1_xboole_0
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) != iProver_top
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(demodulation,[status(thm)],[c_974,c_687]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_1071,plain,
% 1.07/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_xboole_0
% 1.07/1.04      | k1_relat_1(sK1) != k1_xboole_0
% 1.07/1.04      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(demodulation,[status(thm)],[c_1058,c_4]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_874,plain,
% 1.07/1.04      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
% 1.07/1.04      | k1_xboole_0 = k1_relat_1(sK1) ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_266]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_875,plain,
% 1.07/1.04      ( k1_xboole_0 = k1_relat_1(sK1)
% 1.07/1.04      | m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.07/1.04      inference(predicate_to_equality,[status(thm)],[c_874]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_450,plain,( X0 = X0 ),theory(equality) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_812,plain,
% 1.07/1.04      ( k1_relat_1(sK1) = k1_relat_1(sK1) ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_450]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_451,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_751,plain,
% 1.07/1.04      ( k1_relat_1(sK1) != X0
% 1.07/1.04      | k1_relat_1(sK1) = k1_xboole_0
% 1.07/1.04      | k1_xboole_0 != X0 ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_451]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(c_811,plain,
% 1.07/1.04      ( k1_relat_1(sK1) != k1_relat_1(sK1)
% 1.07/1.04      | k1_relat_1(sK1) = k1_xboole_0
% 1.07/1.04      | k1_xboole_0 != k1_relat_1(sK1) ),
% 1.07/1.04      inference(instantiation,[status(thm)],[c_751]) ).
% 1.07/1.04  
% 1.07/1.04  cnf(contradiction,plain,
% 1.07/1.04      ( $false ),
% 1.07/1.04      inference(minisat,
% 1.07/1.04                [status(thm)],
% 1.07/1.04                [c_1591,c_1577,c_1071,c_973,c_875,c_812,c_811]) ).
% 1.07/1.04  
% 1.07/1.04  
% 1.07/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.07/1.04  
% 1.07/1.04  ------                               Statistics
% 1.07/1.04  
% 1.07/1.04  ------ General
% 1.07/1.04  
% 1.07/1.04  abstr_ref_over_cycles:                  0
% 1.07/1.04  abstr_ref_under_cycles:                 0
% 1.07/1.04  gc_basic_clause_elim:                   0
% 1.07/1.04  forced_gc_time:                         0
% 1.07/1.04  parsing_time:                           0.014
% 1.07/1.04  unif_index_cands_time:                  0.
% 1.07/1.04  unif_index_add_time:                    0.
% 1.07/1.04  orderings_time:                         0.
% 1.07/1.04  out_proof_time:                         0.012
% 1.07/1.04  total_time:                             0.147
% 1.07/1.04  num_of_symbols:                         47
% 1.07/1.04  num_of_terms:                           1577
% 1.07/1.04  
% 1.07/1.04  ------ Preprocessing
% 1.07/1.04  
% 1.07/1.04  num_of_splits:                          0
% 1.07/1.04  num_of_split_atoms:                     0
% 1.07/1.04  num_of_reused_defs:                     0
% 1.07/1.04  num_eq_ax_congr_red:                    17
% 1.07/1.04  num_of_sem_filtered_clauses:            2
% 1.07/1.04  num_of_subtypes:                        0
% 1.07/1.04  monotx_restored_types:                  0
% 1.07/1.04  sat_num_of_epr_types:                   0
% 1.07/1.04  sat_num_of_non_cyclic_types:            0
% 1.07/1.04  sat_guarded_non_collapsed_types:        0
% 1.07/1.04  num_pure_diseq_elim:                    0
% 1.07/1.04  simp_replaced_by:                       0
% 1.07/1.04  res_preprocessed:                       85
% 1.07/1.04  prep_upred:                             0
% 1.07/1.04  prep_unflattend:                        34
% 1.07/1.04  smt_new_axioms:                         0
% 1.07/1.04  pred_elim_cands:                        2
% 1.07/1.04  pred_elim:                              4
% 1.07/1.04  pred_elim_cl:                           7
% 1.07/1.04  pred_elim_cycles:                       6
% 1.07/1.04  merged_defs:                            0
% 1.07/1.04  merged_defs_ncl:                        0
% 1.07/1.04  bin_hyper_res:                          0
% 1.07/1.04  prep_cycles:                            4
% 1.07/1.04  pred_elim_time:                         0.006
% 1.07/1.04  splitting_time:                         0.
% 1.07/1.04  sem_filter_time:                        0.
% 1.07/1.04  monotx_time:                            0.
% 1.07/1.04  subtype_inf_time:                       0.
% 1.07/1.04  
% 1.07/1.04  ------ Problem properties
% 1.07/1.04  
% 1.07/1.04  clauses:                                14
% 1.07/1.04  conjectures:                            0
% 1.07/1.04  epr:                                    2
% 1.07/1.04  horn:                                   13
% 1.07/1.04  ground:                                 3
% 1.07/1.04  unary:                                  3
% 1.07/1.04  binary:                                 6
% 1.07/1.04  lits:                                   33
% 1.07/1.04  lits_eq:                                18
% 1.07/1.04  fd_pure:                                0
% 1.07/1.04  fd_pseudo:                              0
% 1.07/1.04  fd_cond:                                4
% 1.07/1.04  fd_pseudo_cond:                         1
% 1.07/1.04  ac_symbols:                             0
% 1.07/1.04  
% 1.07/1.04  ------ Propositional Solver
% 1.07/1.04  
% 1.07/1.04  prop_solver_calls:                      26
% 1.07/1.04  prop_fast_solver_calls:                 510
% 1.07/1.04  smt_solver_calls:                       0
% 1.07/1.04  smt_fast_solver_calls:                  0
% 1.07/1.04  prop_num_of_clauses:                    554
% 1.07/1.04  prop_preprocess_simplified:             2561
% 1.07/1.04  prop_fo_subsumed:                       6
% 1.07/1.04  prop_solver_time:                       0.
% 1.07/1.04  smt_solver_time:                        0.
% 1.07/1.04  smt_fast_solver_time:                   0.
% 1.07/1.04  prop_fast_solver_time:                  0.
% 1.07/1.04  prop_unsat_core_time:                   0.
% 1.07/1.04  
% 1.07/1.04  ------ QBF
% 1.07/1.04  
% 1.07/1.04  qbf_q_res:                              0
% 1.07/1.04  qbf_num_tautologies:                    0
% 1.07/1.04  qbf_prep_cycles:                        0
% 1.07/1.04  
% 1.07/1.04  ------ BMC1
% 1.07/1.04  
% 1.07/1.04  bmc1_current_bound:                     -1
% 1.07/1.04  bmc1_last_solved_bound:                 -1
% 1.07/1.04  bmc1_unsat_core_size:                   -1
% 1.07/1.04  bmc1_unsat_core_parents_size:           -1
% 1.07/1.04  bmc1_merge_next_fun:                    0
% 1.07/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.07/1.04  
% 1.07/1.04  ------ Instantiation
% 1.07/1.04  
% 1.07/1.04  inst_num_of_clauses:                    184
% 1.07/1.04  inst_num_in_passive:                    1
% 1.07/1.04  inst_num_in_active:                     106
% 1.07/1.04  inst_num_in_unprocessed:                77
% 1.07/1.04  inst_num_of_loops:                      120
% 1.07/1.04  inst_num_of_learning_restarts:          0
% 1.07/1.04  inst_num_moves_active_passive:          12
% 1.07/1.04  inst_lit_activity:                      0
% 1.07/1.04  inst_lit_activity_moves:                0
% 1.07/1.04  inst_num_tautologies:                   0
% 1.07/1.04  inst_num_prop_implied:                  0
% 1.07/1.04  inst_num_existing_simplified:           0
% 1.07/1.04  inst_num_eq_res_simplified:             0
% 1.07/1.04  inst_num_child_elim:                    0
% 1.07/1.04  inst_num_of_dismatching_blockings:      8
% 1.07/1.04  inst_num_of_non_proper_insts:           148
% 1.07/1.04  inst_num_of_duplicates:                 0
% 1.07/1.04  inst_inst_num_from_inst_to_res:         0
% 1.07/1.04  inst_dismatching_checking_time:         0.
% 1.07/1.04  
% 1.07/1.04  ------ Resolution
% 1.07/1.04  
% 1.07/1.04  res_num_of_clauses:                     0
% 1.07/1.04  res_num_in_passive:                     0
% 1.07/1.04  res_num_in_active:                      0
% 1.07/1.04  res_num_of_loops:                       89
% 1.07/1.04  res_forward_subset_subsumed:            17
% 1.07/1.04  res_backward_subset_subsumed:           0
% 1.07/1.04  res_forward_subsumed:                   0
% 1.07/1.04  res_backward_subsumed:                  0
% 1.07/1.04  res_forward_subsumption_resolution:     1
% 1.07/1.04  res_backward_subsumption_resolution:    0
% 1.07/1.04  res_clause_to_clause_subsumption:       82
% 1.07/1.04  res_orphan_elimination:                 0
% 1.07/1.04  res_tautology_del:                      34
% 1.07/1.04  res_num_eq_res_simplified:              0
% 1.07/1.04  res_num_sel_changes:                    0
% 1.07/1.04  res_moves_from_active_to_pass:          0
% 1.07/1.04  
% 1.07/1.04  ------ Superposition
% 1.07/1.04  
% 1.07/1.04  sup_time_total:                         0.
% 1.07/1.04  sup_time_generating:                    0.
% 1.07/1.04  sup_time_sim_full:                      0.
% 1.07/1.04  sup_time_sim_immed:                     0.
% 1.07/1.04  
% 1.07/1.04  sup_num_of_clauses:                     30
% 1.07/1.04  sup_num_in_active:                      18
% 1.07/1.04  sup_num_in_passive:                     12
% 1.07/1.04  sup_num_of_loops:                       23
% 1.07/1.04  sup_fw_superposition:                   17
% 1.07/1.04  sup_bw_superposition:                   10
% 1.07/1.04  sup_immediate_simplified:               10
% 1.07/1.04  sup_given_eliminated:                   0
% 1.07/1.04  comparisons_done:                       0
% 1.07/1.04  comparisons_avoided:                    0
% 1.07/1.04  
% 1.07/1.04  ------ Simplifications
% 1.07/1.04  
% 1.07/1.04  
% 1.07/1.04  sim_fw_subset_subsumed:                 2
% 1.07/1.04  sim_bw_subset_subsumed:                 2
% 1.07/1.04  sim_fw_subsumed:                        2
% 1.07/1.04  sim_bw_subsumed:                        0
% 1.07/1.04  sim_fw_subsumption_res:                 0
% 1.07/1.04  sim_bw_subsumption_res:                 0
% 1.07/1.04  sim_tautology_del:                      0
% 1.07/1.04  sim_eq_tautology_del:                   2
% 1.07/1.04  sim_eq_res_simp:                        0
% 1.07/1.04  sim_fw_demodulated:                     6
% 1.07/1.04  sim_bw_demodulated:                     4
% 1.07/1.04  sim_light_normalised:                   3
% 1.07/1.04  sim_joinable_taut:                      0
% 1.07/1.04  sim_joinable_simp:                      0
% 1.07/1.04  sim_ac_normalised:                      0
% 1.07/1.04  sim_smt_subsumption:                    0
% 1.07/1.04  
%------------------------------------------------------------------------------
