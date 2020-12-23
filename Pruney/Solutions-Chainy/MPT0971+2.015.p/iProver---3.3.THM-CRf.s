%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:03 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 384 expanded)
%              Number of clauses        :   54 ( 117 expanded)
%              Number of leaves         :   13 (  77 expanded)
%              Depth                    :   19
%              Number of atoms          :  322 (1754 expanded)
%              Number of equality atoms :  126 ( 503 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK6,X4) != sK5
          | ~ r2_hidden(X4,sK3) )
      & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,X4) != sK5
        | ~ r2_hidden(X4,sK3) )
    & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f31])).

fof(f46,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f49,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) != sK5
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_1021,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_253,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1160,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_1215,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1021,c_18,c_253,c_1160])).

cnf(c_1216,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1215])).

cnf(c_1024,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1028,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1452,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1024,c_1028])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1029,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1855,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1029])).

cnf(c_2113,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1855,c_18])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1032,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2119,plain,
    ( m1_subset_1(X0,sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_1032])).

cnf(c_2549,plain,
    ( m1_subset_1(sK2(sK6,X0),sK3) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_2119])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1033,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2874,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2549,c_1033])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1027,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1448,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1024,c_1027])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1025,plain,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1594,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1448,c_1025])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1031,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2120,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_1031])).

cnf(c_2646,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_2120])).

cnf(c_2768,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_2646])).

cnf(c_3132,plain,
    ( r2_hidden(sK2(sK6,X0),sK3) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2874,c_2768])).

cnf(c_3133,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3132])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_266,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_1020,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_268,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_1174,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_18,c_268,c_1160])).

cnf(c_1175,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1174])).

cnf(c_1598,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_1594,c_1175])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK6,X0) != sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1026,plain,
    ( k1_funct_1(sK6,X0) != sK5
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1755,plain,
    ( r2_hidden(sK2(sK6,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1026])).

cnf(c_3140,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3133,c_1755])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3140,c_1594])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.04/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.00  
% 2.04/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.04/1.00  
% 2.04/1.00  ------  iProver source info
% 2.04/1.00  
% 2.04/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.04/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.04/1.00  git: non_committed_changes: false
% 2.04/1.00  git: last_make_outside_of_git: false
% 2.04/1.00  
% 2.04/1.00  ------ 
% 2.04/1.00  
% 2.04/1.00  ------ Input Options
% 2.04/1.00  
% 2.04/1.00  --out_options                           all
% 2.04/1.00  --tptp_safe_out                         true
% 2.04/1.00  --problem_path                          ""
% 2.04/1.00  --include_path                          ""
% 2.04/1.00  --clausifier                            res/vclausify_rel
% 2.04/1.00  --clausifier_options                    --mode clausify
% 2.04/1.00  --stdin                                 false
% 2.04/1.00  --stats_out                             all
% 2.04/1.00  
% 2.04/1.00  ------ General Options
% 2.04/1.00  
% 2.04/1.00  --fof                                   false
% 2.04/1.00  --time_out_real                         305.
% 2.04/1.00  --time_out_virtual                      -1.
% 2.04/1.00  --symbol_type_check                     false
% 2.04/1.00  --clausify_out                          false
% 2.04/1.00  --sig_cnt_out                           false
% 2.04/1.00  --trig_cnt_out                          false
% 2.04/1.00  --trig_cnt_out_tolerance                1.
% 2.04/1.00  --trig_cnt_out_sk_spl                   false
% 2.04/1.00  --abstr_cl_out                          false
% 2.04/1.00  
% 2.04/1.00  ------ Global Options
% 2.04/1.00  
% 2.04/1.00  --schedule                              default
% 2.04/1.00  --add_important_lit                     false
% 2.04/1.00  --prop_solver_per_cl                    1000
% 2.04/1.00  --min_unsat_core                        false
% 2.04/1.00  --soft_assumptions                      false
% 2.04/1.00  --soft_lemma_size                       3
% 2.04/1.00  --prop_impl_unit_size                   0
% 2.04/1.00  --prop_impl_unit                        []
% 2.04/1.00  --share_sel_clauses                     true
% 2.04/1.00  --reset_solvers                         false
% 2.04/1.00  --bc_imp_inh                            [conj_cone]
% 2.04/1.00  --conj_cone_tolerance                   3.
% 2.04/1.00  --extra_neg_conj                        none
% 2.04/1.00  --large_theory_mode                     true
% 2.04/1.00  --prolific_symb_bound                   200
% 2.04/1.00  --lt_threshold                          2000
% 2.04/1.00  --clause_weak_htbl                      true
% 2.04/1.00  --gc_record_bc_elim                     false
% 2.04/1.00  
% 2.04/1.00  ------ Preprocessing Options
% 2.04/1.00  
% 2.04/1.00  --preprocessing_flag                    true
% 2.04/1.00  --time_out_prep_mult                    0.1
% 2.04/1.00  --splitting_mode                        input
% 2.04/1.00  --splitting_grd                         true
% 2.04/1.00  --splitting_cvd                         false
% 2.04/1.00  --splitting_cvd_svl                     false
% 2.04/1.00  --splitting_nvd                         32
% 2.04/1.00  --sub_typing                            true
% 2.04/1.00  --prep_gs_sim                           true
% 2.04/1.00  --prep_unflatten                        true
% 2.04/1.00  --prep_res_sim                          true
% 2.04/1.00  --prep_upred                            true
% 2.04/1.00  --prep_sem_filter                       exhaustive
% 2.04/1.00  --prep_sem_filter_out                   false
% 2.04/1.00  --pred_elim                             true
% 2.04/1.00  --res_sim_input                         true
% 2.04/1.00  --eq_ax_congr_red                       true
% 2.04/1.00  --pure_diseq_elim                       true
% 2.04/1.00  --brand_transform                       false
% 2.04/1.00  --non_eq_to_eq                          false
% 2.04/1.00  --prep_def_merge                        true
% 2.04/1.00  --prep_def_merge_prop_impl              false
% 2.04/1.00  --prep_def_merge_mbd                    true
% 2.04/1.00  --prep_def_merge_tr_red                 false
% 2.04/1.00  --prep_def_merge_tr_cl                  false
% 2.04/1.00  --smt_preprocessing                     true
% 2.04/1.00  --smt_ac_axioms                         fast
% 2.04/1.00  --preprocessed_out                      false
% 2.04/1.00  --preprocessed_stats                    false
% 2.04/1.00  
% 2.04/1.00  ------ Abstraction refinement Options
% 2.04/1.00  
% 2.04/1.00  --abstr_ref                             []
% 2.04/1.00  --abstr_ref_prep                        false
% 2.04/1.00  --abstr_ref_until_sat                   false
% 2.04/1.00  --abstr_ref_sig_restrict                funpre
% 2.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.00  --abstr_ref_under                       []
% 2.04/1.00  
% 2.04/1.00  ------ SAT Options
% 2.04/1.00  
% 2.04/1.00  --sat_mode                              false
% 2.04/1.00  --sat_fm_restart_options                ""
% 2.04/1.00  --sat_gr_def                            false
% 2.04/1.00  --sat_epr_types                         true
% 2.04/1.00  --sat_non_cyclic_types                  false
% 2.04/1.00  --sat_finite_models                     false
% 2.04/1.00  --sat_fm_lemmas                         false
% 2.04/1.00  --sat_fm_prep                           false
% 2.04/1.00  --sat_fm_uc_incr                        true
% 2.04/1.00  --sat_out_model                         small
% 2.04/1.00  --sat_out_clauses                       false
% 2.04/1.00  
% 2.04/1.00  ------ QBF Options
% 2.04/1.00  
% 2.04/1.00  --qbf_mode                              false
% 2.04/1.00  --qbf_elim_univ                         false
% 2.04/1.00  --qbf_dom_inst                          none
% 2.04/1.00  --qbf_dom_pre_inst                      false
% 2.04/1.00  --qbf_sk_in                             false
% 2.04/1.00  --qbf_pred_elim                         true
% 2.04/1.00  --qbf_split                             512
% 2.04/1.00  
% 2.04/1.00  ------ BMC1 Options
% 2.04/1.00  
% 2.04/1.00  --bmc1_incremental                      false
% 2.04/1.00  --bmc1_axioms                           reachable_all
% 2.04/1.00  --bmc1_min_bound                        0
% 2.04/1.00  --bmc1_max_bound                        -1
% 2.04/1.00  --bmc1_max_bound_default                -1
% 2.04/1.00  --bmc1_symbol_reachability              true
% 2.04/1.00  --bmc1_property_lemmas                  false
% 2.04/1.00  --bmc1_k_induction                      false
% 2.04/1.00  --bmc1_non_equiv_states                 false
% 2.04/1.00  --bmc1_deadlock                         false
% 2.04/1.00  --bmc1_ucm                              false
% 2.04/1.00  --bmc1_add_unsat_core                   none
% 2.04/1.00  --bmc1_unsat_core_children              false
% 2.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.00  --bmc1_out_stat                         full
% 2.04/1.00  --bmc1_ground_init                      false
% 2.04/1.00  --bmc1_pre_inst_next_state              false
% 2.04/1.00  --bmc1_pre_inst_state                   false
% 2.04/1.00  --bmc1_pre_inst_reach_state             false
% 2.04/1.00  --bmc1_out_unsat_core                   false
% 2.04/1.00  --bmc1_aig_witness_out                  false
% 2.04/1.00  --bmc1_verbose                          false
% 2.04/1.00  --bmc1_dump_clauses_tptp                false
% 2.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.00  --bmc1_dump_file                        -
% 2.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.00  --bmc1_ucm_extend_mode                  1
% 2.04/1.00  --bmc1_ucm_init_mode                    2
% 2.04/1.00  --bmc1_ucm_cone_mode                    none
% 2.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.00  --bmc1_ucm_relax_model                  4
% 2.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.00  --bmc1_ucm_layered_model                none
% 2.04/1.00  --bmc1_ucm_max_lemma_size               10
% 2.04/1.00  
% 2.04/1.00  ------ AIG Options
% 2.04/1.00  
% 2.04/1.00  --aig_mode                              false
% 2.04/1.00  
% 2.04/1.00  ------ Instantiation Options
% 2.04/1.00  
% 2.04/1.00  --instantiation_flag                    true
% 2.04/1.00  --inst_sos_flag                         false
% 2.04/1.00  --inst_sos_phase                        true
% 2.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.00  --inst_lit_sel_side                     num_symb
% 2.04/1.00  --inst_solver_per_active                1400
% 2.04/1.00  --inst_solver_calls_frac                1.
% 2.04/1.00  --inst_passive_queue_type               priority_queues
% 2.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.00  --inst_passive_queues_freq              [25;2]
% 2.04/1.00  --inst_dismatching                      true
% 2.04/1.00  --inst_eager_unprocessed_to_passive     true
% 2.04/1.00  --inst_prop_sim_given                   true
% 2.04/1.00  --inst_prop_sim_new                     false
% 2.04/1.00  --inst_subs_new                         false
% 2.04/1.00  --inst_eq_res_simp                      false
% 2.04/1.00  --inst_subs_given                       false
% 2.04/1.00  --inst_orphan_elimination               true
% 2.04/1.00  --inst_learning_loop_flag               true
% 2.04/1.00  --inst_learning_start                   3000
% 2.04/1.00  --inst_learning_factor                  2
% 2.04/1.00  --inst_start_prop_sim_after_learn       3
% 2.04/1.00  --inst_sel_renew                        solver
% 2.04/1.00  --inst_lit_activity_flag                true
% 2.04/1.00  --inst_restr_to_given                   false
% 2.04/1.00  --inst_activity_threshold               500
% 2.04/1.00  --inst_out_proof                        true
% 2.04/1.00  
% 2.04/1.00  ------ Resolution Options
% 2.04/1.00  
% 2.04/1.00  --resolution_flag                       true
% 2.04/1.00  --res_lit_sel                           adaptive
% 2.04/1.00  --res_lit_sel_side                      none
% 2.04/1.00  --res_ordering                          kbo
% 2.04/1.00  --res_to_prop_solver                    active
% 2.04/1.00  --res_prop_simpl_new                    false
% 2.04/1.00  --res_prop_simpl_given                  true
% 2.04/1.00  --res_passive_queue_type                priority_queues
% 2.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.00  --res_passive_queues_freq               [15;5]
% 2.04/1.00  --res_forward_subs                      full
% 2.04/1.00  --res_backward_subs                     full
% 2.04/1.00  --res_forward_subs_resolution           true
% 2.04/1.00  --res_backward_subs_resolution          true
% 2.04/1.00  --res_orphan_elimination                true
% 2.04/1.00  --res_time_limit                        2.
% 2.04/1.00  --res_out_proof                         true
% 2.04/1.00  
% 2.04/1.00  ------ Superposition Options
% 2.04/1.00  
% 2.04/1.00  --superposition_flag                    true
% 2.04/1.00  --sup_passive_queue_type                priority_queues
% 2.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.00  --demod_completeness_check              fast
% 2.04/1.00  --demod_use_ground                      true
% 2.04/1.00  --sup_to_prop_solver                    passive
% 2.04/1.00  --sup_prop_simpl_new                    true
% 2.04/1.00  --sup_prop_simpl_given                  true
% 2.04/1.00  --sup_fun_splitting                     false
% 2.04/1.00  --sup_smt_interval                      50000
% 2.04/1.00  
% 2.04/1.00  ------ Superposition Simplification Setup
% 2.04/1.00  
% 2.04/1.00  --sup_indices_passive                   []
% 2.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.00  --sup_full_bw                           [BwDemod]
% 2.04/1.00  --sup_immed_triv                        [TrivRules]
% 2.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.00  --sup_immed_bw_main                     []
% 2.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.00  
% 2.04/1.00  ------ Combination Options
% 2.04/1.00  
% 2.04/1.00  --comb_res_mult                         3
% 2.04/1.00  --comb_sup_mult                         2
% 2.04/1.00  --comb_inst_mult                        10
% 2.04/1.00  
% 2.04/1.00  ------ Debug Options
% 2.04/1.00  
% 2.04/1.00  --dbg_backtrace                         false
% 2.04/1.00  --dbg_dump_prop_clauses                 false
% 2.04/1.00  --dbg_dump_prop_clauses_file            -
% 2.04/1.00  --dbg_out_stat                          false
% 2.04/1.00  ------ Parsing...
% 2.04/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.04/1.00  
% 2.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.04/1.00  
% 2.04/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.04/1.00  
% 2.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.04/1.00  ------ Proving...
% 2.04/1.00  ------ Problem Properties 
% 2.04/1.00  
% 2.04/1.00  
% 2.04/1.00  clauses                                 16
% 2.04/1.00  conjectures                             3
% 2.04/1.00  EPR                                     1
% 2.04/1.00  Horn                                    13
% 2.04/1.00  unary                                   2
% 2.04/1.00  binary                                  5
% 2.04/1.00  lits                                    43
% 2.04/1.00  lits eq                                 9
% 2.04/1.00  fd_pure                                 0
% 2.04/1.00  fd_pseudo                               0
% 2.04/1.00  fd_cond                                 3
% 2.04/1.00  fd_pseudo_cond                          0
% 2.04/1.00  AC symbols                              0
% 2.04/1.00  
% 2.04/1.00  ------ Schedule dynamic 5 is on 
% 2.04/1.00  
% 2.04/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.04/1.00  
% 2.04/1.00  
% 2.04/1.00  ------ 
% 2.04/1.00  Current options:
% 2.04/1.00  ------ 
% 2.04/1.00  
% 2.04/1.00  ------ Input Options
% 2.04/1.00  
% 2.04/1.00  --out_options                           all
% 2.04/1.00  --tptp_safe_out                         true
% 2.04/1.00  --problem_path                          ""
% 2.04/1.00  --include_path                          ""
% 2.04/1.00  --clausifier                            res/vclausify_rel
% 2.04/1.00  --clausifier_options                    --mode clausify
% 2.04/1.00  --stdin                                 false
% 2.04/1.00  --stats_out                             all
% 2.04/1.00  
% 2.04/1.00  ------ General Options
% 2.04/1.00  
% 2.04/1.00  --fof                                   false
% 2.04/1.00  --time_out_real                         305.
% 2.04/1.00  --time_out_virtual                      -1.
% 2.04/1.00  --symbol_type_check                     false
% 2.04/1.00  --clausify_out                          false
% 2.04/1.00  --sig_cnt_out                           false
% 2.04/1.00  --trig_cnt_out                          false
% 2.04/1.00  --trig_cnt_out_tolerance                1.
% 2.04/1.00  --trig_cnt_out_sk_spl                   false
% 2.04/1.00  --abstr_cl_out                          false
% 2.04/1.00  
% 2.04/1.00  ------ Global Options
% 2.04/1.00  
% 2.04/1.00  --schedule                              default
% 2.04/1.00  --add_important_lit                     false
% 2.04/1.00  --prop_solver_per_cl                    1000
% 2.04/1.00  --min_unsat_core                        false
% 2.04/1.00  --soft_assumptions                      false
% 2.04/1.00  --soft_lemma_size                       3
% 2.04/1.00  --prop_impl_unit_size                   0
% 2.04/1.00  --prop_impl_unit                        []
% 2.04/1.00  --share_sel_clauses                     true
% 2.04/1.00  --reset_solvers                         false
% 2.04/1.00  --bc_imp_inh                            [conj_cone]
% 2.04/1.00  --conj_cone_tolerance                   3.
% 2.04/1.00  --extra_neg_conj                        none
% 2.04/1.00  --large_theory_mode                     true
% 2.04/1.00  --prolific_symb_bound                   200
% 2.04/1.00  --lt_threshold                          2000
% 2.04/1.00  --clause_weak_htbl                      true
% 2.04/1.00  --gc_record_bc_elim                     false
% 2.04/1.00  
% 2.04/1.00  ------ Preprocessing Options
% 2.04/1.00  
% 2.04/1.00  --preprocessing_flag                    true
% 2.04/1.00  --time_out_prep_mult                    0.1
% 2.04/1.00  --splitting_mode                        input
% 2.04/1.00  --splitting_grd                         true
% 2.04/1.00  --splitting_cvd                         false
% 2.04/1.00  --splitting_cvd_svl                     false
% 2.04/1.00  --splitting_nvd                         32
% 2.04/1.00  --sub_typing                            true
% 2.04/1.00  --prep_gs_sim                           true
% 2.04/1.00  --prep_unflatten                        true
% 2.04/1.00  --prep_res_sim                          true
% 2.04/1.00  --prep_upred                            true
% 2.04/1.00  --prep_sem_filter                       exhaustive
% 2.04/1.00  --prep_sem_filter_out                   false
% 2.04/1.00  --pred_elim                             true
% 2.04/1.00  --res_sim_input                         true
% 2.04/1.00  --eq_ax_congr_red                       true
% 2.04/1.00  --pure_diseq_elim                       true
% 2.04/1.00  --brand_transform                       false
% 2.04/1.00  --non_eq_to_eq                          false
% 2.04/1.00  --prep_def_merge                        true
% 2.04/1.00  --prep_def_merge_prop_impl              false
% 2.04/1.00  --prep_def_merge_mbd                    true
% 2.04/1.00  --prep_def_merge_tr_red                 false
% 2.04/1.00  --prep_def_merge_tr_cl                  false
% 2.04/1.00  --smt_preprocessing                     true
% 2.04/1.00  --smt_ac_axioms                         fast
% 2.04/1.00  --preprocessed_out                      false
% 2.04/1.00  --preprocessed_stats                    false
% 2.04/1.00  
% 2.04/1.00  ------ Abstraction refinement Options
% 2.04/1.00  
% 2.04/1.00  --abstr_ref                             []
% 2.04/1.00  --abstr_ref_prep                        false
% 2.04/1.00  --abstr_ref_until_sat                   false
% 2.04/1.00  --abstr_ref_sig_restrict                funpre
% 2.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.00  --abstr_ref_under                       []
% 2.04/1.00  
% 2.04/1.00  ------ SAT Options
% 2.04/1.00  
% 2.04/1.00  --sat_mode                              false
% 2.04/1.00  --sat_fm_restart_options                ""
% 2.04/1.00  --sat_gr_def                            false
% 2.04/1.00  --sat_epr_types                         true
% 2.04/1.00  --sat_non_cyclic_types                  false
% 2.04/1.00  --sat_finite_models                     false
% 2.04/1.00  --sat_fm_lemmas                         false
% 2.04/1.00  --sat_fm_prep                           false
% 2.04/1.00  --sat_fm_uc_incr                        true
% 2.04/1.00  --sat_out_model                         small
% 2.04/1.00  --sat_out_clauses                       false
% 2.04/1.00  
% 2.04/1.00  ------ QBF Options
% 2.04/1.00  
% 2.04/1.00  --qbf_mode                              false
% 2.04/1.00  --qbf_elim_univ                         false
% 2.04/1.00  --qbf_dom_inst                          none
% 2.04/1.00  --qbf_dom_pre_inst                      false
% 2.04/1.00  --qbf_sk_in                             false
% 2.04/1.00  --qbf_pred_elim                         true
% 2.04/1.00  --qbf_split                             512
% 2.04/1.00  
% 2.04/1.00  ------ BMC1 Options
% 2.04/1.00  
% 2.04/1.00  --bmc1_incremental                      false
% 2.04/1.00  --bmc1_axioms                           reachable_all
% 2.04/1.00  --bmc1_min_bound                        0
% 2.04/1.00  --bmc1_max_bound                        -1
% 2.04/1.00  --bmc1_max_bound_default                -1
% 2.04/1.00  --bmc1_symbol_reachability              true
% 2.04/1.00  --bmc1_property_lemmas                  false
% 2.04/1.00  --bmc1_k_induction                      false
% 2.04/1.00  --bmc1_non_equiv_states                 false
% 2.04/1.00  --bmc1_deadlock                         false
% 2.04/1.00  --bmc1_ucm                              false
% 2.04/1.00  --bmc1_add_unsat_core                   none
% 2.04/1.00  --bmc1_unsat_core_children              false
% 2.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.00  --bmc1_out_stat                         full
% 2.04/1.00  --bmc1_ground_init                      false
% 2.04/1.00  --bmc1_pre_inst_next_state              false
% 2.04/1.00  --bmc1_pre_inst_state                   false
% 2.04/1.00  --bmc1_pre_inst_reach_state             false
% 2.04/1.00  --bmc1_out_unsat_core                   false
% 2.04/1.00  --bmc1_aig_witness_out                  false
% 2.04/1.00  --bmc1_verbose                          false
% 2.04/1.00  --bmc1_dump_clauses_tptp                false
% 2.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.00  --bmc1_dump_file                        -
% 2.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.00  --bmc1_ucm_extend_mode                  1
% 2.04/1.00  --bmc1_ucm_init_mode                    2
% 2.04/1.00  --bmc1_ucm_cone_mode                    none
% 2.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.00  --bmc1_ucm_relax_model                  4
% 2.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.00  --bmc1_ucm_layered_model                none
% 2.04/1.00  --bmc1_ucm_max_lemma_size               10
% 2.04/1.00  
% 2.04/1.00  ------ AIG Options
% 2.04/1.00  
% 2.04/1.00  --aig_mode                              false
% 2.04/1.00  
% 2.04/1.00  ------ Instantiation Options
% 2.04/1.00  
% 2.04/1.00  --instantiation_flag                    true
% 2.04/1.00  --inst_sos_flag                         false
% 2.04/1.00  --inst_sos_phase                        true
% 2.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.00  --inst_lit_sel_side                     none
% 2.04/1.00  --inst_solver_per_active                1400
% 2.04/1.00  --inst_solver_calls_frac                1.
% 2.04/1.00  --inst_passive_queue_type               priority_queues
% 2.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.00  --inst_passive_queues_freq              [25;2]
% 2.04/1.00  --inst_dismatching                      true
% 2.04/1.00  --inst_eager_unprocessed_to_passive     true
% 2.04/1.00  --inst_prop_sim_given                   true
% 2.04/1.00  --inst_prop_sim_new                     false
% 2.04/1.00  --inst_subs_new                         false
% 2.04/1.00  --inst_eq_res_simp                      false
% 2.04/1.00  --inst_subs_given                       false
% 2.04/1.00  --inst_orphan_elimination               true
% 2.04/1.00  --inst_learning_loop_flag               true
% 2.04/1.00  --inst_learning_start                   3000
% 2.04/1.00  --inst_learning_factor                  2
% 2.04/1.00  --inst_start_prop_sim_after_learn       3
% 2.04/1.00  --inst_sel_renew                        solver
% 2.04/1.00  --inst_lit_activity_flag                true
% 2.04/1.00  --inst_restr_to_given                   false
% 2.04/1.00  --inst_activity_threshold               500
% 2.04/1.00  --inst_out_proof                        true
% 2.04/1.00  
% 2.04/1.00  ------ Resolution Options
% 2.04/1.00  
% 2.04/1.00  --resolution_flag                       false
% 2.04/1.00  --res_lit_sel                           adaptive
% 2.04/1.00  --res_lit_sel_side                      none
% 2.04/1.00  --res_ordering                          kbo
% 2.04/1.00  --res_to_prop_solver                    active
% 2.04/1.00  --res_prop_simpl_new                    false
% 2.04/1.00  --res_prop_simpl_given                  true
% 2.04/1.00  --res_passive_queue_type                priority_queues
% 2.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.00  --res_passive_queues_freq               [15;5]
% 2.04/1.00  --res_forward_subs                      full
% 2.04/1.00  --res_backward_subs                     full
% 2.04/1.00  --res_forward_subs_resolution           true
% 2.04/1.00  --res_backward_subs_resolution          true
% 2.04/1.00  --res_orphan_elimination                true
% 2.04/1.00  --res_time_limit                        2.
% 2.04/1.00  --res_out_proof                         true
% 2.04/1.00  
% 2.04/1.00  ------ Superposition Options
% 2.04/1.00  
% 2.04/1.00  --superposition_flag                    true
% 2.04/1.00  --sup_passive_queue_type                priority_queues
% 2.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.00  --demod_completeness_check              fast
% 2.04/1.00  --demod_use_ground                      true
% 2.04/1.00  --sup_to_prop_solver                    passive
% 2.04/1.00  --sup_prop_simpl_new                    true
% 2.04/1.00  --sup_prop_simpl_given                  true
% 2.04/1.00  --sup_fun_splitting                     false
% 2.04/1.00  --sup_smt_interval                      50000
% 2.04/1.00  
% 2.04/1.00  ------ Superposition Simplification Setup
% 2.04/1.00  
% 2.04/1.00  --sup_indices_passive                   []
% 2.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.00  --sup_full_bw                           [BwDemod]
% 2.04/1.00  --sup_immed_triv                        [TrivRules]
% 2.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.00  --sup_immed_bw_main                     []
% 2.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.00  
% 2.04/1.00  ------ Combination Options
% 2.04/1.00  
% 2.04/1.00  --comb_res_mult                         3
% 2.04/1.00  --comb_sup_mult                         2
% 2.04/1.00  --comb_inst_mult                        10
% 2.04/1.00  
% 2.04/1.00  ------ Debug Options
% 2.04/1.00  
% 2.04/1.00  --dbg_backtrace                         false
% 2.04/1.00  --dbg_dump_prop_clauses                 false
% 2.04/1.00  --dbg_dump_prop_clauses_file            -
% 2.04/1.00  --dbg_out_stat                          false
% 2.04/1.00  
% 2.04/1.00  
% 2.04/1.00  
% 2.04/1.00  
% 2.04/1.00  ------ Proving...
% 2.04/1.00  
% 2.04/1.00  
% 2.04/1.00  % SZS status Theorem for theBenchmark.p
% 2.04/1.00  
% 2.04/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.04/1.00  
% 2.04/1.00  fof(f4,axiom,(
% 2.04/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f17,plain,(
% 2.04/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.04/1.00    inference(ennf_transformation,[],[f4])).
% 2.04/1.00  
% 2.04/1.00  fof(f18,plain,(
% 2.04/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.04/1.00    inference(flattening,[],[f17])).
% 2.04/1.00  
% 2.04/1.00  fof(f25,plain,(
% 2.04/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.04/1.00    inference(nnf_transformation,[],[f18])).
% 2.04/1.00  
% 2.04/1.00  fof(f26,plain,(
% 2.04/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.04/1.00    inference(rectify,[],[f25])).
% 2.04/1.00  
% 2.04/1.00  fof(f29,plain,(
% 2.04/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 2.04/1.00    introduced(choice_axiom,[])).
% 2.04/1.00  
% 2.04/1.00  fof(f28,plain,(
% 2.04/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 2.04/1.00    introduced(choice_axiom,[])).
% 2.04/1.00  
% 2.04/1.00  fof(f27,plain,(
% 2.04/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 2.04/1.00    introduced(choice_axiom,[])).
% 2.04/1.00  
% 2.04/1.00  fof(f30,plain,(
% 2.04/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 2.04/1.00  
% 2.04/1.00  fof(f36,plain,(
% 2.04/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/1.00    inference(cnf_transformation,[],[f30])).
% 2.04/1.00  
% 2.04/1.00  fof(f53,plain,(
% 2.04/1.00    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/1.00    inference(equality_resolution,[],[f36])).
% 2.04/1.00  
% 2.04/1.00  fof(f9,conjecture,(
% 2.04/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f10,negated_conjecture,(
% 2.04/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 2.04/1.00    inference(negated_conjecture,[],[f9])).
% 2.04/1.00  
% 2.04/1.00  fof(f11,plain,(
% 2.04/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 2.04/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.04/1.00  
% 2.04/1.00  fof(f23,plain,(
% 2.04/1.00    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.04/1.00    inference(ennf_transformation,[],[f11])).
% 2.04/1.00  
% 2.04/1.00  fof(f24,plain,(
% 2.04/1.00    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.04/1.00    inference(flattening,[],[f23])).
% 2.04/1.00  
% 2.04/1.00  fof(f31,plain,(
% 2.04/1.00    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 2.04/1.00    introduced(choice_axiom,[])).
% 2.04/1.00  
% 2.04/1.00  fof(f32,plain,(
% 2.04/1.00    ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 2.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f31])).
% 2.04/1.00  
% 2.04/1.00  fof(f46,plain,(
% 2.04/1.00    v1_funct_1(sK6)),
% 2.04/1.00    inference(cnf_transformation,[],[f32])).
% 2.04/1.00  
% 2.04/1.00  fof(f47,plain,(
% 2.04/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.04/1.00    inference(cnf_transformation,[],[f32])).
% 2.04/1.00  
% 2.04/1.00  fof(f5,axiom,(
% 2.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f19,plain,(
% 2.04/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.00    inference(ennf_transformation,[],[f5])).
% 2.04/1.00  
% 2.04/1.00  fof(f42,plain,(
% 2.04/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.00    inference(cnf_transformation,[],[f19])).
% 2.04/1.00  
% 2.04/1.00  fof(f7,axiom,(
% 2.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f21,plain,(
% 2.04/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.00    inference(ennf_transformation,[],[f7])).
% 2.04/1.00  
% 2.04/1.00  fof(f44,plain,(
% 2.04/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.00    inference(cnf_transformation,[],[f21])).
% 2.04/1.00  
% 2.04/1.00  fof(f6,axiom,(
% 2.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f20,plain,(
% 2.04/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.00    inference(ennf_transformation,[],[f6])).
% 2.04/1.00  
% 2.04/1.00  fof(f43,plain,(
% 2.04/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.00    inference(cnf_transformation,[],[f20])).
% 2.04/1.00  
% 2.04/1.00  fof(f2,axiom,(
% 2.04/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f14,plain,(
% 2.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.04/1.00    inference(ennf_transformation,[],[f2])).
% 2.04/1.00  
% 2.04/1.00  fof(f15,plain,(
% 2.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.04/1.00    inference(flattening,[],[f14])).
% 2.04/1.00  
% 2.04/1.00  fof(f34,plain,(
% 2.04/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.04/1.00    inference(cnf_transformation,[],[f15])).
% 2.04/1.00  
% 2.04/1.00  fof(f1,axiom,(
% 2.04/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f12,plain,(
% 2.04/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.04/1.00    inference(ennf_transformation,[],[f1])).
% 2.04/1.00  
% 2.04/1.00  fof(f13,plain,(
% 2.04/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.04/1.00    inference(flattening,[],[f12])).
% 2.04/1.00  
% 2.04/1.00  fof(f33,plain,(
% 2.04/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.04/1.00    inference(cnf_transformation,[],[f13])).
% 2.04/1.00  
% 2.04/1.00  fof(f8,axiom,(
% 2.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f22,plain,(
% 2.04/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.00    inference(ennf_transformation,[],[f8])).
% 2.04/1.00  
% 2.04/1.00  fof(f45,plain,(
% 2.04/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.00    inference(cnf_transformation,[],[f22])).
% 2.04/1.00  
% 2.04/1.00  fof(f48,plain,(
% 2.04/1.00    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))),
% 2.04/1.00    inference(cnf_transformation,[],[f32])).
% 2.04/1.00  
% 2.04/1.00  fof(f3,axiom,(
% 2.04/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.00  
% 2.04/1.00  fof(f16,plain,(
% 2.04/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.04/1.00    inference(ennf_transformation,[],[f3])).
% 2.04/1.00  
% 2.04/1.00  fof(f35,plain,(
% 2.04/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.04/1.00    inference(cnf_transformation,[],[f16])).
% 2.04/1.00  
% 2.04/1.00  fof(f37,plain,(
% 2.04/1.00    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/1.00    inference(cnf_transformation,[],[f30])).
% 2.04/1.00  
% 2.04/1.00  fof(f52,plain,(
% 2.04/1.00    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.04/1.00    inference(equality_resolution,[],[f37])).
% 2.04/1.00  
% 2.04/1.00  fof(f49,plain,(
% 2.04/1.00    ( ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) )),
% 2.04/1.00    inference(cnf_transformation,[],[f32])).
% 2.04/1.00  
% 2.04/1.00  cnf(c_8,plain,
% 2.04/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.04/1.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 2.04/1.00      | ~ v1_relat_1(X1)
% 2.04/1.00      | ~ v1_funct_1(X1) ),
% 2.04/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.04/1.00  
% 2.04/1.00  cnf(c_16,negated_conjecture,
% 2.04/1.00      ( v1_funct_1(sK6) ),
% 2.04/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.04/1.00  
% 2.04/1.00  cnf(c_251,plain,
% 2.04/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.04/1.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 2.04/1.00      | ~ v1_relat_1(X1)
% 2.04/1.00      | sK6 != X1 ),
% 2.04/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.04/1.00  
% 2.04/1.00  cnf(c_252,plain,
% 2.04/1.00      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 2.04/1.00      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 2.04/1.00      | ~ v1_relat_1(sK6) ),
% 2.04/1.00      inference(unflattening,[status(thm)],[c_251]) ).
% 2.04/1.00  
% 2.04/1.00  cnf(c_1021,plain,
% 2.04/1.00      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.00      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.04/1.00      | v1_relat_1(sK6) != iProver_top ),
% 2.04/1.00      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 2.04/1.00  
% 2.04/1.00  cnf(c_15,negated_conjecture,
% 2.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.04/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_18,plain,
% 2.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_253,plain,
% 2.04/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_9,plain,
% 2.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.01      | v1_relat_1(X0) ),
% 2.04/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1159,plain,
% 2.04/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.04/1.01      | v1_relat_1(sK6) ),
% 2.04/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1160,plain,
% 2.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.04/1.01      | v1_relat_1(sK6) = iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_1159]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1215,plain,
% 2.04/1.01      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.04/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 2.04/1.01      inference(global_propositional_subsumption,
% 2.04/1.01                [status(thm)],
% 2.04/1.01                [c_1021,c_18,c_253,c_1160]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1216,plain,
% 2.04/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
% 2.04/1.01      inference(renaming,[status(thm)],[c_1215]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1024,plain,
% 2.04/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_11,plain,
% 2.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.04/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1028,plain,
% 2.04/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.04/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1452,plain,
% 2.04/1.01      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1024,c_1028]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_10,plain,
% 2.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.01      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.04/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1029,plain,
% 2.04/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.04/1.01      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1855,plain,
% 2.04/1.01      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top
% 2.04/1.01      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1452,c_1029]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2113,plain,
% 2.04/1.01      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.04/1.01      inference(global_propositional_subsumption,
% 2.04/1.01                [status(thm)],
% 2.04/1.01                [c_1855,c_18]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1,plain,
% 2.04/1.01      ( m1_subset_1(X0,X1)
% 2.04/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.04/1.01      | ~ r2_hidden(X0,X2) ),
% 2.04/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1032,plain,
% 2.04/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.04/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.04/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2119,plain,
% 2.04/1.01      ( m1_subset_1(X0,sK3) = iProver_top
% 2.04/1.01      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_2113,c_1032]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2549,plain,
% 2.04/1.01      ( m1_subset_1(sK2(sK6,X0),sK3) = iProver_top
% 2.04/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1216,c_2119]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_0,plain,
% 2.04/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.04/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1033,plain,
% 2.04/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.04/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.04/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2874,plain,
% 2.04/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | r2_hidden(sK2(sK6,X0),sK3) = iProver_top
% 2.04/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_2549,c_1033]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_12,plain,
% 2.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.04/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1027,plain,
% 2.04/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.04/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1448,plain,
% 2.04/1.01      ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1024,c_1027]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_14,negated_conjecture,
% 2.04/1.01      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
% 2.04/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1025,plain,
% 2.04/1.01      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1594,plain,
% 2.04/1.01      ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
% 2.04/1.01      inference(demodulation,[status(thm)],[c_1448,c_1025]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2,plain,
% 2.04/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.04/1.01      | ~ r2_hidden(X2,X0)
% 2.04/1.01      | ~ v1_xboole_0(X1) ),
% 2.04/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1031,plain,
% 2.04/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.04/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.04/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2120,plain,
% 2.04/1.01      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.04/1.01      | v1_xboole_0(sK3) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_2113,c_1031]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2646,plain,
% 2.04/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | v1_xboole_0(sK3) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1216,c_2120]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_2768,plain,
% 2.04/1.01      ( v1_xboole_0(sK3) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1594,c_2646]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_3132,plain,
% 2.04/1.01      ( r2_hidden(sK2(sK6,X0),sK3) = iProver_top
% 2.04/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 2.04/1.01      inference(global_propositional_subsumption,
% 2.04/1.01                [status(thm)],
% 2.04/1.01                [c_2874,c_2768]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_3133,plain,
% 2.04/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | r2_hidden(sK2(sK6,X0),sK3) = iProver_top ),
% 2.04/1.01      inference(renaming,[status(thm)],[c_3132]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_7,plain,
% 2.04/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.04/1.01      | ~ v1_relat_1(X1)
% 2.04/1.01      | ~ v1_funct_1(X1)
% 2.04/1.01      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 2.04/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_266,plain,
% 2.04/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.04/1.01      | ~ v1_relat_1(X1)
% 2.04/1.01      | k1_funct_1(X1,sK2(X1,X0)) = X0
% 2.04/1.01      | sK6 != X1 ),
% 2.04/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_267,plain,
% 2.04/1.01      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 2.04/1.01      | ~ v1_relat_1(sK6)
% 2.04/1.01      | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
% 2.04/1.01      inference(unflattening,[status(thm)],[c_266]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1020,plain,
% 2.04/1.01      ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
% 2.04/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_268,plain,
% 2.04/1.01      ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
% 2.04/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | v1_relat_1(sK6) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1174,plain,
% 2.04/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.04/1.01      | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
% 2.04/1.01      inference(global_propositional_subsumption,
% 2.04/1.01                [status(thm)],
% 2.04/1.01                [c_1020,c_18,c_268,c_1160]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1175,plain,
% 2.04/1.01      ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
% 2.04/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 2.04/1.01      inference(renaming,[status(thm)],[c_1174]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1598,plain,
% 2.04/1.01      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1594,c_1175]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_13,negated_conjecture,
% 2.04/1.01      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK6,X0) != sK5 ),
% 2.04/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1026,plain,
% 2.04/1.01      ( k1_funct_1(sK6,X0) != sK5 | r2_hidden(X0,sK3) != iProver_top ),
% 2.04/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_1755,plain,
% 2.04/1.01      ( r2_hidden(sK2(sK6,sK5),sK3) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_1598,c_1026]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(c_3140,plain,
% 2.04/1.01      ( r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top ),
% 2.04/1.01      inference(superposition,[status(thm)],[c_3133,c_1755]) ).
% 2.04/1.01  
% 2.04/1.01  cnf(contradiction,plain,
% 2.04/1.01      ( $false ),
% 2.04/1.01      inference(minisat,[status(thm)],[c_3140,c_1594]) ).
% 2.04/1.01  
% 2.04/1.01  
% 2.04/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.04/1.01  
% 2.04/1.01  ------                               Statistics
% 2.04/1.01  
% 2.04/1.01  ------ General
% 2.04/1.01  
% 2.04/1.01  abstr_ref_over_cycles:                  0
% 2.04/1.01  abstr_ref_under_cycles:                 0
% 2.04/1.01  gc_basic_clause_elim:                   0
% 2.04/1.01  forced_gc_time:                         0
% 2.04/1.01  parsing_time:                           0.014
% 2.04/1.01  unif_index_cands_time:                  0.
% 2.04/1.01  unif_index_add_time:                    0.
% 2.04/1.01  orderings_time:                         0.
% 2.04/1.01  out_proof_time:                         0.007
% 2.04/1.01  total_time:                             0.19
% 2.04/1.01  num_of_symbols:                         50
% 2.04/1.01  num_of_terms:                           2422
% 2.04/1.01  
% 2.04/1.01  ------ Preprocessing
% 2.04/1.01  
% 2.04/1.01  num_of_splits:                          0
% 2.04/1.01  num_of_split_atoms:                     0
% 2.04/1.01  num_of_reused_defs:                     0
% 2.04/1.01  num_eq_ax_congr_red:                    27
% 2.04/1.01  num_of_sem_filtered_clauses:            1
% 2.04/1.01  num_of_subtypes:                        0
% 2.04/1.01  monotx_restored_types:                  0
% 2.04/1.01  sat_num_of_epr_types:                   0
% 2.04/1.01  sat_num_of_non_cyclic_types:            0
% 2.04/1.01  sat_guarded_non_collapsed_types:        0
% 2.04/1.01  num_pure_diseq_elim:                    0
% 2.04/1.01  simp_replaced_by:                       0
% 2.04/1.01  res_preprocessed:                       94
% 2.04/1.01  prep_upred:                             0
% 2.04/1.01  prep_unflattend:                        18
% 2.04/1.01  smt_new_axioms:                         0
% 2.04/1.01  pred_elim_cands:                        4
% 2.04/1.01  pred_elim:                              1
% 2.04/1.01  pred_elim_cl:                           1
% 2.04/1.01  pred_elim_cycles:                       5
% 2.04/1.01  merged_defs:                            0
% 2.04/1.01  merged_defs_ncl:                        0
% 2.04/1.01  bin_hyper_res:                          0
% 2.04/1.01  prep_cycles:                            4
% 2.04/1.01  pred_elim_time:                         0.011
% 2.04/1.01  splitting_time:                         0.
% 2.04/1.01  sem_filter_time:                        0.
% 2.04/1.01  monotx_time:                            0.001
% 2.04/1.01  subtype_inf_time:                       0.
% 2.04/1.01  
% 2.04/1.01  ------ Problem properties
% 2.04/1.01  
% 2.04/1.01  clauses:                                16
% 2.04/1.01  conjectures:                            3
% 2.04/1.01  epr:                                    1
% 2.04/1.01  horn:                                   13
% 2.04/1.01  ground:                                 2
% 2.04/1.01  unary:                                  2
% 2.04/1.01  binary:                                 5
% 2.04/1.01  lits:                                   43
% 2.04/1.01  lits_eq:                                9
% 2.04/1.01  fd_pure:                                0
% 2.04/1.01  fd_pseudo:                              0
% 2.04/1.01  fd_cond:                                3
% 2.04/1.01  fd_pseudo_cond:                         0
% 2.04/1.01  ac_symbols:                             0
% 2.04/1.01  
% 2.04/1.01  ------ Propositional Solver
% 2.04/1.01  
% 2.04/1.01  prop_solver_calls:                      29
% 2.04/1.01  prop_fast_solver_calls:                 705
% 2.04/1.01  smt_solver_calls:                       0
% 2.04/1.01  smt_fast_solver_calls:                  0
% 2.04/1.01  prop_num_of_clauses:                    1069
% 2.04/1.01  prop_preprocess_simplified:             3757
% 2.04/1.01  prop_fo_subsumed:                       9
% 2.04/1.01  prop_solver_time:                       0.
% 2.04/1.01  smt_solver_time:                        0.
% 2.04/1.01  smt_fast_solver_time:                   0.
% 2.04/1.01  prop_fast_solver_time:                  0.
% 2.04/1.01  prop_unsat_core_time:                   0.
% 2.04/1.01  
% 2.04/1.01  ------ QBF
% 2.04/1.01  
% 2.04/1.01  qbf_q_res:                              0
% 2.04/1.01  qbf_num_tautologies:                    0
% 2.04/1.01  qbf_prep_cycles:                        0
% 2.04/1.01  
% 2.04/1.01  ------ BMC1
% 2.04/1.01  
% 2.04/1.01  bmc1_current_bound:                     -1
% 2.04/1.01  bmc1_last_solved_bound:                 -1
% 2.04/1.01  bmc1_unsat_core_size:                   -1
% 2.04/1.01  bmc1_unsat_core_parents_size:           -1
% 2.04/1.01  bmc1_merge_next_fun:                    0
% 2.04/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.04/1.01  
% 2.04/1.01  ------ Instantiation
% 2.04/1.01  
% 2.04/1.01  inst_num_of_clauses:                    294
% 2.04/1.01  inst_num_in_passive:                    81
% 2.04/1.01  inst_num_in_active:                     189
% 2.04/1.01  inst_num_in_unprocessed:                24
% 2.04/1.01  inst_num_of_loops:                      240
% 2.04/1.01  inst_num_of_learning_restarts:          0
% 2.04/1.01  inst_num_moves_active_passive:          47
% 2.04/1.01  inst_lit_activity:                      0
% 2.04/1.01  inst_lit_activity_moves:                0
% 2.04/1.01  inst_num_tautologies:                   0
% 2.04/1.01  inst_num_prop_implied:                  0
% 2.04/1.01  inst_num_existing_simplified:           0
% 2.04/1.01  inst_num_eq_res_simplified:             0
% 2.04/1.01  inst_num_child_elim:                    0
% 2.04/1.01  inst_num_of_dismatching_blockings:      69
% 2.04/1.01  inst_num_of_non_proper_insts:           270
% 2.04/1.01  inst_num_of_duplicates:                 0
% 2.04/1.01  inst_inst_num_from_inst_to_res:         0
% 2.04/1.01  inst_dismatching_checking_time:         0.
% 2.04/1.01  
% 2.04/1.01  ------ Resolution
% 2.04/1.01  
% 2.04/1.01  res_num_of_clauses:                     0
% 2.04/1.01  res_num_in_passive:                     0
% 2.04/1.01  res_num_in_active:                      0
% 2.04/1.01  res_num_of_loops:                       98
% 2.04/1.01  res_forward_subset_subsumed:            17
% 2.04/1.01  res_backward_subset_subsumed:           0
% 2.04/1.01  res_forward_subsumed:                   0
% 2.04/1.01  res_backward_subsumed:                  0
% 2.04/1.01  res_forward_subsumption_resolution:     0
% 2.04/1.01  res_backward_subsumption_resolution:    0
% 2.04/1.01  res_clause_to_clause_subsumption:       170
% 2.04/1.01  res_orphan_elimination:                 0
% 2.04/1.01  res_tautology_del:                      21
% 2.04/1.01  res_num_eq_res_simplified:              0
% 2.04/1.01  res_num_sel_changes:                    0
% 2.04/1.01  res_moves_from_active_to_pass:          0
% 2.04/1.01  
% 2.04/1.01  ------ Superposition
% 2.04/1.01  
% 2.04/1.01  sup_time_total:                         0.
% 2.04/1.01  sup_time_generating:                    0.
% 2.04/1.01  sup_time_sim_full:                      0.
% 2.04/1.01  sup_time_sim_immed:                     0.
% 2.04/1.01  
% 2.04/1.01  sup_num_of_clauses:                     79
% 2.04/1.01  sup_num_in_active:                      45
% 2.04/1.01  sup_num_in_passive:                     34
% 2.04/1.01  sup_num_of_loops:                       46
% 2.04/1.01  sup_fw_superposition:                   70
% 2.04/1.01  sup_bw_superposition:                   17
% 2.04/1.01  sup_immediate_simplified:               9
% 2.04/1.01  sup_given_eliminated:                   1
% 2.04/1.01  comparisons_done:                       0
% 2.04/1.01  comparisons_avoided:                    2
% 2.04/1.01  
% 2.04/1.01  ------ Simplifications
% 2.04/1.01  
% 2.04/1.01  
% 2.04/1.01  sim_fw_subset_subsumed:                 2
% 2.04/1.01  sim_bw_subset_subsumed:                 0
% 2.04/1.01  sim_fw_subsumed:                        0
% 2.04/1.01  sim_bw_subsumed:                        1
% 2.04/1.01  sim_fw_subsumption_res:                 1
% 2.04/1.01  sim_bw_subsumption_res:                 0
% 2.04/1.01  sim_tautology_del:                      0
% 2.04/1.01  sim_eq_tautology_del:                   22
% 2.04/1.01  sim_eq_res_simp:                        0
% 2.04/1.01  sim_fw_demodulated:                     0
% 2.04/1.01  sim_bw_demodulated:                     1
% 2.04/1.01  sim_light_normalised:                   6
% 2.04/1.01  sim_joinable_taut:                      0
% 2.04/1.01  sim_joinable_simp:                      0
% 2.04/1.01  sim_ac_normalised:                      0
% 2.04/1.01  sim_smt_subsumption:                    0
% 2.04/1.01  
%------------------------------------------------------------------------------
