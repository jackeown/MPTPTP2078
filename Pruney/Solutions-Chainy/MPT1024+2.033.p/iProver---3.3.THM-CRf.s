%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:54 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 298 expanded)
%              Number of clauses        :   52 (  94 expanded)
%              Number of leaves         :   12 (  64 expanded)
%              Depth                    :   21
%              Number of atoms          :  325 (1369 expanded)
%              Number of equality atoms :  102 ( 288 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK5
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK4,X5) != X4
              | ~ r2_hidden(X5,sK3)
              | ~ r2_hidden(X5,sK1) )
          & r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ! [X5] :
        ( k1_funct_1(sK4,X5) != sK5
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f23,f33,f32])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X5] :
      ( k1_funct_1(sK4,X5) != sK5
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1021,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1020,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1014,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1024,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1929,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_1024])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1025,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1936,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1929,c_1025])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1023,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1870,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_1023])).

cnf(c_2029,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1936,c_1870])).

cnf(c_2030,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2029])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1026,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2038,plain,
    ( r2_hidden(X0,sK1) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_1026])).

cnf(c_3517,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_2038])).

cnf(c_20,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1164,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1165,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1164])).

cnf(c_4629,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3517,c_20,c_1165])).

cnf(c_4630,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_4629])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1017,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1501,plain,
    ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1014,c_1017])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1015,plain,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1504,plain,
    ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1501,c_1015])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_235,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_236,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_1013,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_237,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_1189,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_20,c_237,c_1165])).

cnf(c_1190,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_1189])).

cnf(c_2060,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_1190])).

cnf(c_2631,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2060,c_20,c_1165])).

cnf(c_2632,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2631])).

cnf(c_2641,plain,
    ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_1504,c_2632])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,X0) != sK5 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1016,plain,
    ( k1_funct_1(sK4,X0) != sK5
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3161,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_1016])).

cnf(c_4637,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4630,c_3161])).

cnf(c_4800,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4637,c_1504])).

cnf(c_4805,plain,
    ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_4800])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4805,c_1504,c_1165,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.80/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.99  
% 2.80/0.99  ------  iProver source info
% 2.80/0.99  
% 2.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.99  git: non_committed_changes: false
% 2.80/0.99  git: last_make_outside_of_git: false
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options
% 2.80/0.99  
% 2.80/0.99  --out_options                           all
% 2.80/0.99  --tptp_safe_out                         true
% 2.80/0.99  --problem_path                          ""
% 2.80/0.99  --include_path                          ""
% 2.80/0.99  --clausifier                            res/vclausify_rel
% 2.80/0.99  --clausifier_options                    --mode clausify
% 2.80/0.99  --stdin                                 false
% 2.80/0.99  --stats_out                             all
% 2.80/0.99  
% 2.80/0.99  ------ General Options
% 2.80/0.99  
% 2.80/0.99  --fof                                   false
% 2.80/0.99  --time_out_real                         305.
% 2.80/0.99  --time_out_virtual                      -1.
% 2.80/0.99  --symbol_type_check                     false
% 2.80/0.99  --clausify_out                          false
% 2.80/0.99  --sig_cnt_out                           false
% 2.80/0.99  --trig_cnt_out                          false
% 2.80/0.99  --trig_cnt_out_tolerance                1.
% 2.80/0.99  --trig_cnt_out_sk_spl                   false
% 2.80/0.99  --abstr_cl_out                          false
% 2.80/0.99  
% 2.80/0.99  ------ Global Options
% 2.80/0.99  
% 2.80/0.99  --schedule                              default
% 2.80/0.99  --add_important_lit                     false
% 2.80/0.99  --prop_solver_per_cl                    1000
% 2.80/0.99  --min_unsat_core                        false
% 2.80/0.99  --soft_assumptions                      false
% 2.80/0.99  --soft_lemma_size                       3
% 2.80/0.99  --prop_impl_unit_size                   0
% 2.80/0.99  --prop_impl_unit                        []
% 2.80/0.99  --share_sel_clauses                     true
% 2.80/0.99  --reset_solvers                         false
% 2.80/0.99  --bc_imp_inh                            [conj_cone]
% 2.80/0.99  --conj_cone_tolerance                   3.
% 2.80/0.99  --extra_neg_conj                        none
% 2.80/0.99  --large_theory_mode                     true
% 2.80/0.99  --prolific_symb_bound                   200
% 2.80/0.99  --lt_threshold                          2000
% 2.80/0.99  --clause_weak_htbl                      true
% 2.80/0.99  --gc_record_bc_elim                     false
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing Options
% 2.80/0.99  
% 2.80/0.99  --preprocessing_flag                    true
% 2.80/0.99  --time_out_prep_mult                    0.1
% 2.80/0.99  --splitting_mode                        input
% 2.80/0.99  --splitting_grd                         true
% 2.80/0.99  --splitting_cvd                         false
% 2.80/0.99  --splitting_cvd_svl                     false
% 2.80/0.99  --splitting_nvd                         32
% 2.80/0.99  --sub_typing                            true
% 2.80/0.99  --prep_gs_sim                           true
% 2.80/0.99  --prep_unflatten                        true
% 2.80/0.99  --prep_res_sim                          true
% 2.80/0.99  --prep_upred                            true
% 2.80/0.99  --prep_sem_filter                       exhaustive
% 2.80/0.99  --prep_sem_filter_out                   false
% 2.80/0.99  --pred_elim                             true
% 2.80/0.99  --res_sim_input                         true
% 2.80/0.99  --eq_ax_congr_red                       true
% 2.80/0.99  --pure_diseq_elim                       true
% 2.80/0.99  --brand_transform                       false
% 2.80/0.99  --non_eq_to_eq                          false
% 2.80/0.99  --prep_def_merge                        true
% 2.80/0.99  --prep_def_merge_prop_impl              false
% 2.80/0.99  --prep_def_merge_mbd                    true
% 2.80/0.99  --prep_def_merge_tr_red                 false
% 2.80/0.99  --prep_def_merge_tr_cl                  false
% 2.80/0.99  --smt_preprocessing                     true
% 2.80/0.99  --smt_ac_axioms                         fast
% 2.80/0.99  --preprocessed_out                      false
% 2.80/0.99  --preprocessed_stats                    false
% 2.80/0.99  
% 2.80/0.99  ------ Abstraction refinement Options
% 2.80/0.99  
% 2.80/0.99  --abstr_ref                             []
% 2.80/0.99  --abstr_ref_prep                        false
% 2.80/0.99  --abstr_ref_until_sat                   false
% 2.80/0.99  --abstr_ref_sig_restrict                funpre
% 2.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.99  --abstr_ref_under                       []
% 2.80/0.99  
% 2.80/0.99  ------ SAT Options
% 2.80/0.99  
% 2.80/0.99  --sat_mode                              false
% 2.80/0.99  --sat_fm_restart_options                ""
% 2.80/0.99  --sat_gr_def                            false
% 2.80/0.99  --sat_epr_types                         true
% 2.80/0.99  --sat_non_cyclic_types                  false
% 2.80/0.99  --sat_finite_models                     false
% 2.80/0.99  --sat_fm_lemmas                         false
% 2.80/0.99  --sat_fm_prep                           false
% 2.80/0.99  --sat_fm_uc_incr                        true
% 2.80/0.99  --sat_out_model                         small
% 2.80/0.99  --sat_out_clauses                       false
% 2.80/0.99  
% 2.80/0.99  ------ QBF Options
% 2.80/0.99  
% 2.80/0.99  --qbf_mode                              false
% 2.80/0.99  --qbf_elim_univ                         false
% 2.80/0.99  --qbf_dom_inst                          none
% 2.80/0.99  --qbf_dom_pre_inst                      false
% 2.80/0.99  --qbf_sk_in                             false
% 2.80/0.99  --qbf_pred_elim                         true
% 2.80/0.99  --qbf_split                             512
% 2.80/0.99  
% 2.80/0.99  ------ BMC1 Options
% 2.80/0.99  
% 2.80/0.99  --bmc1_incremental                      false
% 2.80/0.99  --bmc1_axioms                           reachable_all
% 2.80/0.99  --bmc1_min_bound                        0
% 2.80/0.99  --bmc1_max_bound                        -1
% 2.80/0.99  --bmc1_max_bound_default                -1
% 2.80/0.99  --bmc1_symbol_reachability              true
% 2.80/0.99  --bmc1_property_lemmas                  false
% 2.80/0.99  --bmc1_k_induction                      false
% 2.80/0.99  --bmc1_non_equiv_states                 false
% 2.80/0.99  --bmc1_deadlock                         false
% 2.80/0.99  --bmc1_ucm                              false
% 2.80/0.99  --bmc1_add_unsat_core                   none
% 2.80/0.99  --bmc1_unsat_core_children              false
% 2.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.99  --bmc1_out_stat                         full
% 2.80/0.99  --bmc1_ground_init                      false
% 2.80/0.99  --bmc1_pre_inst_next_state              false
% 2.80/0.99  --bmc1_pre_inst_state                   false
% 2.80/0.99  --bmc1_pre_inst_reach_state             false
% 2.80/0.99  --bmc1_out_unsat_core                   false
% 2.80/0.99  --bmc1_aig_witness_out                  false
% 2.80/0.99  --bmc1_verbose                          false
% 2.80/0.99  --bmc1_dump_clauses_tptp                false
% 2.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.99  --bmc1_dump_file                        -
% 2.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.99  --bmc1_ucm_extend_mode                  1
% 2.80/0.99  --bmc1_ucm_init_mode                    2
% 2.80/0.99  --bmc1_ucm_cone_mode                    none
% 2.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.99  --bmc1_ucm_relax_model                  4
% 2.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.99  --bmc1_ucm_layered_model                none
% 2.80/0.99  --bmc1_ucm_max_lemma_size               10
% 2.80/0.99  
% 2.80/0.99  ------ AIG Options
% 2.80/0.99  
% 2.80/0.99  --aig_mode                              false
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation Options
% 2.80/0.99  
% 2.80/0.99  --instantiation_flag                    true
% 2.80/0.99  --inst_sos_flag                         false
% 2.80/0.99  --inst_sos_phase                        true
% 2.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel_side                     num_symb
% 2.80/0.99  --inst_solver_per_active                1400
% 2.80/0.99  --inst_solver_calls_frac                1.
% 2.80/0.99  --inst_passive_queue_type               priority_queues
% 2.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.99  --inst_passive_queues_freq              [25;2]
% 2.80/0.99  --inst_dismatching                      true
% 2.80/0.99  --inst_eager_unprocessed_to_passive     true
% 2.80/0.99  --inst_prop_sim_given                   true
% 2.80/0.99  --inst_prop_sim_new                     false
% 2.80/0.99  --inst_subs_new                         false
% 2.80/0.99  --inst_eq_res_simp                      false
% 2.80/0.99  --inst_subs_given                       false
% 2.80/0.99  --inst_orphan_elimination               true
% 2.80/0.99  --inst_learning_loop_flag               true
% 2.80/0.99  --inst_learning_start                   3000
% 2.80/0.99  --inst_learning_factor                  2
% 2.80/0.99  --inst_start_prop_sim_after_learn       3
% 2.80/0.99  --inst_sel_renew                        solver
% 2.80/0.99  --inst_lit_activity_flag                true
% 2.80/0.99  --inst_restr_to_given                   false
% 2.80/0.99  --inst_activity_threshold               500
% 2.80/0.99  --inst_out_proof                        true
% 2.80/0.99  
% 2.80/0.99  ------ Resolution Options
% 2.80/0.99  
% 2.80/0.99  --resolution_flag                       true
% 2.80/0.99  --res_lit_sel                           adaptive
% 2.80/0.99  --res_lit_sel_side                      none
% 2.80/0.99  --res_ordering                          kbo
% 2.80/0.99  --res_to_prop_solver                    active
% 2.80/0.99  --res_prop_simpl_new                    false
% 2.80/0.99  --res_prop_simpl_given                  true
% 2.80/0.99  --res_passive_queue_type                priority_queues
% 2.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.99  --res_passive_queues_freq               [15;5]
% 2.80/0.99  --res_forward_subs                      full
% 2.80/0.99  --res_backward_subs                     full
% 2.80/0.99  --res_forward_subs_resolution           true
% 2.80/0.99  --res_backward_subs_resolution          true
% 2.80/0.99  --res_orphan_elimination                true
% 2.80/0.99  --res_time_limit                        2.
% 2.80/0.99  --res_out_proof                         true
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Options
% 2.80/0.99  
% 2.80/0.99  --superposition_flag                    true
% 2.80/0.99  --sup_passive_queue_type                priority_queues
% 2.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.99  --demod_completeness_check              fast
% 2.80/0.99  --demod_use_ground                      true
% 2.80/0.99  --sup_to_prop_solver                    passive
% 2.80/0.99  --sup_prop_simpl_new                    true
% 2.80/0.99  --sup_prop_simpl_given                  true
% 2.80/0.99  --sup_fun_splitting                     false
% 2.80/0.99  --sup_smt_interval                      50000
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Simplification Setup
% 2.80/0.99  
% 2.80/0.99  --sup_indices_passive                   []
% 2.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_full_bw                           [BwDemod]
% 2.80/0.99  --sup_immed_triv                        [TrivRules]
% 2.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_immed_bw_main                     []
% 2.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  
% 2.80/0.99  ------ Combination Options
% 2.80/0.99  
% 2.80/0.99  --comb_res_mult                         3
% 2.80/0.99  --comb_sup_mult                         2
% 2.80/0.99  --comb_inst_mult                        10
% 2.80/0.99  
% 2.80/0.99  ------ Debug Options
% 2.80/0.99  
% 2.80/0.99  --dbg_backtrace                         false
% 2.80/0.99  --dbg_dump_prop_clauses                 false
% 2.80/0.99  --dbg_dump_prop_clauses_file            -
% 2.80/0.99  --dbg_out_stat                          false
% 2.80/0.99  ------ Parsing...
% 2.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.99  ------ Proving...
% 2.80/0.99  ------ Problem Properties 
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  clauses                                 18
% 2.80/0.99  conjectures                             3
% 2.80/0.99  EPR                                     1
% 2.80/0.99  Horn                                    17
% 2.80/0.99  unary                                   2
% 2.80/0.99  binary                                  4
% 2.80/0.99  lits                                    48
% 2.80/0.99  lits eq                                 3
% 2.80/0.99  fd_pure                                 0
% 2.80/0.99  fd_pseudo                               0
% 2.80/0.99  fd_cond                                 0
% 2.80/0.99  fd_pseudo_cond                          1
% 2.80/0.99  AC symbols                              0
% 2.80/0.99  
% 2.80/0.99  ------ Schedule dynamic 5 is on 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  Current options:
% 2.80/0.99  ------ 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options
% 2.80/0.99  
% 2.80/0.99  --out_options                           all
% 2.80/0.99  --tptp_safe_out                         true
% 2.80/0.99  --problem_path                          ""
% 2.80/0.99  --include_path                          ""
% 2.80/0.99  --clausifier                            res/vclausify_rel
% 2.80/0.99  --clausifier_options                    --mode clausify
% 2.80/0.99  --stdin                                 false
% 2.80/0.99  --stats_out                             all
% 2.80/0.99  
% 2.80/0.99  ------ General Options
% 2.80/0.99  
% 2.80/0.99  --fof                                   false
% 2.80/0.99  --time_out_real                         305.
% 2.80/0.99  --time_out_virtual                      -1.
% 2.80/0.99  --symbol_type_check                     false
% 2.80/0.99  --clausify_out                          false
% 2.80/0.99  --sig_cnt_out                           false
% 2.80/0.99  --trig_cnt_out                          false
% 2.80/0.99  --trig_cnt_out_tolerance                1.
% 2.80/0.99  --trig_cnt_out_sk_spl                   false
% 2.80/0.99  --abstr_cl_out                          false
% 2.80/0.99  
% 2.80/0.99  ------ Global Options
% 2.80/0.99  
% 2.80/0.99  --schedule                              default
% 2.80/0.99  --add_important_lit                     false
% 2.80/0.99  --prop_solver_per_cl                    1000
% 2.80/0.99  --min_unsat_core                        false
% 2.80/0.99  --soft_assumptions                      false
% 2.80/0.99  --soft_lemma_size                       3
% 2.80/0.99  --prop_impl_unit_size                   0
% 2.80/0.99  --prop_impl_unit                        []
% 2.80/0.99  --share_sel_clauses                     true
% 2.80/0.99  --reset_solvers                         false
% 2.80/0.99  --bc_imp_inh                            [conj_cone]
% 2.80/0.99  --conj_cone_tolerance                   3.
% 2.80/0.99  --extra_neg_conj                        none
% 2.80/0.99  --large_theory_mode                     true
% 2.80/0.99  --prolific_symb_bound                   200
% 2.80/0.99  --lt_threshold                          2000
% 2.80/0.99  --clause_weak_htbl                      true
% 2.80/0.99  --gc_record_bc_elim                     false
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing Options
% 2.80/0.99  
% 2.80/0.99  --preprocessing_flag                    true
% 2.80/0.99  --time_out_prep_mult                    0.1
% 2.80/0.99  --splitting_mode                        input
% 2.80/0.99  --splitting_grd                         true
% 2.80/0.99  --splitting_cvd                         false
% 2.80/0.99  --splitting_cvd_svl                     false
% 2.80/0.99  --splitting_nvd                         32
% 2.80/0.99  --sub_typing                            true
% 2.80/0.99  --prep_gs_sim                           true
% 2.80/0.99  --prep_unflatten                        true
% 2.80/0.99  --prep_res_sim                          true
% 2.80/0.99  --prep_upred                            true
% 2.80/0.99  --prep_sem_filter                       exhaustive
% 2.80/0.99  --prep_sem_filter_out                   false
% 2.80/0.99  --pred_elim                             true
% 2.80/0.99  --res_sim_input                         true
% 2.80/0.99  --eq_ax_congr_red                       true
% 2.80/0.99  --pure_diseq_elim                       true
% 2.80/0.99  --brand_transform                       false
% 2.80/0.99  --non_eq_to_eq                          false
% 2.80/0.99  --prep_def_merge                        true
% 2.80/0.99  --prep_def_merge_prop_impl              false
% 2.80/0.99  --prep_def_merge_mbd                    true
% 2.80/0.99  --prep_def_merge_tr_red                 false
% 2.80/0.99  --prep_def_merge_tr_cl                  false
% 2.80/0.99  --smt_preprocessing                     true
% 2.80/0.99  --smt_ac_axioms                         fast
% 2.80/0.99  --preprocessed_out                      false
% 2.80/0.99  --preprocessed_stats                    false
% 2.80/0.99  
% 2.80/0.99  ------ Abstraction refinement Options
% 2.80/0.99  
% 2.80/0.99  --abstr_ref                             []
% 2.80/0.99  --abstr_ref_prep                        false
% 2.80/0.99  --abstr_ref_until_sat                   false
% 2.80/0.99  --abstr_ref_sig_restrict                funpre
% 2.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.99  --abstr_ref_under                       []
% 2.80/0.99  
% 2.80/0.99  ------ SAT Options
% 2.80/0.99  
% 2.80/0.99  --sat_mode                              false
% 2.80/0.99  --sat_fm_restart_options                ""
% 2.80/0.99  --sat_gr_def                            false
% 2.80/0.99  --sat_epr_types                         true
% 2.80/0.99  --sat_non_cyclic_types                  false
% 2.80/0.99  --sat_finite_models                     false
% 2.80/0.99  --sat_fm_lemmas                         false
% 2.80/0.99  --sat_fm_prep                           false
% 2.80/0.99  --sat_fm_uc_incr                        true
% 2.80/0.99  --sat_out_model                         small
% 2.80/0.99  --sat_out_clauses                       false
% 2.80/0.99  
% 2.80/0.99  ------ QBF Options
% 2.80/0.99  
% 2.80/0.99  --qbf_mode                              false
% 2.80/0.99  --qbf_elim_univ                         false
% 2.80/0.99  --qbf_dom_inst                          none
% 2.80/0.99  --qbf_dom_pre_inst                      false
% 2.80/0.99  --qbf_sk_in                             false
% 2.80/0.99  --qbf_pred_elim                         true
% 2.80/0.99  --qbf_split                             512
% 2.80/0.99  
% 2.80/0.99  ------ BMC1 Options
% 2.80/0.99  
% 2.80/0.99  --bmc1_incremental                      false
% 2.80/0.99  --bmc1_axioms                           reachable_all
% 2.80/0.99  --bmc1_min_bound                        0
% 2.80/0.99  --bmc1_max_bound                        -1
% 2.80/0.99  --bmc1_max_bound_default                -1
% 2.80/0.99  --bmc1_symbol_reachability              true
% 2.80/0.99  --bmc1_property_lemmas                  false
% 2.80/0.99  --bmc1_k_induction                      false
% 2.80/0.99  --bmc1_non_equiv_states                 false
% 2.80/0.99  --bmc1_deadlock                         false
% 2.80/0.99  --bmc1_ucm                              false
% 2.80/0.99  --bmc1_add_unsat_core                   none
% 2.80/0.99  --bmc1_unsat_core_children              false
% 2.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.99  --bmc1_out_stat                         full
% 2.80/0.99  --bmc1_ground_init                      false
% 2.80/0.99  --bmc1_pre_inst_next_state              false
% 2.80/0.99  --bmc1_pre_inst_state                   false
% 2.80/0.99  --bmc1_pre_inst_reach_state             false
% 2.80/0.99  --bmc1_out_unsat_core                   false
% 2.80/0.99  --bmc1_aig_witness_out                  false
% 2.80/0.99  --bmc1_verbose                          false
% 2.80/0.99  --bmc1_dump_clauses_tptp                false
% 2.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.99  --bmc1_dump_file                        -
% 2.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.99  --bmc1_ucm_extend_mode                  1
% 2.80/0.99  --bmc1_ucm_init_mode                    2
% 2.80/0.99  --bmc1_ucm_cone_mode                    none
% 2.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.99  --bmc1_ucm_relax_model                  4
% 2.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.99  --bmc1_ucm_layered_model                none
% 2.80/0.99  --bmc1_ucm_max_lemma_size               10
% 2.80/0.99  
% 2.80/0.99  ------ AIG Options
% 2.80/0.99  
% 2.80/0.99  --aig_mode                              false
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation Options
% 2.80/0.99  
% 2.80/0.99  --instantiation_flag                    true
% 2.80/0.99  --inst_sos_flag                         false
% 2.80/0.99  --inst_sos_phase                        true
% 2.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel_side                     none
% 2.80/0.99  --inst_solver_per_active                1400
% 2.80/0.99  --inst_solver_calls_frac                1.
% 2.80/0.99  --inst_passive_queue_type               priority_queues
% 2.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.99  --inst_passive_queues_freq              [25;2]
% 2.80/0.99  --inst_dismatching                      true
% 2.80/0.99  --inst_eager_unprocessed_to_passive     true
% 2.80/0.99  --inst_prop_sim_given                   true
% 2.80/0.99  --inst_prop_sim_new                     false
% 2.80/0.99  --inst_subs_new                         false
% 2.80/0.99  --inst_eq_res_simp                      false
% 2.80/0.99  --inst_subs_given                       false
% 2.80/0.99  --inst_orphan_elimination               true
% 2.80/0.99  --inst_learning_loop_flag               true
% 2.80/0.99  --inst_learning_start                   3000
% 2.80/0.99  --inst_learning_factor                  2
% 2.80/0.99  --inst_start_prop_sim_after_learn       3
% 2.80/0.99  --inst_sel_renew                        solver
% 2.80/0.99  --inst_lit_activity_flag                true
% 2.80/0.99  --inst_restr_to_given                   false
% 2.80/0.99  --inst_activity_threshold               500
% 2.80/0.99  --inst_out_proof                        true
% 2.80/0.99  
% 2.80/0.99  ------ Resolution Options
% 2.80/0.99  
% 2.80/0.99  --resolution_flag                       false
% 2.80/0.99  --res_lit_sel                           adaptive
% 2.80/0.99  --res_lit_sel_side                      none
% 2.80/0.99  --res_ordering                          kbo
% 2.80/0.99  --res_to_prop_solver                    active
% 2.80/0.99  --res_prop_simpl_new                    false
% 2.80/0.99  --res_prop_simpl_given                  true
% 2.80/0.99  --res_passive_queue_type                priority_queues
% 2.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.99  --res_passive_queues_freq               [15;5]
% 2.80/0.99  --res_forward_subs                      full
% 2.80/0.99  --res_backward_subs                     full
% 2.80/0.99  --res_forward_subs_resolution           true
% 2.80/0.99  --res_backward_subs_resolution          true
% 2.80/0.99  --res_orphan_elimination                true
% 2.80/0.99  --res_time_limit                        2.
% 2.80/0.99  --res_out_proof                         true
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Options
% 2.80/0.99  
% 2.80/0.99  --superposition_flag                    true
% 2.80/0.99  --sup_passive_queue_type                priority_queues
% 2.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.99  --demod_completeness_check              fast
% 2.80/0.99  --demod_use_ground                      true
% 2.80/0.99  --sup_to_prop_solver                    passive
% 2.80/0.99  --sup_prop_simpl_new                    true
% 2.80/0.99  --sup_prop_simpl_given                  true
% 2.80/0.99  --sup_fun_splitting                     false
% 2.80/0.99  --sup_smt_interval                      50000
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Simplification Setup
% 2.80/0.99  
% 2.80/0.99  --sup_indices_passive                   []
% 2.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_full_bw                           [BwDemod]
% 2.80/0.99  --sup_immed_triv                        [TrivRules]
% 2.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_immed_bw_main                     []
% 2.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  
% 2.80/0.99  ------ Combination Options
% 2.80/0.99  
% 2.80/0.99  --comb_res_mult                         3
% 2.80/0.99  --comb_sup_mult                         2
% 2.80/0.99  --comb_inst_mult                        10
% 2.80/0.99  
% 2.80/0.99  ------ Debug Options
% 2.80/0.99  
% 2.80/0.99  --dbg_backtrace                         false
% 2.80/0.99  --dbg_dump_prop_clauses                 false
% 2.80/0.99  --dbg_dump_prop_clauses_file            -
% 2.80/0.99  --dbg_out_stat                          false
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ Proving...
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS status Theorem for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  fof(f5,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f17,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.80/0.99    inference(ennf_transformation,[],[f5])).
% 2.80/0.99  
% 2.80/0.99  fof(f26,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.80/0.99    inference(nnf_transformation,[],[f17])).
% 2.80/0.99  
% 2.80/0.99  fof(f27,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.80/0.99    inference(rectify,[],[f26])).
% 2.80/0.99  
% 2.80/0.99  fof(f28,plain,(
% 2.80/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f29,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.80/0.99  
% 2.80/0.99  fof(f43,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f29])).
% 2.80/0.99  
% 2.80/0.99  fof(f42,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f29])).
% 2.80/0.99  
% 2.80/0.99  fof(f9,conjecture,(
% 2.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f10,negated_conjecture,(
% 2.80/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.80/0.99    inference(negated_conjecture,[],[f9])).
% 2.80/0.99  
% 2.80/0.99  fof(f11,plain,(
% 2.80/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.80/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.80/0.99  
% 2.80/0.99  fof(f22,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.80/0.99    inference(ennf_transformation,[],[f11])).
% 2.80/0.99  
% 2.80/0.99  fof(f23,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.80/0.99    inference(flattening,[],[f22])).
% 2.80/0.99  
% 2.80/0.99  fof(f33,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK5 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f32,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK4,X5) != X4 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f34,plain,(
% 2.80/0.99    (! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4)),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f23,f33,f32])).
% 2.80/0.99  
% 2.80/0.99  fof(f51,plain,(
% 2.80/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.80/0.99    inference(cnf_transformation,[],[f34])).
% 2.80/0.99  
% 2.80/0.99  fof(f3,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f14,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.80/0.99    inference(ennf_transformation,[],[f3])).
% 2.80/0.99  
% 2.80/0.99  fof(f15,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.80/0.99    inference(flattening,[],[f14])).
% 2.80/0.99  
% 2.80/0.99  fof(f39,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f15])).
% 2.80/0.99  
% 2.80/0.99  fof(f2,axiom,(
% 2.80/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f12,plain,(
% 2.80/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.80/0.99    inference(ennf_transformation,[],[f2])).
% 2.80/0.99  
% 2.80/0.99  fof(f13,plain,(
% 2.80/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.80/0.99    inference(flattening,[],[f12])).
% 2.80/0.99  
% 2.80/0.99  fof(f38,plain,(
% 2.80/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f13])).
% 2.80/0.99  
% 2.80/0.99  fof(f4,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f16,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.80/0.99    inference(ennf_transformation,[],[f4])).
% 2.80/0.99  
% 2.80/0.99  fof(f40,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f1,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f24,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.80/0.99    inference(nnf_transformation,[],[f1])).
% 2.80/0.99  
% 2.80/0.99  fof(f25,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.80/0.99    inference(flattening,[],[f24])).
% 2.80/0.99  
% 2.80/0.99  fof(f35,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f25])).
% 2.80/0.99  
% 2.80/0.99  fof(f7,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f20,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.99    inference(ennf_transformation,[],[f7])).
% 2.80/0.99  
% 2.80/0.99  fof(f48,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f20])).
% 2.80/0.99  
% 2.80/0.99  fof(f8,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f21,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.99    inference(ennf_transformation,[],[f8])).
% 2.80/0.99  
% 2.80/0.99  fof(f49,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f21])).
% 2.80/0.99  
% 2.80/0.99  fof(f52,plain,(
% 2.80/0.99    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))),
% 2.80/0.99    inference(cnf_transformation,[],[f34])).
% 2.80/0.99  
% 2.80/0.99  fof(f6,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f18,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.80/0.99    inference(ennf_transformation,[],[f6])).
% 2.80/0.99  
% 2.80/0.99  fof(f19,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.80/0.99    inference(flattening,[],[f18])).
% 2.80/0.99  
% 2.80/0.99  fof(f30,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.80/0.99    inference(nnf_transformation,[],[f19])).
% 2.80/0.99  
% 2.80/0.99  fof(f31,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.80/0.99    inference(flattening,[],[f30])).
% 2.80/0.99  
% 2.80/0.99  fof(f46,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f31])).
% 2.80/0.99  
% 2.80/0.99  fof(f50,plain,(
% 2.80/0.99    v1_funct_1(sK4)),
% 2.80/0.99    inference(cnf_transformation,[],[f34])).
% 2.80/0.99  
% 2.80/0.99  fof(f53,plain,(
% 2.80/0.99    ( ! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f34])).
% 2.80/0.99  
% 2.80/0.99  cnf(c_7,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.80/0.99      | r2_hidden(sK0(X0,X2,X1),X2)
% 2.80/0.99      | ~ v1_relat_1(X1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1021,plain,
% 2.80/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.80/0.99      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 2.80/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_8,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.80/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 2.80/0.99      | ~ v1_relat_1(X1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1020,plain,
% 2.80/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.80/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 2.80/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_17,negated_conjecture,
% 2.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1014,plain,
% 2.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4,plain,
% 2.80/0.99      ( m1_subset_1(X0,X1)
% 2.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.80/0.99      | ~ r2_hidden(X0,X2) ),
% 2.80/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1024,plain,
% 2.80/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.80/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1929,plain,
% 2.80/0.99      ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
% 2.80/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1014,c_1024]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1025,plain,
% 2.80/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.80/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.80/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1936,plain,
% 2.80/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
% 2.80/0.99      | r2_hidden(X0,sK4) != iProver_top
% 2.80/0.99      | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1929,c_1025]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_5,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/0.99      | ~ r2_hidden(X2,X0)
% 2.80/0.99      | ~ v1_xboole_0(X1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1023,plain,
% 2.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.80/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.80/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1870,plain,
% 2.80/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.80/0.99      | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1014,c_1023]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2029,plain,
% 2.80/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.80/0.99      | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_1936,c_1870]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2030,plain,
% 2.80/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
% 2.80/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_2029]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2,plain,
% 2.80/0.99      ( r2_hidden(X0,X1)
% 2.80/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1026,plain,
% 2.80/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.80/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2038,plain,
% 2.80/0.99      ( r2_hidden(X0,sK1) = iProver_top
% 2.80/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2030,c_1026]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3517,plain,
% 2.80/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.80/0.99      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 2.80/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1020,c_2038]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_20,plain,
% 2.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_13,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | v1_relat_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1164,plain,
% 2.80/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.80/0.99      | v1_relat_1(sK4) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1165,plain,
% 2.80/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.80/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1164]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4629,plain,
% 2.80/0.99      ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 2.80/0.99      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_3517,c_20,c_1165]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4630,plain,
% 2.80/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.80/0.99      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_4629]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_14,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.80/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1017,plain,
% 2.80/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.80/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1501,plain,
% 2.80/0.99      ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1014,c_1017]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_16,negated_conjecture,
% 2.80/0.99      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1015,plain,
% 2.80/0.99      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1504,plain,
% 2.80/0.99      ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_1501,c_1015]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_11,plain,
% 2.80/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.80/0.99      | ~ v1_funct_1(X2)
% 2.80/0.99      | ~ v1_relat_1(X2)
% 2.80/0.99      | k1_funct_1(X2,X0) = X1 ),
% 2.80/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_18,negated_conjecture,
% 2.80/0.99      ( v1_funct_1(sK4) ),
% 2.80/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_235,plain,
% 2.80/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.80/0.99      | ~ v1_relat_1(X2)
% 2.80/0.99      | k1_funct_1(X2,X0) = X1
% 2.80/0.99      | sK4 != X2 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_236,plain,
% 2.80/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 2.80/0.99      | ~ v1_relat_1(sK4)
% 2.80/0.99      | k1_funct_1(sK4,X0) = X1 ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_235]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1013,plain,
% 2.80/0.99      ( k1_funct_1(sK4,X0) = X1
% 2.80/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.80/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_237,plain,
% 2.80/0.99      ( k1_funct_1(sK4,X0) = X1
% 2.80/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.80/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1189,plain,
% 2.80/0.99      ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.80/0.99      | k1_funct_1(sK4,X0) = X1 ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_1013,c_20,c_237,c_1165]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1190,plain,
% 2.80/0.99      ( k1_funct_1(sK4,X0) = X1
% 2.80/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_1189]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2060,plain,
% 2.80/0.99      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 2.80/0.99      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.80/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1020,c_1190]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2631,plain,
% 2.80/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.80/0.99      | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_2060,c_20,c_1165]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2632,plain,
% 2.80/0.99      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 2.80/0.99      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_2631]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2641,plain,
% 2.80/0.99      ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1504,c_2632]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_15,negated_conjecture,
% 2.80/0.99      ( ~ r2_hidden(X0,sK1)
% 2.80/0.99      | ~ r2_hidden(X0,sK3)
% 2.80/0.99      | k1_funct_1(sK4,X0) != sK5 ),
% 2.80/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1016,plain,
% 2.80/0.99      ( k1_funct_1(sK4,X0) != sK5
% 2.80/0.99      | r2_hidden(X0,sK1) != iProver_top
% 2.80/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3161,plain,
% 2.80/0.99      ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
% 2.80/0.99      | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2641,c_1016]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4637,plain,
% 2.80/0.99      ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
% 2.80/0.99      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_4630,c_3161]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4800,plain,
% 2.80/0.99      ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_4637,c_1504]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4805,plain,
% 2.80/0.99      ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
% 2.80/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1021,c_4800]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(contradiction,plain,
% 2.80/0.99      ( $false ),
% 2.80/0.99      inference(minisat,[status(thm)],[c_4805,c_1504,c_1165,c_20]) ).
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  ------                               Statistics
% 2.80/0.99  
% 2.80/0.99  ------ General
% 2.80/0.99  
% 2.80/0.99  abstr_ref_over_cycles:                  0
% 2.80/0.99  abstr_ref_under_cycles:                 0
% 2.80/0.99  gc_basic_clause_elim:                   0
% 2.80/0.99  forced_gc_time:                         0
% 2.80/0.99  parsing_time:                           0.01
% 2.80/0.99  unif_index_cands_time:                  0.
% 2.80/0.99  unif_index_add_time:                    0.
% 2.80/0.99  orderings_time:                         0.
% 2.80/0.99  out_proof_time:                         0.02
% 2.80/0.99  total_time:                             0.212
% 2.80/0.99  num_of_symbols:                         49
% 2.80/0.99  num_of_terms:                           6981
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing
% 2.80/0.99  
% 2.80/0.99  num_of_splits:                          0
% 2.80/0.99  num_of_split_atoms:                     0
% 2.80/0.99  num_of_reused_defs:                     0
% 2.80/0.99  num_eq_ax_congr_red:                    23
% 2.80/0.99  num_of_sem_filtered_clauses:            1
% 2.80/0.99  num_of_subtypes:                        0
% 2.80/0.99  monotx_restored_types:                  0
% 2.80/0.99  sat_num_of_epr_types:                   0
% 2.80/0.99  sat_num_of_non_cyclic_types:            0
% 2.80/0.99  sat_guarded_non_collapsed_types:        0
% 2.80/0.99  num_pure_diseq_elim:                    0
% 2.80/0.99  simp_replaced_by:                       0
% 2.80/0.99  res_preprocessed:                       96
% 2.80/0.99  prep_upred:                             0
% 2.80/0.99  prep_unflattend:                        17
% 2.80/0.99  smt_new_axioms:                         0
% 2.80/0.99  pred_elim_cands:                        4
% 2.80/0.99  pred_elim:                              1
% 2.80/0.99  pred_elim_cl:                           1
% 2.80/0.99  pred_elim_cycles:                       5
% 2.80/0.99  merged_defs:                            0
% 2.80/0.99  merged_defs_ncl:                        0
% 2.80/0.99  bin_hyper_res:                          0
% 2.80/0.99  prep_cycles:                            4
% 2.80/0.99  pred_elim_time:                         0.006
% 2.80/0.99  splitting_time:                         0.
% 2.80/0.99  sem_filter_time:                        0.
% 2.80/0.99  monotx_time:                            0.
% 2.80/0.99  subtype_inf_time:                       0.
% 2.80/0.99  
% 2.80/0.99  ------ Problem properties
% 2.80/0.99  
% 2.80/0.99  clauses:                                18
% 2.80/0.99  conjectures:                            3
% 2.80/0.99  epr:                                    1
% 2.80/0.99  horn:                                   17
% 2.80/0.99  ground:                                 2
% 2.80/0.99  unary:                                  2
% 2.80/0.99  binary:                                 4
% 2.80/0.99  lits:                                   48
% 2.80/0.99  lits_eq:                                3
% 2.80/0.99  fd_pure:                                0
% 2.80/0.99  fd_pseudo:                              0
% 2.80/0.99  fd_cond:                                0
% 2.80/0.99  fd_pseudo_cond:                         1
% 2.80/0.99  ac_symbols:                             0
% 2.80/0.99  
% 2.80/0.99  ------ Propositional Solver
% 2.80/0.99  
% 2.80/0.99  prop_solver_calls:                      28
% 2.80/0.99  prop_fast_solver_calls:                 701
% 2.80/0.99  smt_solver_calls:                       0
% 2.80/0.99  smt_fast_solver_calls:                  0
% 2.80/0.99  prop_num_of_clauses:                    2195
% 2.80/0.99  prop_preprocess_simplified:             6025
% 2.80/0.99  prop_fo_subsumed:                       9
% 2.80/0.99  prop_solver_time:                       0.
% 2.80/0.99  smt_solver_time:                        0.
% 2.80/0.99  smt_fast_solver_time:                   0.
% 2.80/0.99  prop_fast_solver_time:                  0.
% 2.80/0.99  prop_unsat_core_time:                   0.
% 2.80/0.99  
% 2.80/0.99  ------ QBF
% 2.80/0.99  
% 2.80/0.99  qbf_q_res:                              0
% 2.80/0.99  qbf_num_tautologies:                    0
% 2.80/0.99  qbf_prep_cycles:                        0
% 2.80/0.99  
% 2.80/0.99  ------ BMC1
% 2.80/0.99  
% 2.80/0.99  bmc1_current_bound:                     -1
% 2.80/0.99  bmc1_last_solved_bound:                 -1
% 2.80/0.99  bmc1_unsat_core_size:                   -1
% 2.80/0.99  bmc1_unsat_core_parents_size:           -1
% 2.80/0.99  bmc1_merge_next_fun:                    0
% 2.80/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation
% 2.80/0.99  
% 2.80/0.99  inst_num_of_clauses:                    686
% 2.80/0.99  inst_num_in_passive:                    355
% 2.80/0.99  inst_num_in_active:                     181
% 2.80/0.99  inst_num_in_unprocessed:                150
% 2.80/0.99  inst_num_of_loops:                      210
% 2.80/0.99  inst_num_of_learning_restarts:          0
% 2.80/0.99  inst_num_moves_active_passive:          26
% 2.80/0.99  inst_lit_activity:                      0
% 2.80/0.99  inst_lit_activity_moves:                1
% 2.80/0.99  inst_num_tautologies:                   0
% 2.80/0.99  inst_num_prop_implied:                  0
% 2.80/0.99  inst_num_existing_simplified:           0
% 2.80/0.99  inst_num_eq_res_simplified:             0
% 2.80/0.99  inst_num_child_elim:                    0
% 2.80/0.99  inst_num_of_dismatching_blockings:      10
% 2.80/0.99  inst_num_of_non_proper_insts:           377
% 2.80/0.99  inst_num_of_duplicates:                 0
% 2.80/0.99  inst_inst_num_from_inst_to_res:         0
% 2.80/0.99  inst_dismatching_checking_time:         0.
% 2.80/0.99  
% 2.80/0.99  ------ Resolution
% 2.80/0.99  
% 2.80/0.99  res_num_of_clauses:                     0
% 2.80/0.99  res_num_in_passive:                     0
% 2.80/0.99  res_num_in_active:                      0
% 2.80/0.99  res_num_of_loops:                       100
% 2.80/0.99  res_forward_subset_subsumed:            43
% 2.80/0.99  res_backward_subset_subsumed:           0
% 2.80/0.99  res_forward_subsumed:                   0
% 2.80/0.99  res_backward_subsumed:                  0
% 2.80/0.99  res_forward_subsumption_resolution:     0
% 2.80/0.99  res_backward_subsumption_resolution:    0
% 2.80/0.99  res_clause_to_clause_subsumption:       80
% 2.80/0.99  res_orphan_elimination:                 0
% 2.80/0.99  res_tautology_del:                      11
% 2.80/0.99  res_num_eq_res_simplified:              0
% 2.80/0.99  res_num_sel_changes:                    0
% 2.80/0.99  res_moves_from_active_to_pass:          0
% 2.80/0.99  
% 2.80/0.99  ------ Superposition
% 2.80/0.99  
% 2.80/0.99  sup_time_total:                         0.
% 2.80/0.99  sup_time_generating:                    0.
% 2.80/0.99  sup_time_sim_full:                      0.
% 2.80/0.99  sup_time_sim_immed:                     0.
% 2.80/0.99  
% 2.80/0.99  sup_num_of_clauses:                     54
% 2.80/0.99  sup_num_in_active:                      40
% 2.80/0.99  sup_num_in_passive:                     14
% 2.80/0.99  sup_num_of_loops:                       40
% 2.80/0.99  sup_fw_superposition:                   28
% 2.80/0.99  sup_bw_superposition:                   20
% 2.80/0.99  sup_immediate_simplified:               4
% 2.80/0.99  sup_given_eliminated:                   0
% 2.80/0.99  comparisons_done:                       0
% 2.80/0.99  comparisons_avoided:                    0
% 2.80/0.99  
% 2.80/0.99  ------ Simplifications
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  sim_fw_subset_subsumed:                 2
% 2.80/0.99  sim_bw_subset_subsumed:                 1
% 2.80/0.99  sim_fw_subsumed:                        1
% 2.80/0.99  sim_bw_subsumed:                        1
% 2.80/0.99  sim_fw_subsumption_res:                 0
% 2.80/0.99  sim_bw_subsumption_res:                 0
% 2.80/0.99  sim_tautology_del:                      4
% 2.80/0.99  sim_eq_tautology_del:                   1
% 2.80/0.99  sim_eq_res_simp:                        0
% 2.80/0.99  sim_fw_demodulated:                     0
% 2.80/0.99  sim_bw_demodulated:                     1
% 2.80/0.99  sim_light_normalised:                   0
% 2.80/0.99  sim_joinable_taut:                      0
% 2.80/0.99  sim_joinable_simp:                      0
% 2.80/0.99  sim_ac_normalised:                      0
% 2.80/0.99  sim_smt_subsumption:                    0
% 2.80/0.99  
%------------------------------------------------------------------------------
