%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:54 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 888 expanded)
%              Number of clauses        :   97 ( 275 expanded)
%              Number of leaves         :   15 ( 189 expanded)
%              Depth                    :   20
%              Number of atoms          :  539 (6841 expanded)
%              Number of equality atoms :  260 (2323 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4 != sK5
        & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5)
        & r2_hidden(sK5,X0)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f23,f22])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f25,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_214,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_215,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_1561,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_1798,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_16,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_38,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_40,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_41,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_43,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_1574,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1594,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_197,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_198,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_1562,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_1604,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_1606,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_240,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_241,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_1559,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_1609,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_253,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_254,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_1558,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(subtyping,[status(esa)],[c_254])).

cnf(c_1610,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_1576,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1909,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_188,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_189,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_1563,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_189])).

cnf(c_1927,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_1563])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_179,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_180,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(sK2,sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_182,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_180,c_15,c_13])).

cnf(c_1564,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_1928,plain,
    ( k1_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1927,c_1564])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1565,negated_conjecture,
    ( ~ r2_hidden(X0_45,sK2)
    | ~ r2_hidden(X1_45,sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,X1_45) != k1_funct_1(sK3,X0_45)
    | X1_45 = X0_45 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1929,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_1930,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_1573,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1960,plain,
    ( sK1(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_1579,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_1973,plain,
    ( X0_46 != X1_46
    | X0_46 = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X1_46 ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_1974,plain,
    ( k1_relat_1(sK3) != sK2
    | sK2 = k1_relat_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_1583,plain,
    ( ~ r2_hidden(X0_45,X0_46)
    | r2_hidden(X1_45,X1_46)
    | X1_46 != X0_46
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1934,plain,
    ( r2_hidden(X0_45,X0_46)
    | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | X0_46 != k1_relat_1(sK3)
    | X0_45 != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_2019,plain,
    ( r2_hidden(sK1(sK3),X0_46)
    | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | X0_46 != k1_relat_1(sK3)
    | sK1(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_2020,plain,
    ( X0_46 != k1_relat_1(sK3)
    | sK1(sK3) != sK1(sK3)
    | r2_hidden(sK1(sK3),X0_46) = iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_2022,plain,
    ( sK2 != k1_relat_1(sK3)
    | sK1(sK3) != sK1(sK3)
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK1(sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_1939,plain,
    ( r2_hidden(X0_45,X0_46)
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | X0_46 != k1_relat_1(sK3)
    | X0_45 != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_2029,plain,
    ( r2_hidden(sK0(sK3),X0_46)
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | X0_46 != k1_relat_1(sK3)
    | sK0(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1939])).

cnf(c_2031,plain,
    ( X0_46 != k1_relat_1(sK3)
    | sK0(sK3) != sK0(sK3)
    | r2_hidden(sK0(sK3),X0_46) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

cnf(c_2033,plain,
    ( sK2 != k1_relat_1(sK3)
    | sK0(sK3) != sK0(sK3)
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_2030,plain,
    ( sK0(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_2051,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1798,c_16,c_40,c_43,c_1594,c_1606,c_1609,c_1610,c_1909,c_1928,c_1930,c_1960,c_1974,c_2022,c_2033,c_2030])).

cnf(c_9,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1568,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1793,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_2056,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2051,c_1793])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_266,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_1557,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(sK3))
    | ~ r2_hidden(X1_45,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
    | X0_45 = X1_45 ),
    inference(subtyping,[status(esa)],[c_267])).

cnf(c_1570,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(sK3))
    | ~ r2_hidden(X1_45,k1_relat_1(sK3))
    | k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
    | X0_45 = X1_45
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1557])).

cnf(c_1803,plain,
    ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
    | X0_45 = X1_45
    | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_1571,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1557])).

cnf(c_1611,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_1612,plain,
    ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
    | X0_45 = X1_45
    | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_2155,plain,
    ( r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
    | X0_45 = X1_45
    | k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1803,c_16,c_40,c_43,c_1594,c_1606,c_1609,c_1610,c_1611,c_1612,c_1909,c_1928,c_1930,c_1960,c_1974,c_2022,c_2033,c_2030])).

cnf(c_2156,plain,
    ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
    | X0_45 = X1_45
    | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2155])).

cnf(c_2159,plain,
    ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
    | X0_45 = X1_45
    | r2_hidden(X0_45,sK2) != iProver_top
    | r2_hidden(X1_45,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2156,c_1928])).

cnf(c_2165,plain,
    ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,sK4)
    | sK5 = X0_45
    | r2_hidden(X0_45,sK2) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2056,c_2159])).

cnf(c_2177,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4)
    | sK5 = sK4
    | r2_hidden(sK5,sK2) != iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_1578,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_2061,plain,
    ( sK5 != X0_45
    | sK4 != X0_45
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_2062,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_8,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1569,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1598,plain,
    ( sK4 != sK5
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_1593,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_1582,plain,
    ( k1_funct_1(X0_47,X0_45) = k1_funct_1(X0_47,X1_45)
    | X0_45 != X1_45 ),
    theory(equality)).

cnf(c_1587,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1582])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2177,c_2062,c_2051,c_1598,c_1593,c_1587,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.18/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.18/1.03  
% 1.18/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.18/1.03  
% 1.18/1.03  ------  iProver source info
% 1.18/1.03  
% 1.18/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.18/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.18/1.03  git: non_committed_changes: false
% 1.18/1.03  git: last_make_outside_of_git: false
% 1.18/1.03  
% 1.18/1.03  ------ 
% 1.18/1.03  
% 1.18/1.03  ------ Input Options
% 1.18/1.03  
% 1.18/1.03  --out_options                           all
% 1.18/1.03  --tptp_safe_out                         true
% 1.18/1.03  --problem_path                          ""
% 1.18/1.03  --include_path                          ""
% 1.18/1.03  --clausifier                            res/vclausify_rel
% 1.18/1.03  --clausifier_options                    --mode clausify
% 1.18/1.03  --stdin                                 false
% 1.18/1.03  --stats_out                             all
% 1.18/1.03  
% 1.18/1.03  ------ General Options
% 1.18/1.03  
% 1.18/1.03  --fof                                   false
% 1.18/1.03  --time_out_real                         305.
% 1.18/1.03  --time_out_virtual                      -1.
% 1.18/1.03  --symbol_type_check                     false
% 1.18/1.03  --clausify_out                          false
% 1.18/1.03  --sig_cnt_out                           false
% 1.18/1.03  --trig_cnt_out                          false
% 1.18/1.03  --trig_cnt_out_tolerance                1.
% 1.18/1.03  --trig_cnt_out_sk_spl                   false
% 1.18/1.03  --abstr_cl_out                          false
% 1.18/1.03  
% 1.18/1.03  ------ Global Options
% 1.18/1.03  
% 1.18/1.03  --schedule                              default
% 1.18/1.03  --add_important_lit                     false
% 1.18/1.03  --prop_solver_per_cl                    1000
% 1.18/1.03  --min_unsat_core                        false
% 1.18/1.03  --soft_assumptions                      false
% 1.18/1.03  --soft_lemma_size                       3
% 1.18/1.03  --prop_impl_unit_size                   0
% 1.18/1.03  --prop_impl_unit                        []
% 1.18/1.03  --share_sel_clauses                     true
% 1.18/1.03  --reset_solvers                         false
% 1.18/1.03  --bc_imp_inh                            [conj_cone]
% 1.18/1.03  --conj_cone_tolerance                   3.
% 1.18/1.03  --extra_neg_conj                        none
% 1.18/1.03  --large_theory_mode                     true
% 1.18/1.03  --prolific_symb_bound                   200
% 1.18/1.03  --lt_threshold                          2000
% 1.18/1.03  --clause_weak_htbl                      true
% 1.18/1.03  --gc_record_bc_elim                     false
% 1.18/1.03  
% 1.18/1.03  ------ Preprocessing Options
% 1.18/1.03  
% 1.18/1.03  --preprocessing_flag                    true
% 1.18/1.03  --time_out_prep_mult                    0.1
% 1.18/1.03  --splitting_mode                        input
% 1.18/1.03  --splitting_grd                         true
% 1.18/1.03  --splitting_cvd                         false
% 1.18/1.03  --splitting_cvd_svl                     false
% 1.18/1.03  --splitting_nvd                         32
% 1.18/1.03  --sub_typing                            true
% 1.18/1.03  --prep_gs_sim                           true
% 1.18/1.03  --prep_unflatten                        true
% 1.18/1.03  --prep_res_sim                          true
% 1.18/1.03  --prep_upred                            true
% 1.18/1.03  --prep_sem_filter                       exhaustive
% 1.18/1.03  --prep_sem_filter_out                   false
% 1.18/1.03  --pred_elim                             true
% 1.18/1.03  --res_sim_input                         true
% 1.18/1.03  --eq_ax_congr_red                       true
% 1.18/1.03  --pure_diseq_elim                       true
% 1.18/1.03  --brand_transform                       false
% 1.18/1.03  --non_eq_to_eq                          false
% 1.18/1.03  --prep_def_merge                        true
% 1.18/1.03  --prep_def_merge_prop_impl              false
% 1.18/1.03  --prep_def_merge_mbd                    true
% 1.18/1.03  --prep_def_merge_tr_red                 false
% 1.18/1.03  --prep_def_merge_tr_cl                  false
% 1.18/1.03  --smt_preprocessing                     true
% 1.18/1.03  --smt_ac_axioms                         fast
% 1.18/1.03  --preprocessed_out                      false
% 1.18/1.03  --preprocessed_stats                    false
% 1.18/1.03  
% 1.18/1.03  ------ Abstraction refinement Options
% 1.18/1.03  
% 1.18/1.03  --abstr_ref                             []
% 1.18/1.03  --abstr_ref_prep                        false
% 1.18/1.03  --abstr_ref_until_sat                   false
% 1.18/1.03  --abstr_ref_sig_restrict                funpre
% 1.18/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/1.03  --abstr_ref_under                       []
% 1.18/1.03  
% 1.18/1.03  ------ SAT Options
% 1.18/1.03  
% 1.18/1.03  --sat_mode                              false
% 1.18/1.03  --sat_fm_restart_options                ""
% 1.18/1.03  --sat_gr_def                            false
% 1.18/1.03  --sat_epr_types                         true
% 1.18/1.03  --sat_non_cyclic_types                  false
% 1.18/1.03  --sat_finite_models                     false
% 1.18/1.03  --sat_fm_lemmas                         false
% 1.18/1.03  --sat_fm_prep                           false
% 1.18/1.03  --sat_fm_uc_incr                        true
% 1.18/1.03  --sat_out_model                         small
% 1.18/1.03  --sat_out_clauses                       false
% 1.18/1.03  
% 1.18/1.03  ------ QBF Options
% 1.18/1.03  
% 1.18/1.03  --qbf_mode                              false
% 1.18/1.03  --qbf_elim_univ                         false
% 1.18/1.03  --qbf_dom_inst                          none
% 1.18/1.03  --qbf_dom_pre_inst                      false
% 1.18/1.03  --qbf_sk_in                             false
% 1.18/1.03  --qbf_pred_elim                         true
% 1.18/1.03  --qbf_split                             512
% 1.18/1.03  
% 1.18/1.03  ------ BMC1 Options
% 1.18/1.03  
% 1.18/1.03  --bmc1_incremental                      false
% 1.18/1.03  --bmc1_axioms                           reachable_all
% 1.18/1.03  --bmc1_min_bound                        0
% 1.18/1.03  --bmc1_max_bound                        -1
% 1.18/1.03  --bmc1_max_bound_default                -1
% 1.18/1.03  --bmc1_symbol_reachability              true
% 1.18/1.03  --bmc1_property_lemmas                  false
% 1.18/1.03  --bmc1_k_induction                      false
% 1.18/1.03  --bmc1_non_equiv_states                 false
% 1.18/1.03  --bmc1_deadlock                         false
% 1.18/1.03  --bmc1_ucm                              false
% 1.18/1.03  --bmc1_add_unsat_core                   none
% 1.18/1.03  --bmc1_unsat_core_children              false
% 1.18/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/1.03  --bmc1_out_stat                         full
% 1.18/1.03  --bmc1_ground_init                      false
% 1.18/1.03  --bmc1_pre_inst_next_state              false
% 1.18/1.03  --bmc1_pre_inst_state                   false
% 1.18/1.03  --bmc1_pre_inst_reach_state             false
% 1.18/1.03  --bmc1_out_unsat_core                   false
% 1.18/1.03  --bmc1_aig_witness_out                  false
% 1.18/1.03  --bmc1_verbose                          false
% 1.18/1.03  --bmc1_dump_clauses_tptp                false
% 1.18/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.18/1.03  --bmc1_dump_file                        -
% 1.18/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.18/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.18/1.03  --bmc1_ucm_extend_mode                  1
% 1.18/1.03  --bmc1_ucm_init_mode                    2
% 1.18/1.03  --bmc1_ucm_cone_mode                    none
% 1.18/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.18/1.03  --bmc1_ucm_relax_model                  4
% 1.18/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.18/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/1.03  --bmc1_ucm_layered_model                none
% 1.18/1.03  --bmc1_ucm_max_lemma_size               10
% 1.18/1.03  
% 1.18/1.03  ------ AIG Options
% 1.18/1.03  
% 1.18/1.03  --aig_mode                              false
% 1.18/1.03  
% 1.18/1.03  ------ Instantiation Options
% 1.18/1.03  
% 1.18/1.03  --instantiation_flag                    true
% 1.18/1.03  --inst_sos_flag                         false
% 1.18/1.03  --inst_sos_phase                        true
% 1.18/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/1.03  --inst_lit_sel_side                     num_symb
% 1.18/1.03  --inst_solver_per_active                1400
% 1.18/1.03  --inst_solver_calls_frac                1.
% 1.18/1.03  --inst_passive_queue_type               priority_queues
% 1.18/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/1.03  --inst_passive_queues_freq              [25;2]
% 1.18/1.03  --inst_dismatching                      true
% 1.18/1.03  --inst_eager_unprocessed_to_passive     true
% 1.18/1.03  --inst_prop_sim_given                   true
% 1.18/1.03  --inst_prop_sim_new                     false
% 1.18/1.03  --inst_subs_new                         false
% 1.18/1.03  --inst_eq_res_simp                      false
% 1.18/1.03  --inst_subs_given                       false
% 1.18/1.03  --inst_orphan_elimination               true
% 1.18/1.03  --inst_learning_loop_flag               true
% 1.18/1.03  --inst_learning_start                   3000
% 1.18/1.03  --inst_learning_factor                  2
% 1.18/1.03  --inst_start_prop_sim_after_learn       3
% 1.18/1.03  --inst_sel_renew                        solver
% 1.18/1.03  --inst_lit_activity_flag                true
% 1.18/1.03  --inst_restr_to_given                   false
% 1.18/1.03  --inst_activity_threshold               500
% 1.18/1.03  --inst_out_proof                        true
% 1.18/1.03  
% 1.18/1.03  ------ Resolution Options
% 1.18/1.03  
% 1.18/1.03  --resolution_flag                       true
% 1.18/1.03  --res_lit_sel                           adaptive
% 1.18/1.03  --res_lit_sel_side                      none
% 1.18/1.03  --res_ordering                          kbo
% 1.18/1.03  --res_to_prop_solver                    active
% 1.18/1.03  --res_prop_simpl_new                    false
% 1.18/1.03  --res_prop_simpl_given                  true
% 1.18/1.03  --res_passive_queue_type                priority_queues
% 1.18/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/1.03  --res_passive_queues_freq               [15;5]
% 1.18/1.03  --res_forward_subs                      full
% 1.18/1.03  --res_backward_subs                     full
% 1.18/1.03  --res_forward_subs_resolution           true
% 1.18/1.03  --res_backward_subs_resolution          true
% 1.18/1.03  --res_orphan_elimination                true
% 1.18/1.03  --res_time_limit                        2.
% 1.18/1.03  --res_out_proof                         true
% 1.18/1.03  
% 1.18/1.03  ------ Superposition Options
% 1.18/1.03  
% 1.18/1.03  --superposition_flag                    true
% 1.18/1.03  --sup_passive_queue_type                priority_queues
% 1.18/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.18/1.03  --demod_completeness_check              fast
% 1.18/1.03  --demod_use_ground                      true
% 1.18/1.03  --sup_to_prop_solver                    passive
% 1.18/1.03  --sup_prop_simpl_new                    true
% 1.18/1.03  --sup_prop_simpl_given                  true
% 1.18/1.03  --sup_fun_splitting                     false
% 1.18/1.03  --sup_smt_interval                      50000
% 1.18/1.03  
% 1.18/1.03  ------ Superposition Simplification Setup
% 1.18/1.03  
% 1.18/1.03  --sup_indices_passive                   []
% 1.18/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.03  --sup_full_bw                           [BwDemod]
% 1.18/1.03  --sup_immed_triv                        [TrivRules]
% 1.18/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.03  --sup_immed_bw_main                     []
% 1.18/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.03  
% 1.18/1.03  ------ Combination Options
% 1.18/1.03  
% 1.18/1.03  --comb_res_mult                         3
% 1.18/1.03  --comb_sup_mult                         2
% 1.18/1.03  --comb_inst_mult                        10
% 1.18/1.03  
% 1.18/1.03  ------ Debug Options
% 1.18/1.03  
% 1.18/1.03  --dbg_backtrace                         false
% 1.18/1.03  --dbg_dump_prop_clauses                 false
% 1.18/1.03  --dbg_dump_prop_clauses_file            -
% 1.18/1.03  --dbg_out_stat                          false
% 1.18/1.03  ------ Parsing...
% 1.18/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.18/1.03  
% 1.18/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.18/1.03  
% 1.18/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.18/1.03  
% 1.18/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.18/1.03  ------ Proving...
% 1.18/1.03  ------ Problem Properties 
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  clauses                                 14
% 1.18/1.03  conjectures                             5
% 1.18/1.03  EPR                                     4
% 1.18/1.03  Horn                                    10
% 1.18/1.03  unary                                   1
% 1.18/1.03  binary                                  6
% 1.18/1.03  lits                                    38
% 1.18/1.03  lits eq                                 12
% 1.18/1.03  fd_pure                                 0
% 1.18/1.03  fd_pseudo                               0
% 1.18/1.03  fd_cond                                 0
% 1.18/1.03  fd_pseudo_cond                          2
% 1.18/1.03  AC symbols                              0
% 1.18/1.03  
% 1.18/1.03  ------ Schedule dynamic 5 is on 
% 1.18/1.03  
% 1.18/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  ------ 
% 1.18/1.03  Current options:
% 1.18/1.03  ------ 
% 1.18/1.03  
% 1.18/1.03  ------ Input Options
% 1.18/1.03  
% 1.18/1.03  --out_options                           all
% 1.18/1.03  --tptp_safe_out                         true
% 1.18/1.03  --problem_path                          ""
% 1.18/1.03  --include_path                          ""
% 1.18/1.03  --clausifier                            res/vclausify_rel
% 1.18/1.03  --clausifier_options                    --mode clausify
% 1.18/1.03  --stdin                                 false
% 1.18/1.03  --stats_out                             all
% 1.18/1.03  
% 1.18/1.03  ------ General Options
% 1.18/1.03  
% 1.18/1.03  --fof                                   false
% 1.18/1.03  --time_out_real                         305.
% 1.18/1.03  --time_out_virtual                      -1.
% 1.18/1.03  --symbol_type_check                     false
% 1.18/1.03  --clausify_out                          false
% 1.18/1.03  --sig_cnt_out                           false
% 1.18/1.03  --trig_cnt_out                          false
% 1.18/1.03  --trig_cnt_out_tolerance                1.
% 1.18/1.03  --trig_cnt_out_sk_spl                   false
% 1.18/1.03  --abstr_cl_out                          false
% 1.18/1.03  
% 1.18/1.03  ------ Global Options
% 1.18/1.03  
% 1.18/1.03  --schedule                              default
% 1.18/1.03  --add_important_lit                     false
% 1.18/1.03  --prop_solver_per_cl                    1000
% 1.18/1.03  --min_unsat_core                        false
% 1.18/1.03  --soft_assumptions                      false
% 1.18/1.03  --soft_lemma_size                       3
% 1.18/1.03  --prop_impl_unit_size                   0
% 1.18/1.03  --prop_impl_unit                        []
% 1.18/1.03  --share_sel_clauses                     true
% 1.18/1.03  --reset_solvers                         false
% 1.18/1.03  --bc_imp_inh                            [conj_cone]
% 1.18/1.03  --conj_cone_tolerance                   3.
% 1.18/1.03  --extra_neg_conj                        none
% 1.18/1.03  --large_theory_mode                     true
% 1.18/1.03  --prolific_symb_bound                   200
% 1.18/1.03  --lt_threshold                          2000
% 1.18/1.03  --clause_weak_htbl                      true
% 1.18/1.03  --gc_record_bc_elim                     false
% 1.18/1.03  
% 1.18/1.03  ------ Preprocessing Options
% 1.18/1.03  
% 1.18/1.03  --preprocessing_flag                    true
% 1.18/1.03  --time_out_prep_mult                    0.1
% 1.18/1.03  --splitting_mode                        input
% 1.18/1.03  --splitting_grd                         true
% 1.18/1.03  --splitting_cvd                         false
% 1.18/1.03  --splitting_cvd_svl                     false
% 1.18/1.03  --splitting_nvd                         32
% 1.18/1.03  --sub_typing                            true
% 1.18/1.03  --prep_gs_sim                           true
% 1.18/1.03  --prep_unflatten                        true
% 1.18/1.03  --prep_res_sim                          true
% 1.18/1.03  --prep_upred                            true
% 1.18/1.03  --prep_sem_filter                       exhaustive
% 1.18/1.03  --prep_sem_filter_out                   false
% 1.18/1.03  --pred_elim                             true
% 1.18/1.03  --res_sim_input                         true
% 1.18/1.03  --eq_ax_congr_red                       true
% 1.18/1.03  --pure_diseq_elim                       true
% 1.18/1.03  --brand_transform                       false
% 1.18/1.03  --non_eq_to_eq                          false
% 1.18/1.03  --prep_def_merge                        true
% 1.18/1.03  --prep_def_merge_prop_impl              false
% 1.18/1.03  --prep_def_merge_mbd                    true
% 1.18/1.03  --prep_def_merge_tr_red                 false
% 1.18/1.03  --prep_def_merge_tr_cl                  false
% 1.18/1.03  --smt_preprocessing                     true
% 1.18/1.03  --smt_ac_axioms                         fast
% 1.18/1.03  --preprocessed_out                      false
% 1.18/1.03  --preprocessed_stats                    false
% 1.18/1.03  
% 1.18/1.03  ------ Abstraction refinement Options
% 1.18/1.03  
% 1.18/1.03  --abstr_ref                             []
% 1.18/1.03  --abstr_ref_prep                        false
% 1.18/1.03  --abstr_ref_until_sat                   false
% 1.18/1.03  --abstr_ref_sig_restrict                funpre
% 1.18/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/1.03  --abstr_ref_under                       []
% 1.18/1.03  
% 1.18/1.03  ------ SAT Options
% 1.18/1.03  
% 1.18/1.03  --sat_mode                              false
% 1.18/1.03  --sat_fm_restart_options                ""
% 1.18/1.03  --sat_gr_def                            false
% 1.18/1.03  --sat_epr_types                         true
% 1.18/1.03  --sat_non_cyclic_types                  false
% 1.18/1.03  --sat_finite_models                     false
% 1.18/1.03  --sat_fm_lemmas                         false
% 1.18/1.03  --sat_fm_prep                           false
% 1.18/1.03  --sat_fm_uc_incr                        true
% 1.18/1.03  --sat_out_model                         small
% 1.18/1.03  --sat_out_clauses                       false
% 1.18/1.03  
% 1.18/1.03  ------ QBF Options
% 1.18/1.03  
% 1.18/1.03  --qbf_mode                              false
% 1.18/1.03  --qbf_elim_univ                         false
% 1.18/1.03  --qbf_dom_inst                          none
% 1.18/1.03  --qbf_dom_pre_inst                      false
% 1.18/1.03  --qbf_sk_in                             false
% 1.18/1.03  --qbf_pred_elim                         true
% 1.18/1.03  --qbf_split                             512
% 1.18/1.03  
% 1.18/1.03  ------ BMC1 Options
% 1.18/1.03  
% 1.18/1.03  --bmc1_incremental                      false
% 1.18/1.03  --bmc1_axioms                           reachable_all
% 1.18/1.03  --bmc1_min_bound                        0
% 1.18/1.03  --bmc1_max_bound                        -1
% 1.18/1.03  --bmc1_max_bound_default                -1
% 1.18/1.03  --bmc1_symbol_reachability              true
% 1.18/1.03  --bmc1_property_lemmas                  false
% 1.18/1.03  --bmc1_k_induction                      false
% 1.18/1.03  --bmc1_non_equiv_states                 false
% 1.18/1.03  --bmc1_deadlock                         false
% 1.18/1.03  --bmc1_ucm                              false
% 1.18/1.03  --bmc1_add_unsat_core                   none
% 1.18/1.03  --bmc1_unsat_core_children              false
% 1.18/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/1.03  --bmc1_out_stat                         full
% 1.18/1.03  --bmc1_ground_init                      false
% 1.18/1.03  --bmc1_pre_inst_next_state              false
% 1.18/1.03  --bmc1_pre_inst_state                   false
% 1.18/1.03  --bmc1_pre_inst_reach_state             false
% 1.18/1.03  --bmc1_out_unsat_core                   false
% 1.18/1.03  --bmc1_aig_witness_out                  false
% 1.18/1.03  --bmc1_verbose                          false
% 1.18/1.03  --bmc1_dump_clauses_tptp                false
% 1.18/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.18/1.03  --bmc1_dump_file                        -
% 1.18/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.18/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.18/1.03  --bmc1_ucm_extend_mode                  1
% 1.18/1.03  --bmc1_ucm_init_mode                    2
% 1.18/1.03  --bmc1_ucm_cone_mode                    none
% 1.18/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.18/1.03  --bmc1_ucm_relax_model                  4
% 1.18/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.18/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/1.03  --bmc1_ucm_layered_model                none
% 1.18/1.03  --bmc1_ucm_max_lemma_size               10
% 1.18/1.03  
% 1.18/1.03  ------ AIG Options
% 1.18/1.03  
% 1.18/1.03  --aig_mode                              false
% 1.18/1.03  
% 1.18/1.03  ------ Instantiation Options
% 1.18/1.03  
% 1.18/1.03  --instantiation_flag                    true
% 1.18/1.03  --inst_sos_flag                         false
% 1.18/1.03  --inst_sos_phase                        true
% 1.18/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/1.03  --inst_lit_sel_side                     none
% 1.18/1.03  --inst_solver_per_active                1400
% 1.18/1.03  --inst_solver_calls_frac                1.
% 1.18/1.03  --inst_passive_queue_type               priority_queues
% 1.18/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/1.03  --inst_passive_queues_freq              [25;2]
% 1.18/1.03  --inst_dismatching                      true
% 1.18/1.03  --inst_eager_unprocessed_to_passive     true
% 1.18/1.03  --inst_prop_sim_given                   true
% 1.18/1.03  --inst_prop_sim_new                     false
% 1.18/1.03  --inst_subs_new                         false
% 1.18/1.03  --inst_eq_res_simp                      false
% 1.18/1.03  --inst_subs_given                       false
% 1.18/1.03  --inst_orphan_elimination               true
% 1.18/1.03  --inst_learning_loop_flag               true
% 1.18/1.03  --inst_learning_start                   3000
% 1.18/1.03  --inst_learning_factor                  2
% 1.18/1.03  --inst_start_prop_sim_after_learn       3
% 1.18/1.03  --inst_sel_renew                        solver
% 1.18/1.03  --inst_lit_activity_flag                true
% 1.18/1.03  --inst_restr_to_given                   false
% 1.18/1.03  --inst_activity_threshold               500
% 1.18/1.03  --inst_out_proof                        true
% 1.18/1.03  
% 1.18/1.03  ------ Resolution Options
% 1.18/1.03  
% 1.18/1.03  --resolution_flag                       false
% 1.18/1.03  --res_lit_sel                           adaptive
% 1.18/1.03  --res_lit_sel_side                      none
% 1.18/1.03  --res_ordering                          kbo
% 1.18/1.03  --res_to_prop_solver                    active
% 1.18/1.03  --res_prop_simpl_new                    false
% 1.18/1.03  --res_prop_simpl_given                  true
% 1.18/1.03  --res_passive_queue_type                priority_queues
% 1.18/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/1.03  --res_passive_queues_freq               [15;5]
% 1.18/1.03  --res_forward_subs                      full
% 1.18/1.03  --res_backward_subs                     full
% 1.18/1.03  --res_forward_subs_resolution           true
% 1.18/1.03  --res_backward_subs_resolution          true
% 1.18/1.03  --res_orphan_elimination                true
% 1.18/1.03  --res_time_limit                        2.
% 1.18/1.03  --res_out_proof                         true
% 1.18/1.03  
% 1.18/1.03  ------ Superposition Options
% 1.18/1.03  
% 1.18/1.03  --superposition_flag                    true
% 1.18/1.03  --sup_passive_queue_type                priority_queues
% 1.18/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.18/1.03  --demod_completeness_check              fast
% 1.18/1.03  --demod_use_ground                      true
% 1.18/1.03  --sup_to_prop_solver                    passive
% 1.18/1.03  --sup_prop_simpl_new                    true
% 1.18/1.03  --sup_prop_simpl_given                  true
% 1.18/1.03  --sup_fun_splitting                     false
% 1.18/1.03  --sup_smt_interval                      50000
% 1.18/1.03  
% 1.18/1.03  ------ Superposition Simplification Setup
% 1.18/1.03  
% 1.18/1.03  --sup_indices_passive                   []
% 1.18/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.03  --sup_full_bw                           [BwDemod]
% 1.18/1.03  --sup_immed_triv                        [TrivRules]
% 1.18/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.03  --sup_immed_bw_main                     []
% 1.18/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.03  
% 1.18/1.03  ------ Combination Options
% 1.18/1.03  
% 1.18/1.03  --comb_res_mult                         3
% 1.18/1.03  --comb_sup_mult                         2
% 1.18/1.03  --comb_inst_mult                        10
% 1.18/1.03  
% 1.18/1.03  ------ Debug Options
% 1.18/1.03  
% 1.18/1.03  --dbg_backtrace                         false
% 1.18/1.03  --dbg_dump_prop_clauses                 false
% 1.18/1.03  --dbg_dump_prop_clauses_file            -
% 1.18/1.03  --dbg_out_stat                          false
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  ------ Proving...
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  % SZS status Theorem for theBenchmark.p
% 1.18/1.03  
% 1.18/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.18/1.03  
% 1.18/1.03  fof(f1,axiom,(
% 1.18/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.18/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.03  
% 1.18/1.03  fof(f7,plain,(
% 1.18/1.03    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.18/1.03    inference(ennf_transformation,[],[f1])).
% 1.18/1.03  
% 1.18/1.03  fof(f8,plain,(
% 1.18/1.03    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.18/1.03    inference(flattening,[],[f7])).
% 1.18/1.03  
% 1.18/1.03  fof(f15,plain,(
% 1.18/1.03    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.18/1.03    inference(nnf_transformation,[],[f8])).
% 1.18/1.03  
% 1.18/1.03  fof(f16,plain,(
% 1.18/1.03    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.18/1.03    inference(rectify,[],[f15])).
% 1.18/1.03  
% 1.18/1.03  fof(f17,plain,(
% 1.18/1.03    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 1.18/1.03    introduced(choice_axiom,[])).
% 1.18/1.03  
% 1.18/1.03  fof(f18,plain,(
% 1.18/1.03    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.18/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.18/1.03  
% 1.18/1.03  fof(f26,plain,(
% 1.18/1.03    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.18/1.03    inference(cnf_transformation,[],[f18])).
% 1.18/1.03  
% 1.18/1.03  fof(f5,conjecture,(
% 1.18/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.18/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.03  
% 1.18/1.03  fof(f6,negated_conjecture,(
% 1.18/1.03    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.18/1.03    inference(negated_conjecture,[],[f5])).
% 1.18/1.03  
% 1.18/1.03  fof(f13,plain,(
% 1.18/1.03    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.18/1.03    inference(ennf_transformation,[],[f6])).
% 1.18/1.03  
% 1.18/1.03  fof(f14,plain,(
% 1.18/1.03    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.18/1.03    inference(flattening,[],[f13])).
% 1.18/1.03  
% 1.18/1.03  fof(f19,plain,(
% 1.18/1.03    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.18/1.03    inference(nnf_transformation,[],[f14])).
% 1.18/1.03  
% 1.18/1.03  fof(f20,plain,(
% 1.18/1.03    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.18/1.03    inference(flattening,[],[f19])).
% 1.18/1.03  
% 1.18/1.03  fof(f21,plain,(
% 1.18/1.03    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.18/1.03    inference(rectify,[],[f20])).
% 1.18/1.03  
% 1.18/1.03  fof(f23,plain,(
% 1.18/1.03    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 1.18/1.03    introduced(choice_axiom,[])).
% 1.18/1.03  
% 1.18/1.03  fof(f22,plain,(
% 1.18/1.03    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 1.18/1.03    introduced(choice_axiom,[])).
% 1.18/1.03  
% 1.18/1.03  fof(f24,plain,(
% 1.18/1.03    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 1.18/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f23,f22])).
% 1.18/1.03  
% 1.18/1.03  fof(f33,plain,(
% 1.18/1.03    v1_funct_1(sK3)),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  fof(f27,plain,(
% 1.18/1.03    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.18/1.03    inference(cnf_transformation,[],[f18])).
% 1.18/1.03  
% 1.18/1.03  fof(f2,axiom,(
% 1.18/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.18/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.03  
% 1.18/1.03  fof(f9,plain,(
% 1.18/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/1.03    inference(ennf_transformation,[],[f2])).
% 1.18/1.03  
% 1.18/1.03  fof(f30,plain,(
% 1.18/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.18/1.03    inference(cnf_transformation,[],[f9])).
% 1.18/1.03  
% 1.18/1.03  fof(f35,plain,(
% 1.18/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  fof(f28,plain,(
% 1.18/1.03    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.18/1.03    inference(cnf_transformation,[],[f18])).
% 1.18/1.03  
% 1.18/1.03  fof(f29,plain,(
% 1.18/1.03    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.18/1.03    inference(cnf_transformation,[],[f18])).
% 1.18/1.03  
% 1.18/1.03  fof(f3,axiom,(
% 1.18/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.18/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.03  
% 1.18/1.03  fof(f10,plain,(
% 1.18/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.18/1.03    inference(ennf_transformation,[],[f3])).
% 1.18/1.03  
% 1.18/1.03  fof(f31,plain,(
% 1.18/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.18/1.03    inference(cnf_transformation,[],[f10])).
% 1.18/1.03  
% 1.18/1.03  fof(f4,axiom,(
% 1.18/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.18/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.03  
% 1.18/1.03  fof(f11,plain,(
% 1.18/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.18/1.03    inference(ennf_transformation,[],[f4])).
% 1.18/1.03  
% 1.18/1.03  fof(f12,plain,(
% 1.18/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.18/1.03    inference(flattening,[],[f11])).
% 1.18/1.03  
% 1.18/1.03  fof(f32,plain,(
% 1.18/1.03    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.18/1.03    inference(cnf_transformation,[],[f12])).
% 1.18/1.03  
% 1.18/1.03  fof(f34,plain,(
% 1.18/1.03    v1_funct_2(sK3,sK2,sK2)),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  fof(f36,plain,(
% 1.18/1.03    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  fof(f39,plain,(
% 1.18/1.03    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  fof(f25,plain,(
% 1.18/1.03    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.18/1.03    inference(cnf_transformation,[],[f18])).
% 1.18/1.03  
% 1.18/1.03  fof(f40,plain,(
% 1.18/1.03    sK4 != sK5 | ~v2_funct_1(sK3)),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  fof(f38,plain,(
% 1.18/1.03    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  fof(f37,plain,(
% 1.18/1.03    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 1.18/1.03    inference(cnf_transformation,[],[f24])).
% 1.18/1.03  
% 1.18/1.03  cnf(c_3,plain,
% 1.18/1.03      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.18/1.03      | ~ v1_relat_1(X0)
% 1.18/1.03      | ~ v1_funct_1(X0)
% 1.18/1.03      | v2_funct_1(X0) ),
% 1.18/1.03      inference(cnf_transformation,[],[f26]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_15,negated_conjecture,
% 1.18/1.03      ( v1_funct_1(sK3) ),
% 1.18/1.03      inference(cnf_transformation,[],[f33]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_214,plain,
% 1.18/1.03      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.18/1.03      | ~ v1_relat_1(X0)
% 1.18/1.03      | v2_funct_1(X0)
% 1.18/1.03      | sK3 != X0 ),
% 1.18/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_215,plain,
% 1.18/1.03      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.18/1.03      | ~ v1_relat_1(sK3)
% 1.18/1.03      | v2_funct_1(sK3) ),
% 1.18/1.03      inference(unflattening,[status(thm)],[c_214]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1561,plain,
% 1.18/1.03      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.18/1.03      | ~ v1_relat_1(sK3)
% 1.18/1.03      | v2_funct_1(sK3) ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_215]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1798,plain,
% 1.18/1.03      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.18/1.03      | v1_relat_1(sK3) != iProver_top
% 1.18/1.03      | v2_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_16,plain,
% 1.18/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_38,plain,
% 1.18/1.03      ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
% 1.18/1.03      | v1_relat_1(X0) != iProver_top
% 1.18/1.03      | v1_funct_1(X0) != iProver_top
% 1.18/1.03      | v2_funct_1(X0) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_40,plain,
% 1.18/1.03      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 1.18/1.03      | v1_relat_1(sK3) != iProver_top
% 1.18/1.03      | v1_funct_1(sK3) != iProver_top
% 1.18/1.03      | v2_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_38]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2,plain,
% 1.18/1.03      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.18/1.03      | ~ v1_relat_1(X0)
% 1.18/1.03      | ~ v1_funct_1(X0)
% 1.18/1.03      | v2_funct_1(X0) ),
% 1.18/1.03      inference(cnf_transformation,[],[f27]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_41,plain,
% 1.18/1.03      ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
% 1.18/1.03      | v1_relat_1(X0) != iProver_top
% 1.18/1.03      | v1_funct_1(X0) != iProver_top
% 1.18/1.03      | v2_funct_1(X0) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_43,plain,
% 1.18/1.03      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 1.18/1.03      | v1_relat_1(sK3) != iProver_top
% 1.18/1.03      | v1_funct_1(sK3) != iProver_top
% 1.18/1.03      | v2_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_41]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1574,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1594,plain,
% 1.18/1.03      ( sK2 = sK2 ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1574]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_5,plain,
% 1.18/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.18/1.03      | v1_relat_1(X0) ),
% 1.18/1.03      inference(cnf_transformation,[],[f30]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_13,negated_conjecture,
% 1.18/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.18/1.03      inference(cnf_transformation,[],[f35]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_197,plain,
% 1.18/1.03      ( v1_relat_1(X0)
% 1.18/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.18/1.03      | sK3 != X0 ),
% 1.18/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_198,plain,
% 1.18/1.03      ( v1_relat_1(sK3)
% 1.18/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.18/1.03      inference(unflattening,[status(thm)],[c_197]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1562,plain,
% 1.18/1.03      ( v1_relat_1(sK3)
% 1.18/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_198]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1604,plain,
% 1.18/1.03      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.18/1.03      | v1_relat_1(sK3) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1562]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1606,plain,
% 1.18/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.18/1.03      | v1_relat_1(sK3) = iProver_top ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1604]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1,plain,
% 1.18/1.03      ( ~ v1_relat_1(X0)
% 1.18/1.03      | ~ v1_funct_1(X0)
% 1.18/1.03      | v2_funct_1(X0)
% 1.18/1.03      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 1.18/1.03      inference(cnf_transformation,[],[f28]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_240,plain,
% 1.18/1.03      ( ~ v1_relat_1(X0)
% 1.18/1.03      | v2_funct_1(X0)
% 1.18/1.03      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 1.18/1.03      | sK3 != X0 ),
% 1.18/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_241,plain,
% 1.18/1.03      ( ~ v1_relat_1(sK3)
% 1.18/1.03      | v2_funct_1(sK3)
% 1.18/1.03      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 1.18/1.03      inference(unflattening,[status(thm)],[c_240]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1559,plain,
% 1.18/1.03      ( ~ v1_relat_1(sK3)
% 1.18/1.03      | v2_funct_1(sK3)
% 1.18/1.03      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_241]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1609,plain,
% 1.18/1.03      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 1.18/1.03      | v1_relat_1(sK3) != iProver_top
% 1.18/1.03      | v2_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_0,plain,
% 1.18/1.03      ( ~ v1_relat_1(X0)
% 1.18/1.03      | ~ v1_funct_1(X0)
% 1.18/1.03      | v2_funct_1(X0)
% 1.18/1.03      | sK1(X0) != sK0(X0) ),
% 1.18/1.03      inference(cnf_transformation,[],[f29]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_253,plain,
% 1.18/1.03      ( ~ v1_relat_1(X0)
% 1.18/1.03      | v2_funct_1(X0)
% 1.18/1.03      | sK1(X0) != sK0(X0)
% 1.18/1.03      | sK3 != X0 ),
% 1.18/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_254,plain,
% 1.18/1.03      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 1.18/1.03      inference(unflattening,[status(thm)],[c_253]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1558,plain,
% 1.18/1.03      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_254]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1610,plain,
% 1.18/1.03      ( sK1(sK3) != sK0(sK3)
% 1.18/1.03      | v1_relat_1(sK3) != iProver_top
% 1.18/1.03      | v2_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1576,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1909,plain,
% 1.18/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1576]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_6,plain,
% 1.18/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.18/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.18/1.03      inference(cnf_transformation,[],[f31]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_188,plain,
% 1.18/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.18/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.18/1.03      | sK3 != X2 ),
% 1.18/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_189,plain,
% 1.18/1.03      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.18/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.18/1.03      inference(unflattening,[status(thm)],[c_188]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1563,plain,
% 1.18/1.03      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.18/1.03      | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_189]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1927,plain,
% 1.18/1.03      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 1.18/1.03      inference(equality_resolution,[status(thm)],[c_1563]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_7,plain,
% 1.18/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 1.18/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.18/1.03      | ~ v1_funct_1(X0)
% 1.18/1.03      | k1_relset_1(X1,X1,X0) = X1 ),
% 1.18/1.03      inference(cnf_transformation,[],[f32]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_14,negated_conjecture,
% 1.18/1.03      ( v1_funct_2(sK3,sK2,sK2) ),
% 1.18/1.03      inference(cnf_transformation,[],[f34]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_179,plain,
% 1.18/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.18/1.03      | ~ v1_funct_1(X0)
% 1.18/1.03      | k1_relset_1(X1,X1,X0) = X1
% 1.18/1.03      | sK2 != X1
% 1.18/1.03      | sK3 != X0 ),
% 1.18/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_180,plain,
% 1.18/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 1.18/1.03      | ~ v1_funct_1(sK3)
% 1.18/1.03      | k1_relset_1(sK2,sK2,sK3) = sK2 ),
% 1.18/1.03      inference(unflattening,[status(thm)],[c_179]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_182,plain,
% 1.18/1.03      ( k1_relset_1(sK2,sK2,sK3) = sK2 ),
% 1.18/1.03      inference(global_propositional_subsumption,
% 1.18/1.03                [status(thm)],
% 1.18/1.03                [c_180,c_15,c_13]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1564,plain,
% 1.18/1.03      ( k1_relset_1(sK2,sK2,sK3) = sK2 ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_182]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1928,plain,
% 1.18/1.03      ( k1_relat_1(sK3) = sK2 ),
% 1.18/1.03      inference(light_normalisation,[status(thm)],[c_1927,c_1564]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_12,negated_conjecture,
% 1.18/1.03      ( ~ r2_hidden(X0,sK2)
% 1.18/1.03      | ~ r2_hidden(X1,sK2)
% 1.18/1.03      | v2_funct_1(sK3)
% 1.18/1.03      | X1 = X0
% 1.18/1.03      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 1.18/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1565,negated_conjecture,
% 1.18/1.03      ( ~ r2_hidden(X0_45,sK2)
% 1.18/1.03      | ~ r2_hidden(X1_45,sK2)
% 1.18/1.03      | v2_funct_1(sK3)
% 1.18/1.03      | k1_funct_1(sK3,X1_45) != k1_funct_1(sK3,X0_45)
% 1.18/1.03      | X1_45 = X0_45 ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1929,plain,
% 1.18/1.03      ( ~ r2_hidden(sK1(sK3),sK2)
% 1.18/1.03      | ~ r2_hidden(sK0(sK3),sK2)
% 1.18/1.03      | v2_funct_1(sK3)
% 1.18/1.03      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 1.18/1.03      | sK1(sK3) = sK0(sK3) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1565]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1930,plain,
% 1.18/1.03      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 1.18/1.03      | sK1(sK3) = sK0(sK3)
% 1.18/1.03      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 1.18/1.03      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 1.18/1.03      | v2_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1573,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1960,plain,
% 1.18/1.03      ( sK1(sK3) = sK1(sK3) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1573]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1579,plain,
% 1.18/1.03      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 1.18/1.03      theory(equality) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1973,plain,
% 1.18/1.03      ( X0_46 != X1_46
% 1.18/1.03      | X0_46 = k1_relat_1(sK3)
% 1.18/1.03      | k1_relat_1(sK3) != X1_46 ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1579]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1974,plain,
% 1.18/1.03      ( k1_relat_1(sK3) != sK2 | sK2 = k1_relat_1(sK3) | sK2 != sK2 ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1973]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1583,plain,
% 1.18/1.03      ( ~ r2_hidden(X0_45,X0_46)
% 1.18/1.03      | r2_hidden(X1_45,X1_46)
% 1.18/1.03      | X1_46 != X0_46
% 1.18/1.03      | X1_45 != X0_45 ),
% 1.18/1.03      theory(equality) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1934,plain,
% 1.18/1.03      ( r2_hidden(X0_45,X0_46)
% 1.18/1.03      | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 1.18/1.03      | X0_46 != k1_relat_1(sK3)
% 1.18/1.03      | X0_45 != sK1(sK3) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1583]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2019,plain,
% 1.18/1.03      ( r2_hidden(sK1(sK3),X0_46)
% 1.18/1.03      | ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 1.18/1.03      | X0_46 != k1_relat_1(sK3)
% 1.18/1.03      | sK1(sK3) != sK1(sK3) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1934]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2020,plain,
% 1.18/1.03      ( X0_46 != k1_relat_1(sK3)
% 1.18/1.03      | sK1(sK3) != sK1(sK3)
% 1.18/1.03      | r2_hidden(sK1(sK3),X0_46) = iProver_top
% 1.18/1.03      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_2019]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2022,plain,
% 1.18/1.03      ( sK2 != k1_relat_1(sK3)
% 1.18/1.03      | sK1(sK3) != sK1(sK3)
% 1.18/1.03      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | r2_hidden(sK1(sK3),sK2) = iProver_top ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_2020]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1939,plain,
% 1.18/1.03      ( r2_hidden(X0_45,X0_46)
% 1.18/1.03      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.18/1.03      | X0_46 != k1_relat_1(sK3)
% 1.18/1.03      | X0_45 != sK0(sK3) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1583]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2029,plain,
% 1.18/1.03      ( r2_hidden(sK0(sK3),X0_46)
% 1.18/1.03      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 1.18/1.03      | X0_46 != k1_relat_1(sK3)
% 1.18/1.03      | sK0(sK3) != sK0(sK3) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1939]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2031,plain,
% 1.18/1.03      ( X0_46 != k1_relat_1(sK3)
% 1.18/1.03      | sK0(sK3) != sK0(sK3)
% 1.18/1.03      | r2_hidden(sK0(sK3),X0_46) = iProver_top
% 1.18/1.03      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_2029]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2033,plain,
% 1.18/1.03      ( sK2 != k1_relat_1(sK3)
% 1.18/1.03      | sK0(sK3) != sK0(sK3)
% 1.18/1.03      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | r2_hidden(sK0(sK3),sK2) = iProver_top ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_2031]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2030,plain,
% 1.18/1.03      ( sK0(sK3) = sK0(sK3) ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1573]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2051,plain,
% 1.18/1.03      ( v2_funct_1(sK3) = iProver_top ),
% 1.18/1.03      inference(global_propositional_subsumption,
% 1.18/1.03                [status(thm)],
% 1.18/1.03                [c_1798,c_16,c_40,c_43,c_1594,c_1606,c_1609,c_1610,
% 1.18/1.03                 c_1909,c_1928,c_1930,c_1960,c_1974,c_2022,c_2033,c_2030]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_9,negated_conjecture,
% 1.18/1.03      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.18/1.03      inference(cnf_transformation,[],[f39]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1568,negated_conjecture,
% 1.18/1.03      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1793,plain,
% 1.18/1.03      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 1.18/1.03      | v2_funct_1(sK3) != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2056,plain,
% 1.18/1.03      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 1.18/1.03      inference(superposition,[status(thm)],[c_2051,c_1793]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_4,plain,
% 1.18/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.18/1.03      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.18/1.03      | ~ v1_relat_1(X1)
% 1.18/1.03      | ~ v1_funct_1(X1)
% 1.18/1.03      | ~ v2_funct_1(X1)
% 1.18/1.03      | X0 = X2
% 1.18/1.03      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 1.18/1.03      inference(cnf_transformation,[],[f25]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_266,plain,
% 1.18/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.18/1.03      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.18/1.03      | ~ v1_relat_1(X1)
% 1.18/1.03      | ~ v2_funct_1(X1)
% 1.18/1.03      | X2 = X0
% 1.18/1.03      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 1.18/1.03      | sK3 != X1 ),
% 1.18/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_267,plain,
% 1.18/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.18/1.03      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.18/1.03      | ~ v1_relat_1(sK3)
% 1.18/1.03      | ~ v2_funct_1(sK3)
% 1.18/1.03      | X0 = X1
% 1.18/1.03      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.18/1.03      inference(unflattening,[status(thm)],[c_266]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1557,plain,
% 1.18/1.03      ( ~ r2_hidden(X0_45,k1_relat_1(sK3))
% 1.18/1.03      | ~ r2_hidden(X1_45,k1_relat_1(sK3))
% 1.18/1.03      | ~ v1_relat_1(sK3)
% 1.18/1.03      | ~ v2_funct_1(sK3)
% 1.18/1.03      | k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
% 1.18/1.03      | X0_45 = X1_45 ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_267]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1570,plain,
% 1.18/1.03      ( ~ r2_hidden(X0_45,k1_relat_1(sK3))
% 1.18/1.03      | ~ r2_hidden(X1_45,k1_relat_1(sK3))
% 1.18/1.03      | k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
% 1.18/1.03      | X0_45 = X1_45
% 1.18/1.03      | ~ sP0_iProver_split ),
% 1.18/1.03      inference(splitting,
% 1.18/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.18/1.03                [c_1557]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1803,plain,
% 1.18/1.03      ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
% 1.18/1.03      | X0_45 = X1_45
% 1.18/1.03      | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | sP0_iProver_split != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1570]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1571,plain,
% 1.18/1.03      ( ~ v1_relat_1(sK3) | ~ v2_funct_1(sK3) | sP0_iProver_split ),
% 1.18/1.03      inference(splitting,
% 1.18/1.03                [splitting(split),new_symbols(definition,[])],
% 1.18/1.03                [c_1557]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1611,plain,
% 1.18/1.03      ( v1_relat_1(sK3) != iProver_top
% 1.18/1.03      | v2_funct_1(sK3) != iProver_top
% 1.18/1.03      | sP0_iProver_split = iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1612,plain,
% 1.18/1.03      ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
% 1.18/1.03      | X0_45 = X1_45
% 1.18/1.03      | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | sP0_iProver_split != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1570]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2155,plain,
% 1.18/1.03      ( r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | X0_45 = X1_45
% 1.18/1.03      | k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45) ),
% 1.18/1.03      inference(global_propositional_subsumption,
% 1.18/1.03                [status(thm)],
% 1.18/1.03                [c_1803,c_16,c_40,c_43,c_1594,c_1606,c_1609,c_1610,
% 1.18/1.03                 c_1611,c_1612,c_1909,c_1928,c_1930,c_1960,c_1974,c_2022,
% 1.18/1.03                 c_2033,c_2030]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2156,plain,
% 1.18/1.03      ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
% 1.18/1.03      | X0_45 = X1_45
% 1.18/1.03      | r2_hidden(X0_45,k1_relat_1(sK3)) != iProver_top
% 1.18/1.03      | r2_hidden(X1_45,k1_relat_1(sK3)) != iProver_top ),
% 1.18/1.03      inference(renaming,[status(thm)],[c_2155]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2159,plain,
% 1.18/1.03      ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,X1_45)
% 1.18/1.03      | X0_45 = X1_45
% 1.18/1.03      | r2_hidden(X0_45,sK2) != iProver_top
% 1.18/1.03      | r2_hidden(X1_45,sK2) != iProver_top ),
% 1.18/1.03      inference(light_normalisation,[status(thm)],[c_2156,c_1928]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2165,plain,
% 1.18/1.03      ( k1_funct_1(sK3,X0_45) != k1_funct_1(sK3,sK4)
% 1.18/1.03      | sK5 = X0_45
% 1.18/1.03      | r2_hidden(X0_45,sK2) != iProver_top
% 1.18/1.03      | r2_hidden(sK5,sK2) != iProver_top ),
% 1.18/1.03      inference(superposition,[status(thm)],[c_2056,c_2159]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2177,plain,
% 1.18/1.03      ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4)
% 1.18/1.03      | sK5 = sK4
% 1.18/1.03      | r2_hidden(sK5,sK2) != iProver_top
% 1.18/1.03      | r2_hidden(sK4,sK2) != iProver_top ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_2165]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1578,plain,
% 1.18/1.03      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.18/1.03      theory(equality) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2061,plain,
% 1.18/1.03      ( sK5 != X0_45 | sK4 != X0_45 | sK4 = sK5 ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1578]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_2062,plain,
% 1.18/1.03      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_2061]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_8,negated_conjecture,
% 1.18/1.03      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 1.18/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1569,negated_conjecture,
% 1.18/1.03      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 1.18/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1598,plain,
% 1.18/1.03      ( sK4 != sK5 | v2_funct_1(sK3) != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1593,plain,
% 1.18/1.03      ( sK4 = sK4 ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1573]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1582,plain,
% 1.18/1.03      ( k1_funct_1(X0_47,X0_45) = k1_funct_1(X0_47,X1_45)
% 1.18/1.03      | X0_45 != X1_45 ),
% 1.18/1.03      theory(equality) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_1587,plain,
% 1.18/1.03      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK4) | sK4 != sK4 ),
% 1.18/1.03      inference(instantiation,[status(thm)],[c_1582]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_10,negated_conjecture,
% 1.18/1.03      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 1.18/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_23,plain,
% 1.18/1.03      ( r2_hidden(sK5,sK2) = iProver_top
% 1.18/1.03      | v2_funct_1(sK3) != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_11,negated_conjecture,
% 1.18/1.03      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 1.18/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(c_22,plain,
% 1.18/1.03      ( r2_hidden(sK4,sK2) = iProver_top
% 1.18/1.03      | v2_funct_1(sK3) != iProver_top ),
% 1.18/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.18/1.03  
% 1.18/1.03  cnf(contradiction,plain,
% 1.18/1.03      ( $false ),
% 1.18/1.03      inference(minisat,
% 1.18/1.03                [status(thm)],
% 1.18/1.03                [c_2177,c_2062,c_2051,c_1598,c_1593,c_1587,c_23,c_22]) ).
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.18/1.03  
% 1.18/1.03  ------                               Statistics
% 1.18/1.03  
% 1.18/1.03  ------ General
% 1.18/1.03  
% 1.18/1.03  abstr_ref_over_cycles:                  0
% 1.18/1.03  abstr_ref_under_cycles:                 0
% 1.18/1.03  gc_basic_clause_elim:                   0
% 1.18/1.03  forced_gc_time:                         0
% 1.18/1.03  parsing_time:                           0.009
% 1.18/1.03  unif_index_cands_time:                  0.
% 1.18/1.03  unif_index_add_time:                    0.
% 1.18/1.03  orderings_time:                         0.
% 1.18/1.03  out_proof_time:                         0.02
% 1.18/1.03  total_time:                             0.119
% 1.18/1.03  num_of_symbols:                         52
% 1.18/1.03  num_of_terms:                           834
% 1.18/1.03  
% 1.18/1.03  ------ Preprocessing
% 1.18/1.03  
% 1.18/1.03  num_of_splits:                          1
% 1.18/1.03  num_of_split_atoms:                     1
% 1.18/1.03  num_of_reused_defs:                     0
% 1.18/1.03  num_eq_ax_congr_red:                    14
% 1.18/1.03  num_of_sem_filtered_clauses:            1
% 1.18/1.03  num_of_subtypes:                        6
% 1.18/1.03  monotx_restored_types:                  0
% 1.18/1.03  sat_num_of_epr_types:                   0
% 1.18/1.03  sat_num_of_non_cyclic_types:            0
% 1.18/1.03  sat_guarded_non_collapsed_types:        1
% 1.18/1.03  num_pure_diseq_elim:                    0
% 1.18/1.03  simp_replaced_by:                       0
% 1.18/1.03  res_preprocessed:                       86
% 1.18/1.03  prep_upred:                             0
% 1.18/1.03  prep_unflattend:                        9
% 1.18/1.03  smt_new_axioms:                         0
% 1.18/1.03  pred_elim_cands:                        3
% 1.18/1.03  pred_elim:                              3
% 1.18/1.03  pred_elim_cl:                           3
% 1.18/1.03  pred_elim_cycles:                       7
% 1.18/1.03  merged_defs:                            0
% 1.18/1.03  merged_defs_ncl:                        0
% 1.18/1.03  bin_hyper_res:                          0
% 1.18/1.03  prep_cycles:                            4
% 1.18/1.03  pred_elim_time:                         0.029
% 1.18/1.03  splitting_time:                         0.
% 1.18/1.03  sem_filter_time:                        0.
% 1.18/1.03  monotx_time:                            0.
% 1.18/1.03  subtype_inf_time:                       0.
% 1.18/1.03  
% 1.18/1.03  ------ Problem properties
% 1.18/1.03  
% 1.18/1.03  clauses:                                14
% 1.18/1.03  conjectures:                            5
% 1.18/1.03  epr:                                    4
% 1.18/1.03  horn:                                   10
% 1.18/1.03  ground:                                 10
% 1.18/1.03  unary:                                  1
% 1.18/1.03  binary:                                 6
% 1.18/1.03  lits:                                   38
% 1.18/1.03  lits_eq:                                12
% 1.18/1.03  fd_pure:                                0
% 1.18/1.03  fd_pseudo:                              0
% 1.18/1.03  fd_cond:                                0
% 1.18/1.03  fd_pseudo_cond:                         2
% 1.18/1.03  ac_symbols:                             0
% 1.18/1.03  
% 1.18/1.03  ------ Propositional Solver
% 1.18/1.03  
% 1.18/1.03  prop_solver_calls:                      27
% 1.18/1.03  prop_fast_solver_calls:                 757
% 1.18/1.03  smt_solver_calls:                       0
% 1.18/1.03  smt_fast_solver_calls:                  0
% 1.18/1.03  prop_num_of_clauses:                    337
% 1.18/1.03  prop_preprocess_simplified:             2053
% 1.18/1.03  prop_fo_subsumed:                       9
% 1.18/1.03  prop_solver_time:                       0.
% 1.18/1.03  smt_solver_time:                        0.
% 1.18/1.03  smt_fast_solver_time:                   0.
% 1.18/1.03  prop_fast_solver_time:                  0.
% 1.18/1.03  prop_unsat_core_time:                   0.
% 1.18/1.03  
% 1.18/1.03  ------ QBF
% 1.18/1.03  
% 1.18/1.03  qbf_q_res:                              0
% 1.18/1.03  qbf_num_tautologies:                    0
% 1.18/1.03  qbf_prep_cycles:                        0
% 1.18/1.03  
% 1.18/1.03  ------ BMC1
% 1.18/1.03  
% 1.18/1.03  bmc1_current_bound:                     -1
% 1.18/1.03  bmc1_last_solved_bound:                 -1
% 1.18/1.03  bmc1_unsat_core_size:                   -1
% 1.18/1.03  bmc1_unsat_core_parents_size:           -1
% 1.18/1.03  bmc1_merge_next_fun:                    0
% 1.18/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.18/1.03  
% 1.18/1.03  ------ Instantiation
% 1.18/1.03  
% 1.18/1.03  inst_num_of_clauses:                    74
% 1.18/1.03  inst_num_in_passive:                    1
% 1.18/1.03  inst_num_in_active:                     58
% 1.18/1.03  inst_num_in_unprocessed:                15
% 1.18/1.03  inst_num_of_loops:                      80
% 1.18/1.03  inst_num_of_learning_restarts:          0
% 1.18/1.03  inst_num_moves_active_passive:          18
% 1.18/1.03  inst_lit_activity:                      0
% 1.18/1.03  inst_lit_activity_moves:                0
% 1.18/1.03  inst_num_tautologies:                   0
% 1.18/1.03  inst_num_prop_implied:                  0
% 1.18/1.03  inst_num_existing_simplified:           0
% 1.18/1.03  inst_num_eq_res_simplified:             0
% 1.18/1.03  inst_num_child_elim:                    0
% 1.18/1.03  inst_num_of_dismatching_blockings:      3
% 1.18/1.03  inst_num_of_non_proper_insts:           54
% 1.18/1.03  inst_num_of_duplicates:                 0
% 1.18/1.03  inst_inst_num_from_inst_to_res:         0
% 1.18/1.03  inst_dismatching_checking_time:         0.
% 1.18/1.03  
% 1.18/1.03  ------ Resolution
% 1.18/1.03  
% 1.18/1.03  res_num_of_clauses:                     0
% 1.18/1.03  res_num_in_passive:                     0
% 1.18/1.03  res_num_in_active:                      0
% 1.18/1.03  res_num_of_loops:                       90
% 1.18/1.03  res_forward_subset_subsumed:            2
% 1.18/1.03  res_backward_subset_subsumed:           0
% 1.18/1.03  res_forward_subsumed:                   0
% 1.18/1.03  res_backward_subsumed:                  0
% 1.18/1.03  res_forward_subsumption_resolution:     0
% 1.18/1.03  res_backward_subsumption_resolution:    0
% 1.18/1.03  res_clause_to_clause_subsumption:       17
% 1.18/1.03  res_orphan_elimination:                 0
% 1.18/1.03  res_tautology_del:                      9
% 1.18/1.03  res_num_eq_res_simplified:              0
% 1.18/1.03  res_num_sel_changes:                    0
% 1.18/1.03  res_moves_from_active_to_pass:          0
% 1.18/1.03  
% 1.18/1.03  ------ Superposition
% 1.18/1.03  
% 1.18/1.03  sup_time_total:                         0.
% 1.18/1.03  sup_time_generating:                    0.
% 1.18/1.03  sup_time_sim_full:                      0.
% 1.18/1.03  sup_time_sim_immed:                     0.
% 1.18/1.03  
% 1.18/1.03  sup_num_of_clauses:                     17
% 1.18/1.03  sup_num_in_active:                      12
% 1.18/1.03  sup_num_in_passive:                     5
% 1.18/1.03  sup_num_of_loops:                       14
% 1.18/1.03  sup_fw_superposition:                   2
% 1.18/1.03  sup_bw_superposition:                   3
% 1.18/1.03  sup_immediate_simplified:               2
% 1.18/1.03  sup_given_eliminated:                   0
% 1.18/1.03  comparisons_done:                       0
% 1.18/1.03  comparisons_avoided:                    0
% 1.18/1.03  
% 1.18/1.03  ------ Simplifications
% 1.18/1.03  
% 1.18/1.03  
% 1.18/1.03  sim_fw_subset_subsumed:                 1
% 1.18/1.03  sim_bw_subset_subsumed:                 1
% 1.18/1.03  sim_fw_subsumed:                        0
% 1.18/1.03  sim_bw_subsumed:                        0
% 1.18/1.03  sim_fw_subsumption_res:                 0
% 1.18/1.03  sim_bw_subsumption_res:                 0
% 1.18/1.03  sim_tautology_del:                      0
% 1.18/1.03  sim_eq_tautology_del:                   3
% 1.18/1.03  sim_eq_res_simp:                        0
% 1.18/1.03  sim_fw_demodulated:                     0
% 1.18/1.03  sim_bw_demodulated:                     2
% 1.18/1.03  sim_light_normalised:                   2
% 1.18/1.03  sim_joinable_taut:                      0
% 1.18/1.03  sim_joinable_simp:                      0
% 1.18/1.03  sim_ac_normalised:                      0
% 1.18/1.03  sim_smt_subsumption:                    0
% 1.18/1.03  
%------------------------------------------------------------------------------
