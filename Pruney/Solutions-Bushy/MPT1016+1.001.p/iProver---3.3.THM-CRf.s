%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1016+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:40 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  138 (1334 expanded)
%              Number of clauses        :   98 ( 383 expanded)
%              Number of leaves         :   11 ( 280 expanded)
%              Depth                    :   22
%              Number of atoms          :  542 (10583 expanded)
%              Number of equality atoms :  256 (3493 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
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

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_264,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_265,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_1558,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(subtyping,[status(esa)],[c_265])).

cnf(c_1802,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_197,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_198,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_1562,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_1604,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_1606,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1611,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_1576,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1909,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_214,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_215,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_1561,plain,
    ( ~ r2_hidden(X0_46,k1_relat_1(sK3))
    | ~ r2_hidden(X1_46,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0_46) != k1_funct_1(sK3,X1_46)
    | X0_46 = X1_46 ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_1571,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1561])).

cnf(c_1798,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1573,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1593,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1573])).

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

cnf(c_9,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1568,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1599,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_1607,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

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
    ( k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(X0_48,X1_48,sK3) = k1_relat_1(sK3) ),
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

cnf(c_1570,plain,
    ( ~ r2_hidden(X0_46,k1_relat_1(sK3))
    | ~ r2_hidden(X1_46,k1_relat_1(sK3))
    | k1_funct_1(sK3,X0_46) != k1_funct_1(sK3,X1_46)
    | X0_46 = X1_46
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1561])).

cnf(c_1944,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_1945,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
    | sK4 = sK5
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_1585,plain,
    ( ~ r2_hidden(X0_46,X0_48)
    | r2_hidden(X1_46,X1_48)
    | X1_48 != X0_48
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1947,plain,
    ( ~ r2_hidden(X0_46,X0_48)
    | r2_hidden(sK4,k1_relat_1(sK3))
    | k1_relat_1(sK3) != X0_48
    | sK4 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_1948,plain,
    ( k1_relat_1(sK3) != X0_48
    | sK4 != X0_46
    | r2_hidden(X0_46,X0_48) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_1950,plain,
    ( k1_relat_1(sK3) != sK2
    | sK4 != sK4
    | r2_hidden(sK4,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_1985,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_1977,plain,
    ( ~ r2_hidden(X0_46,X0_48)
    | r2_hidden(sK5,k1_relat_1(sK3))
    | k1_relat_1(sK3) != X0_48
    | sK5 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_2017,plain,
    ( ~ r2_hidden(sK5,X0_48)
    | r2_hidden(sK5,k1_relat_1(sK3))
    | k1_relat_1(sK3) != X0_48
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_2018,plain,
    ( k1_relat_1(sK3) != X0_48
    | sK5 != sK5
    | r2_hidden(sK5,X0_48) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_2020,plain,
    ( k1_relat_1(sK3) != sK2
    | sK5 != sK5
    | r2_hidden(sK5,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_2032,plain,
    ( v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1798,c_22,c_23,c_1593,c_1598,c_1599,c_1606,c_1607,c_1909,c_1928,c_1945,c_1950,c_1985,c_2020])).

cnf(c_2060,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1802,c_22,c_23,c_1593,c_1598,c_1599,c_1606,c_1607,c_1611,c_1909,c_1928,c_1945,c_1950,c_1985,c_2020])).

cnf(c_1799,plain,
    ( k1_funct_1(sK3,X0_46) != k1_funct_1(sK3,X1_46)
    | X0_46 = X1_46
    | r2_hidden(X0_46,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_46,k1_relat_1(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_2038,plain,
    ( k1_funct_1(sK3,X0_46) != k1_funct_1(sK3,X1_46)
    | X0_46 = X1_46
    | r2_hidden(X0_46,sK2) != iProver_top
    | r2_hidden(X1_46,sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1799,c_1928])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1565,negated_conjecture,
    ( ~ r2_hidden(X0_46,sK2)
    | ~ r2_hidden(X1_46,sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,X1_46) != k1_funct_1(sK3,X0_46)
    | X1_46 = X0_46 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1602,plain,
    ( k1_funct_1(sK3,X0_46) != k1_funct_1(sK3,X1_46)
    | X0_46 = X1_46
    | r2_hidden(X0_46,sK2) != iProver_top
    | r2_hidden(X1_46,sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1565])).

cnf(c_2045,plain,
    ( r2_hidden(X1_46,sK2) != iProver_top
    | r2_hidden(X0_46,sK2) != iProver_top
    | X0_46 = X1_46
    | k1_funct_1(sK3,X0_46) != k1_funct_1(sK3,X1_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2038,c_22,c_23,c_1593,c_1598,c_1599,c_1602,c_1606,c_1607,c_1909,c_1928,c_1945,c_1950,c_1985,c_2020])).

cnf(c_2046,plain,
    ( k1_funct_1(sK3,X0_46) != k1_funct_1(sK3,X1_46)
    | X0_46 = X1_46
    | r2_hidden(X1_46,sK2) != iProver_top
    | r2_hidden(X0_46,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2045])).

cnf(c_2065,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_46)
    | sK1(sK3) = X0_46
    | r2_hidden(X0_46,sK2) != iProver_top
    | r2_hidden(sK1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_2046])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_251,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_252,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_1559,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_252])).

cnf(c_1801,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_16,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_38,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_40,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2052,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1801,c_16,c_22,c_23,c_40,c_1593,c_1598,c_1599,c_1606,c_1607,c_1909,c_1928,c_1945,c_1950,c_1985,c_2020])).

cnf(c_2056,plain,
    ( r2_hidden(sK1(sK3),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2052,c_1928])).

cnf(c_2146,plain,
    ( r2_hidden(X0_46,sK2) != iProver_top
    | sK1(sK3) = X0_46
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2065,c_2056])).

cnf(c_2147,plain,
    ( k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,X0_46)
    | sK1(sK3) = X0_46
    | r2_hidden(X0_46,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2146])).

cnf(c_2156,plain,
    ( sK1(sK3) = sK0(sK3)
    | r2_hidden(sK0(sK3),sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2147])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_238,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_239,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_1560,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_1800,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_35,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_37,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2004,plain,
    ( v2_funct_1(sK3) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1800,c_16,c_37,c_1606,c_1909])).

cnf(c_2005,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_2004])).

cnf(c_2008,plain,
    ( r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2005,c_1928])).

cnf(c_1,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_277,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_278,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_1557,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_1612,plain,
    ( sK1(sK3) != sK0(sK3)
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2156,c_2032,c_2008,c_1909,c_1612,c_1606])).


%------------------------------------------------------------------------------
