%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:47 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 605 expanded)
%              Number of clauses        :   97 ( 211 expanded)
%              Number of leaves         :   18 ( 133 expanded)
%              Depth                    :   20
%              Number of atoms          :  466 (2454 expanded)
%              Number of equality atoms :  182 ( 676 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK2,sK3,sK4) != sK3
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK4,X4) = X3
              & r2_hidden(X4,sK2) )
          | ~ r2_hidden(X3,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f38,f37])).

fof(f59,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1090,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_321,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_325,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(X0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_23,c_21])).

cnf(c_326,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_1077,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1089,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2300,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1089])).

cnf(c_1079,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1082,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2195,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1079,c_1082])).

cnf(c_2301,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2300,c_2195])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1081,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8359,plain,
    ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_1081])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_13])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_381,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_14])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_381])).

cnf(c_1076,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_1562,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1076])).

cnf(c_8847,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | sK3 = k1_xboole_0
    | k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8359,c_1562])).

cnf(c_8848,plain,
    ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8847])).

cnf(c_8853,plain,
    ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,sK0(sK2,X0)))) = k1_funct_1(sK4,sK0(sK2,X0))
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_8848])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_692,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1121,plain,
    ( k2_relset_1(sK2,sK3,sK4) != X0
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1173,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1233,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(sK3,k2_relat_1(sK4))
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1234,plain,
    ( sK3 = k2_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1888,plain,
    ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3)
    | r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1892,plain,
    ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top
    | r1_tarski(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1888])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1887,plain,
    ( ~ r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
    | r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1894,plain,
    ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
    | r1_tarski(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1887])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3852,plain,
    ( ~ r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3)
    | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3853,plain,
    ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) != iProver_top
    | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3852])).

cnf(c_1656,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,X0))) = sK0(sK3,X0)
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1081])).

cnf(c_1086,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2202,plain,
    ( k2_relat_1(sK4) = sK3
    | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1086])).

cnf(c_2885,plain,
    ( r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_21,c_18,c_1173,c_1234,c_1513,c_1562])).

cnf(c_2890,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4)) ),
    inference(superposition,[status(thm)],[c_1656,c_2885])).

cnf(c_2420,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2195,c_1077])).

cnf(c_10357,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2890,c_2420])).

cnf(c_10420,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8853,c_21,c_18,c_1173,c_1234,c_1513,c_1562,c_1892,c_1894,c_3853,c_10357])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1087,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_179,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_180])).

cnf(c_305,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_223])).

cnf(c_306,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_1078,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_2035,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1078])).

cnf(c_3950,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2035,c_1089])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1088,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) != iProver_top
    | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6937,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3950,c_1088])).

cnf(c_6967,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6937,c_2035])).

cnf(c_6973,plain,
    ( k2_relat_1(sK4) = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_6967])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_61,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_65,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1114,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
    | ~ r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4))
    | k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1115,plain,
    ( k2_relset_1(sK2,sK3,sK4) = sK3
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) != iProver_top
    | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_1257,plain,
    ( r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0)
    | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1263,plain,
    ( r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0) = iProver_top
    | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_1265,plain,
    ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top
    | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_693,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1161,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
    | k2_relset_1(sK2,sK3,sK4) != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_1313,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
    | ~ r1_tarski(k2_relat_1(sK4),X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_1314,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK3 != X0
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_1316,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | sK3 != sK3
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_2125,plain,
    ( ~ r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_2126,plain,
    ( r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_2128,plain,
    ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_7859,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6973,c_21,c_18,c_61,c_65,c_1115,c_1265,c_1316,c_1513,c_1562,c_2128])).

cnf(c_10438,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10420,c_7859])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5039,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5040,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5039])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10438,c_5040])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.99  
% 3.85/0.99  ------  iProver source info
% 3.85/0.99  
% 3.85/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.99  git: non_committed_changes: false
% 3.85/0.99  git: last_make_outside_of_git: false
% 3.85/0.99  
% 3.85/0.99  ------ 
% 3.85/0.99  
% 3.85/0.99  ------ Input Options
% 3.85/0.99  
% 3.85/0.99  --out_options                           all
% 3.85/0.99  --tptp_safe_out                         true
% 3.85/0.99  --problem_path                          ""
% 3.85/0.99  --include_path                          ""
% 3.85/0.99  --clausifier                            res/vclausify_rel
% 3.85/0.99  --clausifier_options                    ""
% 3.85/0.99  --stdin                                 false
% 3.85/0.99  --stats_out                             all
% 3.85/0.99  
% 3.85/0.99  ------ General Options
% 3.85/0.99  
% 3.85/0.99  --fof                                   false
% 3.85/0.99  --time_out_real                         305.
% 3.85/0.99  --time_out_virtual                      -1.
% 3.85/0.99  --symbol_type_check                     false
% 3.85/0.99  --clausify_out                          false
% 3.85/0.99  --sig_cnt_out                           false
% 3.85/0.99  --trig_cnt_out                          false
% 3.85/0.99  --trig_cnt_out_tolerance                1.
% 3.85/0.99  --trig_cnt_out_sk_spl                   false
% 3.85/0.99  --abstr_cl_out                          false
% 3.85/0.99  
% 3.85/0.99  ------ Global Options
% 3.85/0.99  
% 3.85/0.99  --schedule                              default
% 3.85/0.99  --add_important_lit                     false
% 3.85/0.99  --prop_solver_per_cl                    1000
% 3.85/0.99  --min_unsat_core                        false
% 3.85/0.99  --soft_assumptions                      false
% 3.85/0.99  --soft_lemma_size                       3
% 3.85/0.99  --prop_impl_unit_size                   0
% 3.85/0.99  --prop_impl_unit                        []
% 3.85/0.99  --share_sel_clauses                     true
% 3.85/0.99  --reset_solvers                         false
% 3.85/0.99  --bc_imp_inh                            [conj_cone]
% 3.85/0.99  --conj_cone_tolerance                   3.
% 3.85/0.99  --extra_neg_conj                        none
% 3.85/0.99  --large_theory_mode                     true
% 3.85/0.99  --prolific_symb_bound                   200
% 3.85/0.99  --lt_threshold                          2000
% 3.85/0.99  --clause_weak_htbl                      true
% 3.85/0.99  --gc_record_bc_elim                     false
% 3.85/0.99  
% 3.85/0.99  ------ Preprocessing Options
% 3.85/0.99  
% 3.85/0.99  --preprocessing_flag                    true
% 3.85/0.99  --time_out_prep_mult                    0.1
% 3.85/0.99  --splitting_mode                        input
% 3.85/0.99  --splitting_grd                         true
% 3.85/0.99  --splitting_cvd                         false
% 3.85/0.99  --splitting_cvd_svl                     false
% 3.85/0.99  --splitting_nvd                         32
% 3.85/0.99  --sub_typing                            true
% 3.85/0.99  --prep_gs_sim                           true
% 3.85/0.99  --prep_unflatten                        true
% 3.85/0.99  --prep_res_sim                          true
% 3.85/0.99  --prep_upred                            true
% 3.85/0.99  --prep_sem_filter                       exhaustive
% 3.85/0.99  --prep_sem_filter_out                   false
% 3.85/0.99  --pred_elim                             true
% 3.85/0.99  --res_sim_input                         true
% 3.85/0.99  --eq_ax_congr_red                       true
% 3.85/0.99  --pure_diseq_elim                       true
% 3.85/0.99  --brand_transform                       false
% 3.85/0.99  --non_eq_to_eq                          false
% 3.85/0.99  --prep_def_merge                        true
% 3.85/0.99  --prep_def_merge_prop_impl              false
% 3.85/0.99  --prep_def_merge_mbd                    true
% 3.85/0.99  --prep_def_merge_tr_red                 false
% 3.85/0.99  --prep_def_merge_tr_cl                  false
% 3.85/0.99  --smt_preprocessing                     true
% 3.85/0.99  --smt_ac_axioms                         fast
% 3.85/0.99  --preprocessed_out                      false
% 3.85/0.99  --preprocessed_stats                    false
% 3.85/0.99  
% 3.85/0.99  ------ Abstraction refinement Options
% 3.85/0.99  
% 3.85/0.99  --abstr_ref                             []
% 3.85/0.99  --abstr_ref_prep                        false
% 3.85/0.99  --abstr_ref_until_sat                   false
% 3.85/0.99  --abstr_ref_sig_restrict                funpre
% 3.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.99  --abstr_ref_under                       []
% 3.85/0.99  
% 3.85/0.99  ------ SAT Options
% 3.85/0.99  
% 3.85/0.99  --sat_mode                              false
% 3.85/0.99  --sat_fm_restart_options                ""
% 3.85/0.99  --sat_gr_def                            false
% 3.85/0.99  --sat_epr_types                         true
% 3.85/0.99  --sat_non_cyclic_types                  false
% 3.85/0.99  --sat_finite_models                     false
% 3.85/0.99  --sat_fm_lemmas                         false
% 3.85/0.99  --sat_fm_prep                           false
% 3.85/0.99  --sat_fm_uc_incr                        true
% 3.85/0.99  --sat_out_model                         small
% 3.85/0.99  --sat_out_clauses                       false
% 3.85/0.99  
% 3.85/0.99  ------ QBF Options
% 3.85/0.99  
% 3.85/0.99  --qbf_mode                              false
% 3.85/0.99  --qbf_elim_univ                         false
% 3.85/0.99  --qbf_dom_inst                          none
% 3.85/0.99  --qbf_dom_pre_inst                      false
% 3.85/0.99  --qbf_sk_in                             false
% 3.85/0.99  --qbf_pred_elim                         true
% 3.85/0.99  --qbf_split                             512
% 3.85/0.99  
% 3.85/0.99  ------ BMC1 Options
% 3.85/0.99  
% 3.85/0.99  --bmc1_incremental                      false
% 3.85/0.99  --bmc1_axioms                           reachable_all
% 3.85/0.99  --bmc1_min_bound                        0
% 3.85/0.99  --bmc1_max_bound                        -1
% 3.85/0.99  --bmc1_max_bound_default                -1
% 3.85/0.99  --bmc1_symbol_reachability              true
% 3.85/0.99  --bmc1_property_lemmas                  false
% 3.85/0.99  --bmc1_k_induction                      false
% 3.85/0.99  --bmc1_non_equiv_states                 false
% 3.85/0.99  --bmc1_deadlock                         false
% 3.85/0.99  --bmc1_ucm                              false
% 3.85/0.99  --bmc1_add_unsat_core                   none
% 3.85/1.00  --bmc1_unsat_core_children              false
% 3.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.00  --bmc1_out_stat                         full
% 3.85/1.00  --bmc1_ground_init                      false
% 3.85/1.00  --bmc1_pre_inst_next_state              false
% 3.85/1.00  --bmc1_pre_inst_state                   false
% 3.85/1.00  --bmc1_pre_inst_reach_state             false
% 3.85/1.00  --bmc1_out_unsat_core                   false
% 3.85/1.00  --bmc1_aig_witness_out                  false
% 3.85/1.00  --bmc1_verbose                          false
% 3.85/1.00  --bmc1_dump_clauses_tptp                false
% 3.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.00  --bmc1_dump_file                        -
% 3.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.00  --bmc1_ucm_extend_mode                  1
% 3.85/1.00  --bmc1_ucm_init_mode                    2
% 3.85/1.00  --bmc1_ucm_cone_mode                    none
% 3.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.00  --bmc1_ucm_relax_model                  4
% 3.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.00  --bmc1_ucm_layered_model                none
% 3.85/1.00  --bmc1_ucm_max_lemma_size               10
% 3.85/1.00  
% 3.85/1.00  ------ AIG Options
% 3.85/1.00  
% 3.85/1.00  --aig_mode                              false
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation Options
% 3.85/1.00  
% 3.85/1.00  --instantiation_flag                    true
% 3.85/1.00  --inst_sos_flag                         true
% 3.85/1.00  --inst_sos_phase                        true
% 3.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel_side                     num_symb
% 3.85/1.00  --inst_solver_per_active                1400
% 3.85/1.00  --inst_solver_calls_frac                1.
% 3.85/1.00  --inst_passive_queue_type               priority_queues
% 3.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/1.00  --inst_passive_queues_freq              [25;2]
% 3.85/1.00  --inst_dismatching                      true
% 3.85/1.00  --inst_eager_unprocessed_to_passive     true
% 3.85/1.00  --inst_prop_sim_given                   true
% 3.85/1.00  --inst_prop_sim_new                     false
% 3.85/1.00  --inst_subs_new                         false
% 3.85/1.00  --inst_eq_res_simp                      false
% 3.85/1.00  --inst_subs_given                       false
% 3.85/1.00  --inst_orphan_elimination               true
% 3.85/1.00  --inst_learning_loop_flag               true
% 3.85/1.00  --inst_learning_start                   3000
% 3.85/1.00  --inst_learning_factor                  2
% 3.85/1.00  --inst_start_prop_sim_after_learn       3
% 3.85/1.00  --inst_sel_renew                        solver
% 3.85/1.00  --inst_lit_activity_flag                true
% 3.85/1.00  --inst_restr_to_given                   false
% 3.85/1.00  --inst_activity_threshold               500
% 3.85/1.00  --inst_out_proof                        true
% 3.85/1.00  
% 3.85/1.00  ------ Resolution Options
% 3.85/1.00  
% 3.85/1.00  --resolution_flag                       true
% 3.85/1.00  --res_lit_sel                           adaptive
% 3.85/1.00  --res_lit_sel_side                      none
% 3.85/1.00  --res_ordering                          kbo
% 3.85/1.00  --res_to_prop_solver                    active
% 3.85/1.00  --res_prop_simpl_new                    false
% 3.85/1.00  --res_prop_simpl_given                  true
% 3.85/1.00  --res_passive_queue_type                priority_queues
% 3.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/1.00  --res_passive_queues_freq               [15;5]
% 3.85/1.00  --res_forward_subs                      full
% 3.85/1.00  --res_backward_subs                     full
% 3.85/1.00  --res_forward_subs_resolution           true
% 3.85/1.00  --res_backward_subs_resolution          true
% 3.85/1.00  --res_orphan_elimination                true
% 3.85/1.00  --res_time_limit                        2.
% 3.85/1.00  --res_out_proof                         true
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Options
% 3.85/1.00  
% 3.85/1.00  --superposition_flag                    true
% 3.85/1.00  --sup_passive_queue_type                priority_queues
% 3.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.00  --demod_completeness_check              fast
% 3.85/1.00  --demod_use_ground                      true
% 3.85/1.00  --sup_to_prop_solver                    passive
% 3.85/1.00  --sup_prop_simpl_new                    true
% 3.85/1.00  --sup_prop_simpl_given                  true
% 3.85/1.00  --sup_fun_splitting                     true
% 3.85/1.00  --sup_smt_interval                      50000
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Simplification Setup
% 3.85/1.00  
% 3.85/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_immed_triv                        [TrivRules]
% 3.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_bw_main                     []
% 3.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_input_bw                          []
% 3.85/1.00  
% 3.85/1.00  ------ Combination Options
% 3.85/1.00  
% 3.85/1.00  --comb_res_mult                         3
% 3.85/1.00  --comb_sup_mult                         2
% 3.85/1.00  --comb_inst_mult                        10
% 3.85/1.00  
% 3.85/1.00  ------ Debug Options
% 3.85/1.00  
% 3.85/1.00  --dbg_backtrace                         false
% 3.85/1.00  --dbg_dump_prop_clauses                 false
% 3.85/1.00  --dbg_dump_prop_clauses_file            -
% 3.85/1.00  --dbg_out_stat                          false
% 3.85/1.00  ------ Parsing...
% 3.85/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  ------ Proving...
% 3.85/1.00  ------ Problem Properties 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  clauses                                 17
% 3.85/1.00  conjectures                             4
% 3.85/1.00  EPR                                     4
% 3.85/1.00  Horn                                    14
% 3.85/1.00  unary                                   3
% 3.85/1.00  binary                                  9
% 3.85/1.00  lits                                    36
% 3.85/1.00  lits eq                                 7
% 3.85/1.00  fd_pure                                 0
% 3.85/1.00  fd_pseudo                               0
% 3.85/1.00  fd_cond                                 0
% 3.85/1.00  fd_pseudo_cond                          3
% 3.85/1.00  AC symbols                              0
% 3.85/1.00  
% 3.85/1.00  ------ Schedule dynamic 5 is on 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  Current options:
% 3.85/1.00  ------ 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options
% 3.85/1.00  
% 3.85/1.00  --out_options                           all
% 3.85/1.00  --tptp_safe_out                         true
% 3.85/1.00  --problem_path                          ""
% 3.85/1.00  --include_path                          ""
% 3.85/1.00  --clausifier                            res/vclausify_rel
% 3.85/1.00  --clausifier_options                    ""
% 3.85/1.00  --stdin                                 false
% 3.85/1.00  --stats_out                             all
% 3.85/1.00  
% 3.85/1.00  ------ General Options
% 3.85/1.00  
% 3.85/1.00  --fof                                   false
% 3.85/1.00  --time_out_real                         305.
% 3.85/1.00  --time_out_virtual                      -1.
% 3.85/1.00  --symbol_type_check                     false
% 3.85/1.00  --clausify_out                          false
% 3.85/1.00  --sig_cnt_out                           false
% 3.85/1.00  --trig_cnt_out                          false
% 3.85/1.00  --trig_cnt_out_tolerance                1.
% 3.85/1.00  --trig_cnt_out_sk_spl                   false
% 3.85/1.00  --abstr_cl_out                          false
% 3.85/1.00  
% 3.85/1.00  ------ Global Options
% 3.85/1.00  
% 3.85/1.00  --schedule                              default
% 3.85/1.00  --add_important_lit                     false
% 3.85/1.00  --prop_solver_per_cl                    1000
% 3.85/1.00  --min_unsat_core                        false
% 3.85/1.00  --soft_assumptions                      false
% 3.85/1.00  --soft_lemma_size                       3
% 3.85/1.00  --prop_impl_unit_size                   0
% 3.85/1.00  --prop_impl_unit                        []
% 3.85/1.00  --share_sel_clauses                     true
% 3.85/1.00  --reset_solvers                         false
% 3.85/1.00  --bc_imp_inh                            [conj_cone]
% 3.85/1.00  --conj_cone_tolerance                   3.
% 3.85/1.00  --extra_neg_conj                        none
% 3.85/1.00  --large_theory_mode                     true
% 3.85/1.00  --prolific_symb_bound                   200
% 3.85/1.00  --lt_threshold                          2000
% 3.85/1.00  --clause_weak_htbl                      true
% 3.85/1.00  --gc_record_bc_elim                     false
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing Options
% 3.85/1.00  
% 3.85/1.00  --preprocessing_flag                    true
% 3.85/1.00  --time_out_prep_mult                    0.1
% 3.85/1.00  --splitting_mode                        input
% 3.85/1.00  --splitting_grd                         true
% 3.85/1.00  --splitting_cvd                         false
% 3.85/1.00  --splitting_cvd_svl                     false
% 3.85/1.00  --splitting_nvd                         32
% 3.85/1.00  --sub_typing                            true
% 3.85/1.00  --prep_gs_sim                           true
% 3.85/1.00  --prep_unflatten                        true
% 3.85/1.00  --prep_res_sim                          true
% 3.85/1.00  --prep_upred                            true
% 3.85/1.00  --prep_sem_filter                       exhaustive
% 3.85/1.00  --prep_sem_filter_out                   false
% 3.85/1.00  --pred_elim                             true
% 3.85/1.00  --res_sim_input                         true
% 3.85/1.00  --eq_ax_congr_red                       true
% 3.85/1.00  --pure_diseq_elim                       true
% 3.85/1.00  --brand_transform                       false
% 3.85/1.00  --non_eq_to_eq                          false
% 3.85/1.00  --prep_def_merge                        true
% 3.85/1.00  --prep_def_merge_prop_impl              false
% 3.85/1.00  --prep_def_merge_mbd                    true
% 3.85/1.00  --prep_def_merge_tr_red                 false
% 3.85/1.00  --prep_def_merge_tr_cl                  false
% 3.85/1.00  --smt_preprocessing                     true
% 3.85/1.00  --smt_ac_axioms                         fast
% 3.85/1.00  --preprocessed_out                      false
% 3.85/1.00  --preprocessed_stats                    false
% 3.85/1.00  
% 3.85/1.00  ------ Abstraction refinement Options
% 3.85/1.00  
% 3.85/1.00  --abstr_ref                             []
% 3.85/1.00  --abstr_ref_prep                        false
% 3.85/1.00  --abstr_ref_until_sat                   false
% 3.85/1.00  --abstr_ref_sig_restrict                funpre
% 3.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/1.00  --abstr_ref_under                       []
% 3.85/1.00  
% 3.85/1.00  ------ SAT Options
% 3.85/1.00  
% 3.85/1.00  --sat_mode                              false
% 3.85/1.00  --sat_fm_restart_options                ""
% 3.85/1.00  --sat_gr_def                            false
% 3.85/1.00  --sat_epr_types                         true
% 3.85/1.00  --sat_non_cyclic_types                  false
% 3.85/1.00  --sat_finite_models                     false
% 3.85/1.00  --sat_fm_lemmas                         false
% 3.85/1.00  --sat_fm_prep                           false
% 3.85/1.00  --sat_fm_uc_incr                        true
% 3.85/1.00  --sat_out_model                         small
% 3.85/1.00  --sat_out_clauses                       false
% 3.85/1.00  
% 3.85/1.00  ------ QBF Options
% 3.85/1.00  
% 3.85/1.00  --qbf_mode                              false
% 3.85/1.00  --qbf_elim_univ                         false
% 3.85/1.00  --qbf_dom_inst                          none
% 3.85/1.00  --qbf_dom_pre_inst                      false
% 3.85/1.00  --qbf_sk_in                             false
% 3.85/1.00  --qbf_pred_elim                         true
% 3.85/1.00  --qbf_split                             512
% 3.85/1.00  
% 3.85/1.00  ------ BMC1 Options
% 3.85/1.00  
% 3.85/1.00  --bmc1_incremental                      false
% 3.85/1.00  --bmc1_axioms                           reachable_all
% 3.85/1.00  --bmc1_min_bound                        0
% 3.85/1.00  --bmc1_max_bound                        -1
% 3.85/1.00  --bmc1_max_bound_default                -1
% 3.85/1.00  --bmc1_symbol_reachability              true
% 3.85/1.00  --bmc1_property_lemmas                  false
% 3.85/1.00  --bmc1_k_induction                      false
% 3.85/1.00  --bmc1_non_equiv_states                 false
% 3.85/1.00  --bmc1_deadlock                         false
% 3.85/1.00  --bmc1_ucm                              false
% 3.85/1.00  --bmc1_add_unsat_core                   none
% 3.85/1.00  --bmc1_unsat_core_children              false
% 3.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.00  --bmc1_out_stat                         full
% 3.85/1.00  --bmc1_ground_init                      false
% 3.85/1.00  --bmc1_pre_inst_next_state              false
% 3.85/1.00  --bmc1_pre_inst_state                   false
% 3.85/1.00  --bmc1_pre_inst_reach_state             false
% 3.85/1.00  --bmc1_out_unsat_core                   false
% 3.85/1.00  --bmc1_aig_witness_out                  false
% 3.85/1.00  --bmc1_verbose                          false
% 3.85/1.00  --bmc1_dump_clauses_tptp                false
% 3.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.00  --bmc1_dump_file                        -
% 3.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.00  --bmc1_ucm_extend_mode                  1
% 3.85/1.00  --bmc1_ucm_init_mode                    2
% 3.85/1.00  --bmc1_ucm_cone_mode                    none
% 3.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.00  --bmc1_ucm_relax_model                  4
% 3.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.00  --bmc1_ucm_layered_model                none
% 3.85/1.00  --bmc1_ucm_max_lemma_size               10
% 3.85/1.00  
% 3.85/1.00  ------ AIG Options
% 3.85/1.00  
% 3.85/1.00  --aig_mode                              false
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation Options
% 3.85/1.00  
% 3.85/1.00  --instantiation_flag                    true
% 3.85/1.00  --inst_sos_flag                         true
% 3.85/1.00  --inst_sos_phase                        true
% 3.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel_side                     none
% 3.85/1.00  --inst_solver_per_active                1400
% 3.85/1.00  --inst_solver_calls_frac                1.
% 3.85/1.00  --inst_passive_queue_type               priority_queues
% 3.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/1.00  --inst_passive_queues_freq              [25;2]
% 3.85/1.00  --inst_dismatching                      true
% 3.85/1.00  --inst_eager_unprocessed_to_passive     true
% 3.85/1.00  --inst_prop_sim_given                   true
% 3.85/1.00  --inst_prop_sim_new                     false
% 3.85/1.00  --inst_subs_new                         false
% 3.85/1.00  --inst_eq_res_simp                      false
% 3.85/1.00  --inst_subs_given                       false
% 3.85/1.00  --inst_orphan_elimination               true
% 3.85/1.00  --inst_learning_loop_flag               true
% 3.85/1.00  --inst_learning_start                   3000
% 3.85/1.00  --inst_learning_factor                  2
% 3.85/1.00  --inst_start_prop_sim_after_learn       3
% 3.85/1.00  --inst_sel_renew                        solver
% 3.85/1.00  --inst_lit_activity_flag                true
% 3.85/1.00  --inst_restr_to_given                   false
% 3.85/1.00  --inst_activity_threshold               500
% 3.85/1.00  --inst_out_proof                        true
% 3.85/1.00  
% 3.85/1.00  ------ Resolution Options
% 3.85/1.00  
% 3.85/1.00  --resolution_flag                       false
% 3.85/1.00  --res_lit_sel                           adaptive
% 3.85/1.00  --res_lit_sel_side                      none
% 3.85/1.00  --res_ordering                          kbo
% 3.85/1.00  --res_to_prop_solver                    active
% 3.85/1.00  --res_prop_simpl_new                    false
% 3.85/1.00  --res_prop_simpl_given                  true
% 3.85/1.00  --res_passive_queue_type                priority_queues
% 3.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/1.00  --res_passive_queues_freq               [15;5]
% 3.85/1.00  --res_forward_subs                      full
% 3.85/1.00  --res_backward_subs                     full
% 3.85/1.00  --res_forward_subs_resolution           true
% 3.85/1.00  --res_backward_subs_resolution          true
% 3.85/1.00  --res_orphan_elimination                true
% 3.85/1.00  --res_time_limit                        2.
% 3.85/1.00  --res_out_proof                         true
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Options
% 3.85/1.00  
% 3.85/1.00  --superposition_flag                    true
% 3.85/1.00  --sup_passive_queue_type                priority_queues
% 3.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.00  --demod_completeness_check              fast
% 3.85/1.00  --demod_use_ground                      true
% 3.85/1.00  --sup_to_prop_solver                    passive
% 3.85/1.00  --sup_prop_simpl_new                    true
% 3.85/1.00  --sup_prop_simpl_given                  true
% 3.85/1.00  --sup_fun_splitting                     true
% 3.85/1.00  --sup_smt_interval                      50000
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Simplification Setup
% 3.85/1.00  
% 3.85/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_immed_triv                        [TrivRules]
% 3.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_bw_main                     []
% 3.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_input_bw                          []
% 3.85/1.00  
% 3.85/1.00  ------ Combination Options
% 3.85/1.00  
% 3.85/1.00  --comb_res_mult                         3
% 3.85/1.00  --comb_sup_mult                         2
% 3.85/1.00  --comb_inst_mult                        10
% 3.85/1.00  
% 3.85/1.00  ------ Debug Options
% 3.85/1.00  
% 3.85/1.00  --dbg_backtrace                         false
% 3.85/1.00  --dbg_dump_prop_clauses                 false
% 3.85/1.00  --dbg_dump_prop_clauses_file            -
% 3.85/1.00  --dbg_out_stat                          false
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS status Theorem for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  fof(f1,axiom,(
% 3.85/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f15,plain,(
% 3.85/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.85/1.00    inference(ennf_transformation,[],[f1])).
% 3.85/1.00  
% 3.85/1.00  fof(f26,plain,(
% 3.85/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/1.00    inference(nnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f27,plain,(
% 3.85/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/1.00    inference(rectify,[],[f26])).
% 3.85/1.00  
% 3.85/1.00  fof(f28,plain,(
% 3.85/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f29,plain,(
% 3.85/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.85/1.00  
% 3.85/1.00  fof(f41,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f29])).
% 3.85/1.00  
% 3.85/1.00  fof(f11,axiom,(
% 3.85/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f22,plain,(
% 3.85/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.85/1.00    inference(ennf_transformation,[],[f11])).
% 3.85/1.00  
% 3.85/1.00  fof(f23,plain,(
% 3.85/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.85/1.00    inference(flattening,[],[f22])).
% 3.85/1.00  
% 3.85/1.00  fof(f57,plain,(
% 3.85/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f12,conjecture,(
% 3.85/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f13,negated_conjecture,(
% 3.85/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.85/1.00    inference(negated_conjecture,[],[f12])).
% 3.85/1.00  
% 3.85/1.00  fof(f24,plain,(
% 3.85/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.85/1.00    inference(ennf_transformation,[],[f13])).
% 3.85/1.00  
% 3.85/1.00  fof(f25,plain,(
% 3.85/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.85/1.00    inference(flattening,[],[f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f38,plain,(
% 3.85/1.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f37,plain,(
% 3.85/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f39,plain,(
% 3.85/1.00    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f38,f37])).
% 3.85/1.00  
% 3.85/1.00  fof(f59,plain,(
% 3.85/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.85/1.00    inference(cnf_transformation,[],[f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f58,plain,(
% 3.85/1.00    v1_funct_1(sK4)),
% 3.85/1.00    inference(cnf_transformation,[],[f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f60,plain,(
% 3.85/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.85/1.00    inference(cnf_transformation,[],[f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f40,plain,(
% 3.85/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f29])).
% 3.85/1.00  
% 3.85/1.00  fof(f10,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f21,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.85/1.00    inference(ennf_transformation,[],[f10])).
% 3.85/1.00  
% 3.85/1.00  fof(f56,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f21])).
% 3.85/1.00  
% 3.85/1.00  fof(f62,plain,(
% 3.85/1.00    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f9,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f14,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.85/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.85/1.00  
% 3.85/1.00  fof(f20,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.85/1.00    inference(ennf_transformation,[],[f14])).
% 3.85/1.00  
% 3.85/1.00  fof(f55,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f20])).
% 3.85/1.00  
% 3.85/1.00  fof(f7,axiom,(
% 3.85/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f18,plain,(
% 3.85/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.85/1.00    inference(ennf_transformation,[],[f7])).
% 3.85/1.00  
% 3.85/1.00  fof(f36,plain,(
% 3.85/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.85/1.00    inference(nnf_transformation,[],[f18])).
% 3.85/1.00  
% 3.85/1.00  fof(f52,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f36])).
% 3.85/1.00  
% 3.85/1.00  fof(f8,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f19,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.85/1.00    inference(ennf_transformation,[],[f8])).
% 3.85/1.00  
% 3.85/1.00  fof(f54,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f19])).
% 3.85/1.00  
% 3.85/1.00  fof(f63,plain,(
% 3.85/1.00    k2_relset_1(sK2,sK3,sK4) != sK3),
% 3.85/1.00    inference(cnf_transformation,[],[f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f4,axiom,(
% 3.85/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f33,plain,(
% 3.85/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/1.00    inference(nnf_transformation,[],[f4])).
% 3.85/1.00  
% 3.85/1.00  fof(f34,plain,(
% 3.85/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/1.00    inference(flattening,[],[f33])).
% 3.85/1.00  
% 3.85/1.00  fof(f48,plain,(
% 3.85/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f34])).
% 3.85/1.00  
% 3.85/1.00  fof(f42,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f29])).
% 3.85/1.00  
% 3.85/1.00  fof(f61,plain,(
% 3.85/1.00    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f3,axiom,(
% 3.85/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f16,plain,(
% 3.85/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.85/1.00    inference(ennf_transformation,[],[f3])).
% 3.85/1.00  
% 3.85/1.00  fof(f30,plain,(
% 3.85/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.85/1.00    inference(nnf_transformation,[],[f16])).
% 3.85/1.00  
% 3.85/1.00  fof(f31,plain,(
% 3.85/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f32,plain,(
% 3.85/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.85/1.00  
% 3.85/1.00  fof(f44,plain,(
% 3.85/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f32])).
% 3.85/1.00  
% 3.85/1.00  fof(f2,axiom,(
% 3.85/1.00    v1_xboole_0(k1_xboole_0)),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f43,plain,(
% 3.85/1.00    v1_xboole_0(k1_xboole_0)),
% 3.85/1.00    inference(cnf_transformation,[],[f2])).
% 3.85/1.00  
% 3.85/1.00  fof(f6,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f17,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.85/1.00    inference(ennf_transformation,[],[f6])).
% 3.85/1.00  
% 3.85/1.00  fof(f51,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f17])).
% 3.85/1.00  
% 3.85/1.00  fof(f5,axiom,(
% 3.85/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.85/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f35,plain,(
% 3.85/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.85/1.00    inference(nnf_transformation,[],[f5])).
% 3.85/1.00  
% 3.85/1.00  fof(f50,plain,(
% 3.85/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f35])).
% 3.85/1.00  
% 3.85/1.00  fof(f45,plain,(
% 3.85/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f32])).
% 3.85/1.00  
% 3.85/1.00  fof(f46,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.85/1.00    inference(cnf_transformation,[],[f34])).
% 3.85/1.00  
% 3.85/1.00  fof(f65,plain,(
% 3.85/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.85/1.00    inference(equality_resolution,[],[f46])).
% 3.85/1.00  
% 3.85/1.00  fof(f47,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.85/1.00    inference(cnf_transformation,[],[f34])).
% 3.85/1.00  
% 3.85/1.00  fof(f64,plain,(
% 3.85/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.85/1.00    inference(equality_resolution,[],[f47])).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1,plain,
% 3.85/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1090,plain,
% 3.85/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.85/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_17,plain,
% 3.85/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/1.00      | ~ r2_hidden(X3,X1)
% 3.85/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | k1_xboole_0 = X2 ),
% 3.85/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_22,negated_conjecture,
% 3.85/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.85/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_320,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/1.00      | ~ r2_hidden(X3,X1)
% 3.85/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.85/1.00      | ~ v1_funct_1(X0)
% 3.85/1.00      | sK4 != X0
% 3.85/1.00      | sK3 != X2
% 3.85/1.00      | sK2 != X1
% 3.85/1.00      | k1_xboole_0 = X2 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_321,plain,
% 3.85/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.85/1.00      | ~ r2_hidden(X0,sK2)
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.85/1.00      | ~ v1_funct_1(sK4)
% 3.85/1.00      | k1_xboole_0 = sK3 ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_320]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_23,negated_conjecture,
% 3.85/1.00      ( v1_funct_1(sK4) ),
% 3.85/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_21,negated_conjecture,
% 3.85/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.85/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_325,plain,
% 3.85/1.00      ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.85/1.00      | ~ r2_hidden(X0,sK2)
% 3.85/1.00      | k1_xboole_0 = sK3 ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_321,c_23,c_21]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_326,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,sK2)
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.85/1.00      | k1_xboole_0 = sK3 ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_325]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1077,plain,
% 3.85/1.00      ( k1_xboole_0 = sK3
% 3.85/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1089,plain,
% 3.85/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.85/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.85/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2300,plain,
% 3.85/1.00      ( sK3 = k1_xboole_0
% 3.85/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
% 3.85/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X1) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1077,c_1089]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1079,plain,
% 3.85/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_16,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1082,plain,
% 3.85/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.85/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2195,plain,
% 3.85/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1079,c_1082]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2301,plain,
% 3.85/1.00      ( sK3 = k1_xboole_0
% 3.85/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
% 3.85/1.00      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_2300,c_2195]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_19,negated_conjecture,
% 3.85/1.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1081,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8359,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
% 3.85/1.00      | sK3 = k1_xboole_0
% 3.85/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.85/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2301,c_1081]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_15,plain,
% 3.85/1.00      ( v5_relat_1(X0,X1)
% 3.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.85/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_13,plain,
% 3.85/1.00      ( ~ v5_relat_1(X0,X1)
% 3.85/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.85/1.00      | ~ v1_relat_1(X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_377,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.85/1.00      | ~ v1_relat_1(X0) ),
% 3.85/1.00      inference(resolution,[status(thm)],[c_15,c_13]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_14,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/1.00      | v1_relat_1(X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_381,plain,
% 3.85/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_377,c_14]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_382,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.85/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_381]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1076,plain,
% 3.85/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.85/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1562,plain,
% 3.85/1.00      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1079,c_1076]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8847,plain,
% 3.85/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.85/1.00      | sK3 = k1_xboole_0
% 3.85/1.00      | k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0) ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_8359,c_1562]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8848,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
% 3.85/1.00      | sK3 = k1_xboole_0
% 3.85/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_8847]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8853,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK5(k1_funct_1(sK4,sK0(sK2,X0)))) = k1_funct_1(sK4,sK0(sK2,X0))
% 3.85/1.00      | sK3 = k1_xboole_0
% 3.85/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1090,c_8848]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_18,negated_conjecture,
% 3.85/1.00      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 3.85/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_692,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1121,plain,
% 3.85/1.00      ( k2_relset_1(sK2,sK3,sK4) != X0
% 3.85/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3
% 3.85/1.00      | sK3 != X0 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_692]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1173,plain,
% 3.85/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.85/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3
% 3.85/1.00      | sK3 != k2_relat_1(sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1121]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6,plain,
% 3.85/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1233,plain,
% 3.85/1.00      ( ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.85/1.00      | ~ r1_tarski(sK3,k2_relat_1(sK4))
% 3.85/1.00      | sK3 = k2_relat_1(sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1234,plain,
% 3.85/1.00      ( sK3 = k2_relat_1(sK4)
% 3.85/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.85/1.00      | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1513,plain,
% 3.85/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.85/1.00      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1888,plain,
% 3.85/1.00      ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3)
% 3.85/1.00      | r1_tarski(sK3,k2_relat_1(sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1892,plain,
% 3.85/1.00      ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top
% 3.85/1.00      | r1_tarski(sK3,k2_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1888]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_0,plain,
% 3.85/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1887,plain,
% 3.85/1.00      ( ~ r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4))
% 3.85/1.00      | r1_tarski(sK3,k2_relat_1(sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1894,plain,
% 3.85/1.00      ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
% 3.85/1.00      | r1_tarski(sK3,k2_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1887]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_20,negated_conjecture,
% 3.85/1.00      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3852,plain,
% 3.85/1.00      ( ~ r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3)
% 3.85/1.00      | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3853,plain,
% 3.85/1.00      ( r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) != iProver_top
% 3.85/1.00      | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_3852]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1656,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,X0))) = sK0(sK3,X0)
% 3.85/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1090,c_1081]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1086,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.85/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2202,plain,
% 3.85/1.00      ( k2_relat_1(sK4) = sK3
% 3.85/1.00      | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1562,c_1086]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2885,plain,
% 3.85/1.00      ( r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_2202,c_21,c_18,c_1173,c_1234,c_1513,c_1562]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2890,plain,
% 3.85/1.00      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1656,c_2885]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2420,plain,
% 3.85/1.00      ( sK3 = k1_xboole_0
% 3.85/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.85/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2195,c_1077]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10357,plain,
% 3.85/1.00      ( sK3 = k1_xboole_0
% 3.85/1.00      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
% 3.85/1.00      | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2890,c_2420]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10420,plain,
% 3.85/1.00      ( sK3 = k1_xboole_0 ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_8853,c_21,c_18,c_1173,c_1234,c_1513,c_1562,c_1892,
% 3.85/1.00                 c_1894,c_3853,c_10357]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5,plain,
% 3.85/1.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1087,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 3.85/1.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3,plain,
% 3.85/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_11,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/1.00      | ~ r2_hidden(X2,X0)
% 3.85/1.00      | ~ v1_xboole_0(X1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9,plain,
% 3.85/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_179,plain,
% 3.85/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.85/1.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_180,plain,
% 3.85/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/1.00      inference(renaming,[status(thm)],[c_179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_223,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.85/1.00      inference(bin_hyper_res,[status(thm)],[c_11,c_180]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_305,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_223]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_306,plain,
% 3.85/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_305]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1078,plain,
% 3.85/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.85/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2035,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 3.85/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1087,c_1078]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3950,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | r2_hidden(sK1(X1,X0),X2) = iProver_top
% 3.85/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.85/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2035,c_1089]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4,plain,
% 3.85/1.00      ( ~ r2_hidden(sK1(X0,X1),X1)
% 3.85/1.00      | ~ r2_hidden(sK1(X0,X1),X0)
% 3.85/1.00      | X1 = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1088,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | r2_hidden(sK1(X1,X0),X0) != iProver_top
% 3.85/1.00      | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6937,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | r2_hidden(sK1(X0,X1),X0) != iProver_top
% 3.85/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.85/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3950,c_1088]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6967,plain,
% 3.85/1.00      ( X0 = X1
% 3.85/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.85/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_6937,c_2035]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6973,plain,
% 3.85/1.00      ( k2_relat_1(sK4) = sK3
% 3.85/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1562,c_6967]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8,plain,
% 3.85/1.00      ( r1_tarski(X0,X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_61,plain,
% 3.85/1.00      ( r1_tarski(sK3,sK3) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_65,plain,
% 3.85/1.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1114,plain,
% 3.85/1.00      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
% 3.85/1.00      | ~ r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4))
% 3.85/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1115,plain,
% 3.85/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3
% 3.85/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) != iProver_top
% 3.85/1.00      | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1257,plain,
% 3.85/1.00      ( r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0)
% 3.85/1.00      | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4)) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1263,plain,
% 3.85/1.00      ( r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0) = iProver_top
% 3.85/1.00      | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1265,plain,
% 3.85/1.00      ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.85/1.00      | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_693,plain,
% 3.85/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.85/1.00      theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1161,plain,
% 3.85/1.00      ( ~ r1_tarski(X0,X1)
% 3.85/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
% 3.85/1.00      | k2_relset_1(sK2,sK3,sK4) != X0
% 3.85/1.00      | sK3 != X1 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_693]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1313,plain,
% 3.85/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3)
% 3.85/1.00      | ~ r1_tarski(k2_relat_1(sK4),X0)
% 3.85/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.85/1.00      | sK3 != X0 ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1161]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1314,plain,
% 3.85/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.85/1.00      | sK3 != X0
% 3.85/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) = iProver_top
% 3.85/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1316,plain,
% 3.85/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.85/1.00      | sK3 != sK3
% 3.85/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) = iProver_top
% 3.85/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_1314]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2125,plain,
% 3.85/1.00      ( ~ r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0)
% 3.85/1.00      | ~ r1_tarski(X0,k1_xboole_0) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2126,plain,
% 3.85/1.00      ( r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),X0) != iProver_top
% 3.85/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2128,plain,
% 3.85/1.00      ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.85/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_2126]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7859,plain,
% 3.85/1.00      ( r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(global_propositional_subsumption,
% 3.85/1.00                [status(thm)],
% 3.85/1.00                [c_6973,c_21,c_18,c_61,c_65,c_1115,c_1265,c_1316,c_1513,
% 3.85/1.00                 c_1562,c_2128]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10438,plain,
% 3.85/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_10420,c_7859]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7,plain,
% 3.85/1.00      ( r1_tarski(X0,X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5039,plain,
% 3.85/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.85/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5040,plain,
% 3.85/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_5039]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(contradiction,plain,
% 3.85/1.00      ( $false ),
% 3.85/1.00      inference(minisat,[status(thm)],[c_10438,c_5040]) ).
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  ------                               Statistics
% 3.85/1.00  
% 3.85/1.00  ------ General
% 3.85/1.00  
% 3.85/1.00  abstr_ref_over_cycles:                  0
% 3.85/1.00  abstr_ref_under_cycles:                 0
% 3.85/1.00  gc_basic_clause_elim:                   0
% 3.85/1.00  forced_gc_time:                         0
% 3.85/1.00  parsing_time:                           0.007
% 3.85/1.00  unif_index_cands_time:                  0.
% 3.85/1.00  unif_index_add_time:                    0.
% 3.85/1.00  orderings_time:                         0.
% 3.85/1.00  out_proof_time:                         0.015
% 3.85/1.00  total_time:                             0.506
% 3.85/1.00  num_of_symbols:                         51
% 3.85/1.00  num_of_terms:                           7669
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing
% 3.85/1.00  
% 3.85/1.00  num_of_splits:                          0
% 3.85/1.00  num_of_split_atoms:                     0
% 3.85/1.00  num_of_reused_defs:                     0
% 3.85/1.00  num_eq_ax_congr_red:                    22
% 3.85/1.00  num_of_sem_filtered_clauses:            1
% 3.85/1.00  num_of_subtypes:                        0
% 3.85/1.00  monotx_restored_types:                  0
% 3.85/1.00  sat_num_of_epr_types:                   0
% 3.85/1.00  sat_num_of_non_cyclic_types:            0
% 3.85/1.00  sat_guarded_non_collapsed_types:        0
% 3.85/1.00  num_pure_diseq_elim:                    0
% 3.85/1.00  simp_replaced_by:                       0
% 3.85/1.00  res_preprocessed:                       93
% 3.85/1.00  prep_upred:                             0
% 3.85/1.00  prep_unflattend:                        14
% 3.85/1.00  smt_new_axioms:                         0
% 3.85/1.00  pred_elim_cands:                        3
% 3.85/1.00  pred_elim:                              5
% 3.85/1.00  pred_elim_cl:                           6
% 3.85/1.00  pred_elim_cycles:                       8
% 3.85/1.00  merged_defs:                            8
% 3.85/1.00  merged_defs_ncl:                        0
% 3.85/1.00  bin_hyper_res:                          9
% 3.85/1.00  prep_cycles:                            4
% 3.85/1.00  pred_elim_time:                         0.004
% 3.85/1.00  splitting_time:                         0.
% 3.85/1.00  sem_filter_time:                        0.
% 3.85/1.00  monotx_time:                            0.001
% 3.85/1.00  subtype_inf_time:                       0.
% 3.85/1.00  
% 3.85/1.00  ------ Problem properties
% 3.85/1.00  
% 3.85/1.00  clauses:                                17
% 3.85/1.00  conjectures:                            4
% 3.85/1.00  epr:                                    4
% 3.85/1.00  horn:                                   14
% 3.85/1.00  ground:                                 2
% 3.85/1.00  unary:                                  3
% 3.85/1.00  binary:                                 9
% 3.85/1.00  lits:                                   36
% 3.85/1.00  lits_eq:                                7
% 3.85/1.00  fd_pure:                                0
% 3.85/1.00  fd_pseudo:                              0
% 3.85/1.00  fd_cond:                                0
% 3.85/1.00  fd_pseudo_cond:                         3
% 3.85/1.00  ac_symbols:                             0
% 3.85/1.00  
% 3.85/1.00  ------ Propositional Solver
% 3.85/1.00  
% 3.85/1.00  prop_solver_calls:                      29
% 3.85/1.00  prop_fast_solver_calls:                 803
% 3.85/1.00  smt_solver_calls:                       0
% 3.85/1.00  smt_fast_solver_calls:                  0
% 3.85/1.00  prop_num_of_clauses:                    4442
% 3.85/1.00  prop_preprocess_simplified:             11892
% 3.85/1.00  prop_fo_subsumed:                       15
% 3.85/1.00  prop_solver_time:                       0.
% 3.85/1.00  smt_solver_time:                        0.
% 3.85/1.00  smt_fast_solver_time:                   0.
% 3.85/1.00  prop_fast_solver_time:                  0.
% 3.85/1.00  prop_unsat_core_time:                   0.
% 3.85/1.00  
% 3.85/1.00  ------ QBF
% 3.85/1.00  
% 3.85/1.00  qbf_q_res:                              0
% 3.85/1.00  qbf_num_tautologies:                    0
% 3.85/1.00  qbf_prep_cycles:                        0
% 3.85/1.00  
% 3.85/1.00  ------ BMC1
% 3.85/1.00  
% 3.85/1.00  bmc1_current_bound:                     -1
% 3.85/1.00  bmc1_last_solved_bound:                 -1
% 3.85/1.00  bmc1_unsat_core_size:                   -1
% 3.85/1.00  bmc1_unsat_core_parents_size:           -1
% 3.85/1.00  bmc1_merge_next_fun:                    0
% 3.85/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation
% 3.85/1.00  
% 3.85/1.00  inst_num_of_clauses:                    1145
% 3.85/1.00  inst_num_in_passive:                    657
% 3.85/1.00  inst_num_in_active:                     392
% 3.85/1.00  inst_num_in_unprocessed:                96
% 3.85/1.00  inst_num_of_loops:                      560
% 3.85/1.00  inst_num_of_learning_restarts:          0
% 3.85/1.00  inst_num_moves_active_passive:          168
% 3.85/1.00  inst_lit_activity:                      0
% 3.85/1.00  inst_lit_activity_moves:                0
% 3.85/1.00  inst_num_tautologies:                   0
% 3.85/1.00  inst_num_prop_implied:                  0
% 3.85/1.00  inst_num_existing_simplified:           0
% 3.85/1.00  inst_num_eq_res_simplified:             0
% 3.85/1.00  inst_num_child_elim:                    0
% 3.85/1.00  inst_num_of_dismatching_blockings:      582
% 3.85/1.00  inst_num_of_non_proper_insts:           1253
% 3.85/1.00  inst_num_of_duplicates:                 0
% 3.85/1.00  inst_inst_num_from_inst_to_res:         0
% 3.85/1.00  inst_dismatching_checking_time:         0.
% 3.85/1.00  
% 3.85/1.00  ------ Resolution
% 3.85/1.00  
% 3.85/1.00  res_num_of_clauses:                     0
% 3.85/1.00  res_num_in_passive:                     0
% 3.85/1.00  res_num_in_active:                      0
% 3.85/1.00  res_num_of_loops:                       97
% 3.85/1.00  res_forward_subset_subsumed:            124
% 3.85/1.00  res_backward_subset_subsumed:           0
% 3.85/1.00  res_forward_subsumed:                   0
% 3.85/1.00  res_backward_subsumed:                  0
% 3.85/1.00  res_forward_subsumption_resolution:     0
% 3.85/1.00  res_backward_subsumption_resolution:    0
% 3.85/1.00  res_clause_to_clause_subsumption:       4004
% 3.85/1.00  res_orphan_elimination:                 0
% 3.85/1.00  res_tautology_del:                      183
% 3.85/1.00  res_num_eq_res_simplified:              0
% 3.85/1.00  res_num_sel_changes:                    0
% 3.85/1.00  res_moves_from_active_to_pass:          0
% 3.85/1.00  
% 3.85/1.00  ------ Superposition
% 3.85/1.00  
% 3.85/1.00  sup_time_total:                         0.
% 3.85/1.00  sup_time_generating:                    0.
% 3.85/1.00  sup_time_sim_full:                      0.
% 3.85/1.00  sup_time_sim_immed:                     0.
% 3.85/1.00  
% 3.85/1.00  sup_num_of_clauses:                     544
% 3.85/1.00  sup_num_in_active:                      30
% 3.85/1.00  sup_num_in_passive:                     514
% 3.85/1.00  sup_num_of_loops:                       110
% 3.85/1.00  sup_fw_superposition:                   523
% 3.85/1.00  sup_bw_superposition:                   367
% 3.85/1.00  sup_immediate_simplified:               102
% 3.85/1.00  sup_given_eliminated:                   0
% 3.85/1.00  comparisons_done:                       0
% 3.85/1.00  comparisons_avoided:                    28
% 3.85/1.00  
% 3.85/1.00  ------ Simplifications
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  sim_fw_subset_subsumed:                 49
% 3.85/1.00  sim_bw_subset_subsumed:                 11
% 3.85/1.00  sim_fw_subsumed:                        79
% 3.85/1.00  sim_bw_subsumed:                        2
% 3.85/1.00  sim_fw_subsumption_res:                 0
% 3.85/1.00  sim_bw_subsumption_res:                 0
% 3.85/1.00  sim_tautology_del:                      5
% 3.85/1.00  sim_eq_tautology_del:                   55
% 3.85/1.00  sim_eq_res_simp:                        2
% 3.85/1.00  sim_fw_demodulated:                     3
% 3.85/1.00  sim_bw_demodulated:                     74
% 3.85/1.00  sim_light_normalised:                   1
% 3.85/1.00  sim_joinable_taut:                      0
% 3.85/1.00  sim_joinable_simp:                      0
% 3.85/1.00  sim_ac_normalised:                      0
% 3.85/1.00  sim_smt_subsumption:                    0
% 3.85/1.00  
%------------------------------------------------------------------------------
