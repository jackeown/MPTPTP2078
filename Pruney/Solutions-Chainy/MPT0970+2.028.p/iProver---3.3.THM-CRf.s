%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:51 EST 2020

% Result     : Theorem 15.85s
% Output     : CNFRefutation 15.85s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 449 expanded)
%              Number of clauses        :   82 ( 155 expanded)
%              Number of leaves         :   18 ( 105 expanded)
%              Depth                    :   17
%              Number of atoms          :  414 (1890 expanded)
%              Number of equality atoms :  198 ( 625 expanded)
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

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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

fof(f38,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f37,f36])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2475,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),X0)
    | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ r1_tarski(k2_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_51349,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_51352,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51349])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_883,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_886,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1442,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_883,c_886])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3685,plain,
    ( sK3 = k1_xboole_0
    | k1_relset_1(sK2,sK3,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1442,c_27])).

cnf(c_3686,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3685])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_893,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1715,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_883,c_893])).

cnf(c_3687,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3686,c_1715])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_892,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1636,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_883,c_892])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_894,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2622,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_894])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3985,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2622,c_28])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_898,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3990,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3985,c_898])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_901,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_885,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1841,plain,
    ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
    | sK3 = X0
    | r2_hidden(sK1(X0,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_885])).

cnf(c_903,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7885,plain,
    ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
    | sK3 = X0
    | r2_hidden(sK1(X0,sK3),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_903])).

cnf(c_18473,plain,
    ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
    | sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7885,c_885])).

cnf(c_18758,plain,
    ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3)
    | k2_relat_1(sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_3990,c_18473])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2621,plain,
    ( k2_relat_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1636,c_20])).

cnf(c_49816,plain,
    ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18758,c_2621])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_897,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_49822,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_49816,c_897])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1117,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1118,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_50051,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49822,c_26,c_28,c_1118])).

cnf(c_50058,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3687,c_50051])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_900,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1882,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_903])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_896,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8505,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_896])).

cnf(c_12526,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_8505])).

cnf(c_12585,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12526,c_903])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_902,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) != iProver_top
    | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13065,plain,
    ( X0 = X1
    | r2_hidden(sK1(X0,X1),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12585,c_902])).

cnf(c_13363,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13065,c_12526])).

cnf(c_13375,plain,
    ( k2_relat_1(sK4) = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3990,c_13363])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10744,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_10745,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) != iProver_top
    | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10744])).

cnf(c_295,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_9806,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X1)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_9807,plain,
    ( sK3 != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9806])).

cnf(c_9809,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9807])).

cnf(c_2487,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2488,plain,
    ( sK3 = k2_relat_1(sK4)
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2487])).

cnf(c_1259,plain,
    ( r2_hidden(sK1(X0,sK3),X0)
    | r2_hidden(sK1(X0,sK3),sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1984,plain,
    ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_1985,plain,
    ( sK3 = k2_relat_1(sK4)
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_294,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1140,plain,
    ( k2_relset_1(sK2,sK3,sK4) != X0
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_1545,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | k2_relset_1(sK2,sK3,sK4) = sK3
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_77,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_79,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51352,c_50058,c_13375,c_10745,c_9809,c_3990,c_2621,c_2488,c_1985,c_1545,c_1159,c_79,c_20,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.85/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.85/2.50  
% 15.85/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.85/2.50  
% 15.85/2.50  ------  iProver source info
% 15.85/2.50  
% 15.85/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.85/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.85/2.50  git: non_committed_changes: false
% 15.85/2.50  git: last_make_outside_of_git: false
% 15.85/2.50  
% 15.85/2.50  ------ 
% 15.85/2.50  
% 15.85/2.50  ------ Input Options
% 15.85/2.50  
% 15.85/2.50  --out_options                           all
% 15.85/2.50  --tptp_safe_out                         true
% 15.85/2.50  --problem_path                          ""
% 15.85/2.50  --include_path                          ""
% 15.85/2.50  --clausifier                            res/vclausify_rel
% 15.85/2.50  --clausifier_options                    --mode clausify
% 15.85/2.50  --stdin                                 false
% 15.85/2.50  --stats_out                             sel
% 15.85/2.50  
% 15.85/2.50  ------ General Options
% 15.85/2.50  
% 15.85/2.50  --fof                                   false
% 15.85/2.50  --time_out_real                         604.99
% 15.85/2.50  --time_out_virtual                      -1.
% 15.85/2.50  --symbol_type_check                     false
% 15.85/2.50  --clausify_out                          false
% 15.85/2.50  --sig_cnt_out                           false
% 15.85/2.50  --trig_cnt_out                          false
% 15.85/2.50  --trig_cnt_out_tolerance                1.
% 15.85/2.50  --trig_cnt_out_sk_spl                   false
% 15.85/2.50  --abstr_cl_out                          false
% 15.85/2.50  
% 15.85/2.50  ------ Global Options
% 15.85/2.50  
% 15.85/2.50  --schedule                              none
% 15.85/2.50  --add_important_lit                     false
% 15.85/2.50  --prop_solver_per_cl                    1000
% 15.85/2.50  --min_unsat_core                        false
% 15.85/2.50  --soft_assumptions                      false
% 15.85/2.50  --soft_lemma_size                       3
% 15.85/2.50  --prop_impl_unit_size                   0
% 15.85/2.50  --prop_impl_unit                        []
% 15.85/2.50  --share_sel_clauses                     true
% 15.85/2.50  --reset_solvers                         false
% 15.85/2.50  --bc_imp_inh                            [conj_cone]
% 15.85/2.50  --conj_cone_tolerance                   3.
% 15.85/2.50  --extra_neg_conj                        none
% 15.85/2.50  --large_theory_mode                     true
% 15.85/2.50  --prolific_symb_bound                   200
% 15.85/2.50  --lt_threshold                          2000
% 15.85/2.50  --clause_weak_htbl                      true
% 15.85/2.50  --gc_record_bc_elim                     false
% 15.85/2.50  
% 15.85/2.50  ------ Preprocessing Options
% 15.85/2.50  
% 15.85/2.50  --preprocessing_flag                    true
% 15.85/2.50  --time_out_prep_mult                    0.1
% 15.85/2.50  --splitting_mode                        input
% 15.85/2.50  --splitting_grd                         true
% 15.85/2.50  --splitting_cvd                         false
% 15.85/2.50  --splitting_cvd_svl                     false
% 15.85/2.50  --splitting_nvd                         32
% 15.85/2.50  --sub_typing                            true
% 15.85/2.50  --prep_gs_sim                           false
% 15.85/2.50  --prep_unflatten                        true
% 15.85/2.50  --prep_res_sim                          true
% 15.85/2.50  --prep_upred                            true
% 15.85/2.50  --prep_sem_filter                       exhaustive
% 15.85/2.50  --prep_sem_filter_out                   false
% 15.85/2.50  --pred_elim                             false
% 15.85/2.50  --res_sim_input                         true
% 15.85/2.50  --eq_ax_congr_red                       true
% 15.85/2.50  --pure_diseq_elim                       true
% 15.85/2.50  --brand_transform                       false
% 15.85/2.50  --non_eq_to_eq                          false
% 15.85/2.50  --prep_def_merge                        true
% 15.85/2.50  --prep_def_merge_prop_impl              false
% 15.85/2.50  --prep_def_merge_mbd                    true
% 15.85/2.50  --prep_def_merge_tr_red                 false
% 15.85/2.50  --prep_def_merge_tr_cl                  false
% 15.85/2.50  --smt_preprocessing                     true
% 15.85/2.50  --smt_ac_axioms                         fast
% 15.85/2.50  --preprocessed_out                      false
% 15.85/2.50  --preprocessed_stats                    false
% 15.85/2.50  
% 15.85/2.50  ------ Abstraction refinement Options
% 15.85/2.50  
% 15.85/2.50  --abstr_ref                             []
% 15.85/2.50  --abstr_ref_prep                        false
% 15.85/2.50  --abstr_ref_until_sat                   false
% 15.85/2.50  --abstr_ref_sig_restrict                funpre
% 15.85/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.85/2.50  --abstr_ref_under                       []
% 15.85/2.50  
% 15.85/2.50  ------ SAT Options
% 15.85/2.50  
% 15.85/2.50  --sat_mode                              false
% 15.85/2.50  --sat_fm_restart_options                ""
% 15.85/2.50  --sat_gr_def                            false
% 15.85/2.50  --sat_epr_types                         true
% 15.85/2.50  --sat_non_cyclic_types                  false
% 15.85/2.50  --sat_finite_models                     false
% 15.85/2.50  --sat_fm_lemmas                         false
% 15.85/2.50  --sat_fm_prep                           false
% 15.85/2.50  --sat_fm_uc_incr                        true
% 15.85/2.50  --sat_out_model                         small
% 15.85/2.50  --sat_out_clauses                       false
% 15.85/2.50  
% 15.85/2.50  ------ QBF Options
% 15.85/2.50  
% 15.85/2.50  --qbf_mode                              false
% 15.85/2.50  --qbf_elim_univ                         false
% 15.85/2.50  --qbf_dom_inst                          none
% 15.85/2.50  --qbf_dom_pre_inst                      false
% 15.85/2.50  --qbf_sk_in                             false
% 15.85/2.50  --qbf_pred_elim                         true
% 15.85/2.50  --qbf_split                             512
% 15.85/2.50  
% 15.85/2.50  ------ BMC1 Options
% 15.85/2.50  
% 15.85/2.50  --bmc1_incremental                      false
% 15.85/2.50  --bmc1_axioms                           reachable_all
% 15.85/2.50  --bmc1_min_bound                        0
% 15.85/2.50  --bmc1_max_bound                        -1
% 15.85/2.50  --bmc1_max_bound_default                -1
% 15.85/2.50  --bmc1_symbol_reachability              true
% 15.85/2.50  --bmc1_property_lemmas                  false
% 15.85/2.50  --bmc1_k_induction                      false
% 15.85/2.50  --bmc1_non_equiv_states                 false
% 15.85/2.50  --bmc1_deadlock                         false
% 15.85/2.50  --bmc1_ucm                              false
% 15.85/2.50  --bmc1_add_unsat_core                   none
% 15.85/2.50  --bmc1_unsat_core_children              false
% 15.85/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.85/2.50  --bmc1_out_stat                         full
% 15.85/2.50  --bmc1_ground_init                      false
% 15.85/2.50  --bmc1_pre_inst_next_state              false
% 15.85/2.50  --bmc1_pre_inst_state                   false
% 15.85/2.50  --bmc1_pre_inst_reach_state             false
% 15.85/2.50  --bmc1_out_unsat_core                   false
% 15.85/2.50  --bmc1_aig_witness_out                  false
% 15.85/2.50  --bmc1_verbose                          false
% 15.85/2.50  --bmc1_dump_clauses_tptp                false
% 15.85/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.85/2.50  --bmc1_dump_file                        -
% 15.85/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.85/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.85/2.50  --bmc1_ucm_extend_mode                  1
% 15.85/2.50  --bmc1_ucm_init_mode                    2
% 15.85/2.50  --bmc1_ucm_cone_mode                    none
% 15.85/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.85/2.50  --bmc1_ucm_relax_model                  4
% 15.85/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.85/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.85/2.50  --bmc1_ucm_layered_model                none
% 15.85/2.50  --bmc1_ucm_max_lemma_size               10
% 15.85/2.50  
% 15.85/2.50  ------ AIG Options
% 15.85/2.50  
% 15.85/2.50  --aig_mode                              false
% 15.85/2.50  
% 15.85/2.50  ------ Instantiation Options
% 15.85/2.50  
% 15.85/2.50  --instantiation_flag                    true
% 15.85/2.50  --inst_sos_flag                         false
% 15.85/2.50  --inst_sos_phase                        true
% 15.85/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.85/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.85/2.50  --inst_lit_sel_side                     num_symb
% 15.85/2.50  --inst_solver_per_active                1400
% 15.85/2.50  --inst_solver_calls_frac                1.
% 15.85/2.50  --inst_passive_queue_type               priority_queues
% 15.85/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.85/2.50  --inst_passive_queues_freq              [25;2]
% 15.85/2.50  --inst_dismatching                      true
% 15.85/2.50  --inst_eager_unprocessed_to_passive     true
% 15.85/2.50  --inst_prop_sim_given                   true
% 15.85/2.50  --inst_prop_sim_new                     false
% 15.85/2.50  --inst_subs_new                         false
% 15.85/2.50  --inst_eq_res_simp                      false
% 15.85/2.50  --inst_subs_given                       false
% 15.85/2.50  --inst_orphan_elimination               true
% 15.85/2.50  --inst_learning_loop_flag               true
% 15.85/2.50  --inst_learning_start                   3000
% 15.85/2.50  --inst_learning_factor                  2
% 15.85/2.50  --inst_start_prop_sim_after_learn       3
% 15.85/2.50  --inst_sel_renew                        solver
% 15.85/2.50  --inst_lit_activity_flag                true
% 15.85/2.50  --inst_restr_to_given                   false
% 15.85/2.50  --inst_activity_threshold               500
% 15.85/2.50  --inst_out_proof                        true
% 15.85/2.50  
% 15.85/2.50  ------ Resolution Options
% 15.85/2.50  
% 15.85/2.50  --resolution_flag                       true
% 15.85/2.50  --res_lit_sel                           adaptive
% 15.85/2.50  --res_lit_sel_side                      none
% 15.85/2.50  --res_ordering                          kbo
% 15.85/2.50  --res_to_prop_solver                    active
% 15.85/2.50  --res_prop_simpl_new                    false
% 15.85/2.50  --res_prop_simpl_given                  true
% 15.85/2.50  --res_passive_queue_type                priority_queues
% 15.85/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.85/2.50  --res_passive_queues_freq               [15;5]
% 15.85/2.50  --res_forward_subs                      full
% 15.85/2.50  --res_backward_subs                     full
% 15.85/2.50  --res_forward_subs_resolution           true
% 15.85/2.50  --res_backward_subs_resolution          true
% 15.85/2.50  --res_orphan_elimination                true
% 15.85/2.50  --res_time_limit                        2.
% 15.85/2.50  --res_out_proof                         true
% 15.85/2.50  
% 15.85/2.50  ------ Superposition Options
% 15.85/2.50  
% 15.85/2.50  --superposition_flag                    true
% 15.85/2.50  --sup_passive_queue_type                priority_queues
% 15.85/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.85/2.50  --sup_passive_queues_freq               [1;4]
% 15.85/2.50  --demod_completeness_check              fast
% 15.85/2.50  --demod_use_ground                      true
% 15.85/2.50  --sup_to_prop_solver                    passive
% 15.85/2.50  --sup_prop_simpl_new                    true
% 15.85/2.50  --sup_prop_simpl_given                  true
% 15.85/2.50  --sup_fun_splitting                     false
% 15.85/2.50  --sup_smt_interval                      50000
% 15.85/2.50  
% 15.85/2.50  ------ Superposition Simplification Setup
% 15.85/2.50  
% 15.85/2.50  --sup_indices_passive                   []
% 15.85/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.85/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.85/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.85/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.85/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.85/2.50  --sup_full_bw                           [BwDemod]
% 15.85/2.50  --sup_immed_triv                        [TrivRules]
% 15.85/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.85/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.85/2.50  --sup_immed_bw_main                     []
% 15.85/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.85/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.85/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.85/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.85/2.50  
% 15.85/2.50  ------ Combination Options
% 15.85/2.50  
% 15.85/2.50  --comb_res_mult                         3
% 15.85/2.50  --comb_sup_mult                         2
% 15.85/2.50  --comb_inst_mult                        10
% 15.85/2.50  
% 15.85/2.50  ------ Debug Options
% 15.85/2.50  
% 15.85/2.50  --dbg_backtrace                         false
% 15.85/2.50  --dbg_dump_prop_clauses                 false
% 15.85/2.50  --dbg_dump_prop_clauses_file            -
% 15.85/2.50  --dbg_out_stat                          false
% 15.85/2.50  ------ Parsing...
% 15.85/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.85/2.50  
% 15.85/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.85/2.50  
% 15.85/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.85/2.50  
% 15.85/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.85/2.50  ------ Proving...
% 15.85/2.50  ------ Problem Properties 
% 15.85/2.50  
% 15.85/2.50  
% 15.85/2.50  clauses                                 26
% 15.85/2.50  conjectures                             6
% 15.85/2.50  EPR                                     5
% 15.85/2.50  Horn                                    20
% 15.85/2.50  unary                                   5
% 15.85/2.50  binary                                  11
% 15.85/2.50  lits                                    61
% 15.85/2.50  lits eq                                 15
% 15.85/2.50  fd_pure                                 0
% 15.85/2.50  fd_pseudo                               0
% 15.85/2.50  fd_cond                                 3
% 15.85/2.50  fd_pseudo_cond                          2
% 15.85/2.50  AC symbols                              0
% 15.85/2.50  
% 15.85/2.50  ------ Input Options Time Limit: Unbounded
% 15.85/2.50  
% 15.85/2.50  
% 15.85/2.50  ------ 
% 15.85/2.50  Current options:
% 15.85/2.50  ------ 
% 15.85/2.50  
% 15.85/2.50  ------ Input Options
% 15.85/2.50  
% 15.85/2.50  --out_options                           all
% 15.85/2.50  --tptp_safe_out                         true
% 15.85/2.50  --problem_path                          ""
% 15.85/2.50  --include_path                          ""
% 15.85/2.50  --clausifier                            res/vclausify_rel
% 15.85/2.50  --clausifier_options                    --mode clausify
% 15.85/2.50  --stdin                                 false
% 15.85/2.50  --stats_out                             sel
% 15.85/2.50  
% 15.85/2.50  ------ General Options
% 15.85/2.50  
% 15.85/2.50  --fof                                   false
% 15.85/2.50  --time_out_real                         604.99
% 15.85/2.50  --time_out_virtual                      -1.
% 15.85/2.50  --symbol_type_check                     false
% 15.85/2.50  --clausify_out                          false
% 15.85/2.50  --sig_cnt_out                           false
% 15.85/2.50  --trig_cnt_out                          false
% 15.85/2.50  --trig_cnt_out_tolerance                1.
% 15.85/2.50  --trig_cnt_out_sk_spl                   false
% 15.85/2.50  --abstr_cl_out                          false
% 15.85/2.50  
% 15.85/2.50  ------ Global Options
% 15.85/2.50  
% 15.85/2.50  --schedule                              none
% 15.85/2.50  --add_important_lit                     false
% 15.85/2.50  --prop_solver_per_cl                    1000
% 15.85/2.50  --min_unsat_core                        false
% 15.85/2.50  --soft_assumptions                      false
% 15.85/2.50  --soft_lemma_size                       3
% 15.85/2.50  --prop_impl_unit_size                   0
% 15.85/2.50  --prop_impl_unit                        []
% 15.85/2.50  --share_sel_clauses                     true
% 15.85/2.50  --reset_solvers                         false
% 15.85/2.50  --bc_imp_inh                            [conj_cone]
% 15.85/2.50  --conj_cone_tolerance                   3.
% 15.85/2.50  --extra_neg_conj                        none
% 15.85/2.50  --large_theory_mode                     true
% 15.85/2.50  --prolific_symb_bound                   200
% 15.85/2.50  --lt_threshold                          2000
% 15.85/2.50  --clause_weak_htbl                      true
% 15.85/2.50  --gc_record_bc_elim                     false
% 15.85/2.50  
% 15.85/2.50  ------ Preprocessing Options
% 15.85/2.50  
% 15.85/2.50  --preprocessing_flag                    true
% 15.85/2.50  --time_out_prep_mult                    0.1
% 15.85/2.50  --splitting_mode                        input
% 15.85/2.50  --splitting_grd                         true
% 15.85/2.50  --splitting_cvd                         false
% 15.85/2.50  --splitting_cvd_svl                     false
% 15.85/2.50  --splitting_nvd                         32
% 15.85/2.50  --sub_typing                            true
% 15.85/2.50  --prep_gs_sim                           false
% 15.85/2.50  --prep_unflatten                        true
% 15.85/2.50  --prep_res_sim                          true
% 15.85/2.50  --prep_upred                            true
% 15.85/2.50  --prep_sem_filter                       exhaustive
% 15.85/2.50  --prep_sem_filter_out                   false
% 15.85/2.50  --pred_elim                             false
% 15.85/2.50  --res_sim_input                         true
% 15.85/2.50  --eq_ax_congr_red                       true
% 15.85/2.50  --pure_diseq_elim                       true
% 15.85/2.50  --brand_transform                       false
% 15.85/2.50  --non_eq_to_eq                          false
% 15.85/2.50  --prep_def_merge                        true
% 15.85/2.50  --prep_def_merge_prop_impl              false
% 15.85/2.50  --prep_def_merge_mbd                    true
% 15.85/2.50  --prep_def_merge_tr_red                 false
% 15.85/2.50  --prep_def_merge_tr_cl                  false
% 15.85/2.50  --smt_preprocessing                     true
% 15.85/2.50  --smt_ac_axioms                         fast
% 15.85/2.50  --preprocessed_out                      false
% 15.85/2.50  --preprocessed_stats                    false
% 15.85/2.50  
% 15.85/2.50  ------ Abstraction refinement Options
% 15.85/2.50  
% 15.85/2.50  --abstr_ref                             []
% 15.85/2.50  --abstr_ref_prep                        false
% 15.85/2.50  --abstr_ref_until_sat                   false
% 15.85/2.50  --abstr_ref_sig_restrict                funpre
% 15.85/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.85/2.50  --abstr_ref_under                       []
% 15.85/2.50  
% 15.85/2.50  ------ SAT Options
% 15.85/2.50  
% 15.85/2.50  --sat_mode                              false
% 15.85/2.50  --sat_fm_restart_options                ""
% 15.85/2.50  --sat_gr_def                            false
% 15.85/2.50  --sat_epr_types                         true
% 15.85/2.50  --sat_non_cyclic_types                  false
% 15.85/2.50  --sat_finite_models                     false
% 15.85/2.50  --sat_fm_lemmas                         false
% 15.85/2.50  --sat_fm_prep                           false
% 15.85/2.50  --sat_fm_uc_incr                        true
% 15.85/2.50  --sat_out_model                         small
% 15.85/2.50  --sat_out_clauses                       false
% 15.85/2.50  
% 15.85/2.50  ------ QBF Options
% 15.85/2.50  
% 15.85/2.50  --qbf_mode                              false
% 15.85/2.50  --qbf_elim_univ                         false
% 15.85/2.50  --qbf_dom_inst                          none
% 15.85/2.50  --qbf_dom_pre_inst                      false
% 15.85/2.50  --qbf_sk_in                             false
% 15.85/2.50  --qbf_pred_elim                         true
% 15.85/2.50  --qbf_split                             512
% 15.85/2.50  
% 15.85/2.50  ------ BMC1 Options
% 15.85/2.50  
% 15.85/2.50  --bmc1_incremental                      false
% 15.85/2.50  --bmc1_axioms                           reachable_all
% 15.85/2.50  --bmc1_min_bound                        0
% 15.85/2.50  --bmc1_max_bound                        -1
% 15.85/2.50  --bmc1_max_bound_default                -1
% 15.85/2.50  --bmc1_symbol_reachability              true
% 15.85/2.50  --bmc1_property_lemmas                  false
% 15.85/2.50  --bmc1_k_induction                      false
% 15.85/2.50  --bmc1_non_equiv_states                 false
% 15.85/2.50  --bmc1_deadlock                         false
% 15.85/2.50  --bmc1_ucm                              false
% 15.85/2.50  --bmc1_add_unsat_core                   none
% 15.85/2.50  --bmc1_unsat_core_children              false
% 15.85/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.85/2.50  --bmc1_out_stat                         full
% 15.85/2.50  --bmc1_ground_init                      false
% 15.85/2.50  --bmc1_pre_inst_next_state              false
% 15.85/2.50  --bmc1_pre_inst_state                   false
% 15.85/2.50  --bmc1_pre_inst_reach_state             false
% 15.85/2.50  --bmc1_out_unsat_core                   false
% 15.85/2.50  --bmc1_aig_witness_out                  false
% 15.85/2.50  --bmc1_verbose                          false
% 15.85/2.50  --bmc1_dump_clauses_tptp                false
% 15.85/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.85/2.50  --bmc1_dump_file                        -
% 15.85/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.85/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.85/2.50  --bmc1_ucm_extend_mode                  1
% 15.85/2.50  --bmc1_ucm_init_mode                    2
% 15.85/2.50  --bmc1_ucm_cone_mode                    none
% 15.85/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.85/2.50  --bmc1_ucm_relax_model                  4
% 15.85/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.85/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.85/2.50  --bmc1_ucm_layered_model                none
% 15.85/2.50  --bmc1_ucm_max_lemma_size               10
% 15.85/2.50  
% 15.85/2.50  ------ AIG Options
% 15.85/2.50  
% 15.85/2.50  --aig_mode                              false
% 15.85/2.50  
% 15.85/2.50  ------ Instantiation Options
% 15.85/2.50  
% 15.85/2.50  --instantiation_flag                    true
% 15.85/2.50  --inst_sos_flag                         false
% 15.85/2.50  --inst_sos_phase                        true
% 15.85/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.85/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.85/2.50  --inst_lit_sel_side                     num_symb
% 15.85/2.50  --inst_solver_per_active                1400
% 15.85/2.50  --inst_solver_calls_frac                1.
% 15.85/2.50  --inst_passive_queue_type               priority_queues
% 15.85/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.85/2.50  --inst_passive_queues_freq              [25;2]
% 15.85/2.50  --inst_dismatching                      true
% 15.85/2.50  --inst_eager_unprocessed_to_passive     true
% 15.85/2.50  --inst_prop_sim_given                   true
% 15.85/2.50  --inst_prop_sim_new                     false
% 15.85/2.50  --inst_subs_new                         false
% 15.85/2.50  --inst_eq_res_simp                      false
% 15.85/2.50  --inst_subs_given                       false
% 15.85/2.50  --inst_orphan_elimination               true
% 15.85/2.50  --inst_learning_loop_flag               true
% 15.85/2.50  --inst_learning_start                   3000
% 15.85/2.50  --inst_learning_factor                  2
% 15.85/2.50  --inst_start_prop_sim_after_learn       3
% 15.85/2.50  --inst_sel_renew                        solver
% 15.85/2.50  --inst_lit_activity_flag                true
% 15.85/2.50  --inst_restr_to_given                   false
% 15.85/2.50  --inst_activity_threshold               500
% 15.85/2.50  --inst_out_proof                        true
% 15.85/2.50  
% 15.85/2.50  ------ Resolution Options
% 15.85/2.50  
% 15.85/2.50  --resolution_flag                       true
% 15.85/2.50  --res_lit_sel                           adaptive
% 15.85/2.50  --res_lit_sel_side                      none
% 15.85/2.50  --res_ordering                          kbo
% 15.85/2.50  --res_to_prop_solver                    active
% 15.85/2.50  --res_prop_simpl_new                    false
% 15.85/2.50  --res_prop_simpl_given                  true
% 15.85/2.50  --res_passive_queue_type                priority_queues
% 15.85/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.85/2.50  --res_passive_queues_freq               [15;5]
% 15.85/2.50  --res_forward_subs                      full
% 15.85/2.50  --res_backward_subs                     full
% 15.85/2.50  --res_forward_subs_resolution           true
% 15.85/2.50  --res_backward_subs_resolution          true
% 15.85/2.50  --res_orphan_elimination                true
% 15.85/2.50  --res_time_limit                        2.
% 15.85/2.50  --res_out_proof                         true
% 15.85/2.50  
% 15.85/2.50  ------ Superposition Options
% 15.85/2.50  
% 15.85/2.50  --superposition_flag                    true
% 15.85/2.50  --sup_passive_queue_type                priority_queues
% 15.85/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.85/2.50  --sup_passive_queues_freq               [1;4]
% 15.85/2.50  --demod_completeness_check              fast
% 15.85/2.50  --demod_use_ground                      true
% 15.85/2.50  --sup_to_prop_solver                    passive
% 15.85/2.50  --sup_prop_simpl_new                    true
% 15.85/2.50  --sup_prop_simpl_given                  true
% 15.85/2.50  --sup_fun_splitting                     false
% 15.85/2.50  --sup_smt_interval                      50000
% 15.85/2.50  
% 15.85/2.50  ------ Superposition Simplification Setup
% 15.85/2.50  
% 15.85/2.50  --sup_indices_passive                   []
% 15.85/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.85/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.85/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.85/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.85/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.85/2.50  --sup_full_bw                           [BwDemod]
% 15.85/2.50  --sup_immed_triv                        [TrivRules]
% 15.85/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.85/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.85/2.50  --sup_immed_bw_main                     []
% 15.85/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.85/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.85/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.85/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.85/2.50  
% 15.85/2.50  ------ Combination Options
% 15.85/2.50  
% 15.85/2.50  --comb_res_mult                         3
% 15.85/2.50  --comb_sup_mult                         2
% 15.85/2.50  --comb_inst_mult                        10
% 15.85/2.50  
% 15.85/2.50  ------ Debug Options
% 15.85/2.50  
% 15.85/2.50  --dbg_backtrace                         false
% 15.85/2.50  --dbg_dump_prop_clauses                 false
% 15.85/2.50  --dbg_dump_prop_clauses_file            -
% 15.85/2.50  --dbg_out_stat                          false
% 15.85/2.50  
% 15.85/2.50  
% 15.85/2.50  
% 15.85/2.50  
% 15.85/2.50  ------ Proving...
% 15.85/2.50  
% 15.85/2.50  
% 15.85/2.50  % SZS status Theorem for theBenchmark.p
% 15.85/2.50  
% 15.85/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.85/2.50  
% 15.85/2.50  fof(f1,axiom,(
% 15.85/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f14,plain,(
% 15.85/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.85/2.50    inference(ennf_transformation,[],[f1])).
% 15.85/2.50  
% 15.85/2.50  fof(f27,plain,(
% 15.85/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.85/2.50    inference(nnf_transformation,[],[f14])).
% 15.85/2.50  
% 15.85/2.50  fof(f28,plain,(
% 15.85/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.85/2.50    inference(rectify,[],[f27])).
% 15.85/2.50  
% 15.85/2.50  fof(f29,plain,(
% 15.85/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.85/2.50    introduced(choice_axiom,[])).
% 15.85/2.50  
% 15.85/2.50  fof(f30,plain,(
% 15.85/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.85/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 15.85/2.50  
% 15.85/2.50  fof(f39,plain,(
% 15.85/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f30])).
% 15.85/2.50  
% 15.85/2.50  fof(f12,conjecture,(
% 15.85/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f13,negated_conjecture,(
% 15.85/2.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.85/2.50    inference(negated_conjecture,[],[f12])).
% 15.85/2.50  
% 15.85/2.50  fof(f25,plain,(
% 15.85/2.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.85/2.50    inference(ennf_transformation,[],[f13])).
% 15.85/2.50  
% 15.85/2.50  fof(f26,plain,(
% 15.85/2.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.85/2.50    inference(flattening,[],[f25])).
% 15.85/2.50  
% 15.85/2.50  fof(f37,plain,(
% 15.85/2.50    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 15.85/2.50    introduced(choice_axiom,[])).
% 15.85/2.50  
% 15.85/2.50  fof(f36,plain,(
% 15.85/2.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 15.85/2.50    introduced(choice_axiom,[])).
% 15.85/2.50  
% 15.85/2.50  fof(f38,plain,(
% 15.85/2.50    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 15.85/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f37,f36])).
% 15.85/2.50  
% 15.85/2.50  fof(f61,plain,(
% 15.85/2.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 15.85/2.50    inference(cnf_transformation,[],[f38])).
% 15.85/2.50  
% 15.85/2.50  fof(f11,axiom,(
% 15.85/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f23,plain,(
% 15.85/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.85/2.50    inference(ennf_transformation,[],[f11])).
% 15.85/2.50  
% 15.85/2.50  fof(f24,plain,(
% 15.85/2.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.85/2.50    inference(flattening,[],[f23])).
% 15.85/2.50  
% 15.85/2.50  fof(f35,plain,(
% 15.85/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.85/2.50    inference(nnf_transformation,[],[f24])).
% 15.85/2.50  
% 15.85/2.50  fof(f53,plain,(
% 15.85/2.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.85/2.50    inference(cnf_transformation,[],[f35])).
% 15.85/2.50  
% 15.85/2.50  fof(f60,plain,(
% 15.85/2.50    v1_funct_2(sK4,sK2,sK3)),
% 15.85/2.50    inference(cnf_transformation,[],[f38])).
% 15.85/2.50  
% 15.85/2.50  fof(f9,axiom,(
% 15.85/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f21,plain,(
% 15.85/2.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.85/2.50    inference(ennf_transformation,[],[f9])).
% 15.85/2.50  
% 15.85/2.50  fof(f51,plain,(
% 15.85/2.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.85/2.50    inference(cnf_transformation,[],[f21])).
% 15.85/2.50  
% 15.85/2.50  fof(f10,axiom,(
% 15.85/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f22,plain,(
% 15.85/2.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.85/2.50    inference(ennf_transformation,[],[f10])).
% 15.85/2.50  
% 15.85/2.50  fof(f52,plain,(
% 15.85/2.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.85/2.50    inference(cnf_transformation,[],[f22])).
% 15.85/2.50  
% 15.85/2.50  fof(f8,axiom,(
% 15.85/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f20,plain,(
% 15.85/2.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.85/2.50    inference(ennf_transformation,[],[f8])).
% 15.85/2.50  
% 15.85/2.50  fof(f50,plain,(
% 15.85/2.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.85/2.50    inference(cnf_transformation,[],[f20])).
% 15.85/2.50  
% 15.85/2.50  fof(f4,axiom,(
% 15.85/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f34,plain,(
% 15.85/2.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.85/2.50    inference(nnf_transformation,[],[f4])).
% 15.85/2.50  
% 15.85/2.50  fof(f45,plain,(
% 15.85/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.85/2.50    inference(cnf_transformation,[],[f34])).
% 15.85/2.50  
% 15.85/2.50  fof(f2,axiom,(
% 15.85/2.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f15,plain,(
% 15.85/2.50    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 15.85/2.50    inference(ennf_transformation,[],[f2])).
% 15.85/2.50  
% 15.85/2.50  fof(f31,plain,(
% 15.85/2.50    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 15.85/2.50    inference(nnf_transformation,[],[f15])).
% 15.85/2.50  
% 15.85/2.50  fof(f32,plain,(
% 15.85/2.50    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 15.85/2.50    introduced(choice_axiom,[])).
% 15.85/2.50  
% 15.85/2.50  fof(f33,plain,(
% 15.85/2.50    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 15.85/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 15.85/2.50  
% 15.85/2.50  fof(f42,plain,(
% 15.85/2.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f33])).
% 15.85/2.50  
% 15.85/2.50  fof(f63,plain,(
% 15.85/2.50    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f38])).
% 15.85/2.50  
% 15.85/2.50  fof(f64,plain,(
% 15.85/2.50    k2_relset_1(sK2,sK3,sK4) != sK3),
% 15.85/2.50    inference(cnf_transformation,[],[f38])).
% 15.85/2.50  
% 15.85/2.50  fof(f5,axiom,(
% 15.85/2.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f16,plain,(
% 15.85/2.50    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.85/2.50    inference(ennf_transformation,[],[f5])).
% 15.85/2.50  
% 15.85/2.50  fof(f17,plain,(
% 15.85/2.50    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.85/2.50    inference(flattening,[],[f16])).
% 15.85/2.50  
% 15.85/2.50  fof(f47,plain,(
% 15.85/2.50    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f17])).
% 15.85/2.50  
% 15.85/2.50  fof(f59,plain,(
% 15.85/2.50    v1_funct_1(sK4)),
% 15.85/2.50    inference(cnf_transformation,[],[f38])).
% 15.85/2.50  
% 15.85/2.50  fof(f7,axiom,(
% 15.85/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f19,plain,(
% 15.85/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.85/2.50    inference(ennf_transformation,[],[f7])).
% 15.85/2.50  
% 15.85/2.50  fof(f49,plain,(
% 15.85/2.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.85/2.50    inference(cnf_transformation,[],[f19])).
% 15.85/2.50  
% 15.85/2.50  fof(f3,axiom,(
% 15.85/2.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f44,plain,(
% 15.85/2.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f3])).
% 15.85/2.50  
% 15.85/2.50  fof(f6,axiom,(
% 15.85/2.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 15.85/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.85/2.50  
% 15.85/2.50  fof(f18,plain,(
% 15.85/2.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 15.85/2.50    inference(ennf_transformation,[],[f6])).
% 15.85/2.50  
% 15.85/2.50  fof(f48,plain,(
% 15.85/2.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f18])).
% 15.85/2.50  
% 15.85/2.50  fof(f43,plain,(
% 15.85/2.50    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f33])).
% 15.85/2.50  
% 15.85/2.50  fof(f62,plain,(
% 15.85/2.50    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 15.85/2.50    inference(cnf_transformation,[],[f38])).
% 15.85/2.50  
% 15.85/2.50  cnf(c_2,plain,
% 15.85/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.85/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_2475,plain,
% 15.85/2.50      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),X0)
% 15.85/2.50      | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 15.85/2.50      | ~ r1_tarski(k2_relat_1(sK4),X0) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_51349,plain,
% 15.85/2.50      ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 15.85/2.50      | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_2475]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_51352,plain,
% 15.85/2.50      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) != iProver_top
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) = iProver_top
% 15.85/2.50      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_51349]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_23,negated_conjecture,
% 15.85/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 15.85/2.50      inference(cnf_transformation,[],[f61]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_883,plain,
% 15.85/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_19,plain,
% 15.85/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.85/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.85/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.85/2.50      | k1_xboole_0 = X2 ),
% 15.85/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_886,plain,
% 15.85/2.50      ( k1_relset_1(X0,X1,X2) = X0
% 15.85/2.50      | k1_xboole_0 = X1
% 15.85/2.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.85/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1442,plain,
% 15.85/2.50      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 15.85/2.50      | sK3 = k1_xboole_0
% 15.85/2.50      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_883,c_886]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_24,negated_conjecture,
% 15.85/2.50      ( v1_funct_2(sK4,sK2,sK3) ),
% 15.85/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_27,plain,
% 15.85/2.50      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_3685,plain,
% 15.85/2.50      ( sK3 = k1_xboole_0 | k1_relset_1(sK2,sK3,sK4) = sK2 ),
% 15.85/2.50      inference(global_propositional_subsumption,
% 15.85/2.50                [status(thm)],
% 15.85/2.50                [c_1442,c_27]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_3686,plain,
% 15.85/2.50      ( k1_relset_1(sK2,sK3,sK4) = sK2 | sK3 = k1_xboole_0 ),
% 15.85/2.50      inference(renaming,[status(thm)],[c_3685]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_12,plain,
% 15.85/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.85/2.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.85/2.50      inference(cnf_transformation,[],[f51]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_893,plain,
% 15.85/2.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.85/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1715,plain,
% 15.85/2.50      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_883,c_893]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_3687,plain,
% 15.85/2.50      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 15.85/2.50      inference(demodulation,[status(thm)],[c_3686,c_1715]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_13,plain,
% 15.85/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.85/2.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.85/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_892,plain,
% 15.85/2.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.85/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1636,plain,
% 15.85/2.50      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_883,c_892]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_11,plain,
% 15.85/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.85/2.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 15.85/2.50      inference(cnf_transformation,[],[f50]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_894,plain,
% 15.85/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.85/2.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_2622,plain,
% 15.85/2.50      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 15.85/2.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_1636,c_894]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_28,plain,
% 15.85/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_3985,plain,
% 15.85/2.50      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 15.85/2.50      inference(global_propositional_subsumption,
% 15.85/2.50                [status(thm)],
% 15.85/2.50                [c_2622,c_28]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_7,plain,
% 15.85/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.85/2.50      inference(cnf_transformation,[],[f45]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_898,plain,
% 15.85/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.85/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_3990,plain,
% 15.85/2.50      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_3985,c_898]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_4,plain,
% 15.85/2.50      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 15.85/2.50      inference(cnf_transformation,[],[f42]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_901,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 15.85/2.50      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_21,negated_conjecture,
% 15.85/2.50      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 15.85/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_885,plain,
% 15.85/2.50      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1841,plain,
% 15.85/2.50      ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
% 15.85/2.50      | sK3 = X0
% 15.85/2.50      | r2_hidden(sK1(X0,sK3),X0) = iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_901,c_885]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_903,plain,
% 15.85/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.85/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.85/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_7885,plain,
% 15.85/2.50      ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
% 15.85/2.50      | sK3 = X0
% 15.85/2.50      | r2_hidden(sK1(X0,sK3),X1) = iProver_top
% 15.85/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_1841,c_903]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_18473,plain,
% 15.85/2.50      ( k1_funct_1(sK4,sK5(sK1(X0,sK3))) = sK1(X0,sK3)
% 15.85/2.50      | sK3 = X0
% 15.85/2.50      | r1_tarski(X0,sK3) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_7885,c_885]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_18758,plain,
% 15.85/2.50      ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3)
% 15.85/2.50      | k2_relat_1(sK4) = sK3 ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_3990,c_18473]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_20,negated_conjecture,
% 15.85/2.50      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 15.85/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_2621,plain,
% 15.85/2.50      ( k2_relat_1(sK4) != sK3 ),
% 15.85/2.50      inference(demodulation,[status(thm)],[c_1636,c_20]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_49816,plain,
% 15.85/2.50      ( k1_funct_1(sK4,sK5(sK1(k2_relat_1(sK4),sK3))) = sK1(k2_relat_1(sK4),sK3) ),
% 15.85/2.50      inference(global_propositional_subsumption,
% 15.85/2.50                [status(thm)],
% 15.85/2.50                [c_18758,c_2621]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_8,plain,
% 15.85/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.85/2.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 15.85/2.50      | ~ v1_relat_1(X1)
% 15.85/2.50      | ~ v1_funct_1(X1) ),
% 15.85/2.50      inference(cnf_transformation,[],[f47]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_897,plain,
% 15.85/2.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 15.85/2.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 15.85/2.50      | v1_relat_1(X1) != iProver_top
% 15.85/2.50      | v1_funct_1(X1) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_49822,plain,
% 15.85/2.50      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
% 15.85/2.50      | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top
% 15.85/2.50      | v1_relat_1(sK4) != iProver_top
% 15.85/2.50      | v1_funct_1(sK4) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_49816,c_897]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_25,negated_conjecture,
% 15.85/2.50      ( v1_funct_1(sK4) ),
% 15.85/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_26,plain,
% 15.85/2.50      ( v1_funct_1(sK4) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_10,plain,
% 15.85/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.85/2.50      | v1_relat_1(X0) ),
% 15.85/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1117,plain,
% 15.85/2.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 15.85/2.50      | v1_relat_1(sK4) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_10]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1118,plain,
% 15.85/2.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 15.85/2.50      | v1_relat_1(sK4) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_50051,plain,
% 15.85/2.50      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
% 15.85/2.50      | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),k1_relat_1(sK4)) != iProver_top ),
% 15.85/2.50      inference(global_propositional_subsumption,
% 15.85/2.50                [status(thm)],
% 15.85/2.50                [c_49822,c_26,c_28,c_1118]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_50058,plain,
% 15.85/2.50      ( sK3 = k1_xboole_0
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
% 15.85/2.50      | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_3687,c_50051]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_5,plain,
% 15.85/2.50      ( r1_tarski(k1_xboole_0,X0) ),
% 15.85/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_900,plain,
% 15.85/2.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1882,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 15.85/2.50      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 15.85/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_901,c_903]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_9,plain,
% 15.85/2.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 15.85/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_896,plain,
% 15.85/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.85/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_8505,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r2_hidden(sK1(X1,X0),X1) = iProver_top
% 15.85/2.50      | r1_tarski(X0,X2) != iProver_top
% 15.85/2.50      | r1_tarski(X2,sK1(X1,X0)) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_1882,c_896]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_12526,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top
% 15.85/2.50      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_900,c_8505]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_12585,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r2_hidden(sK1(X1,X0),X2) = iProver_top
% 15.85/2.50      | r1_tarski(X1,X2) != iProver_top
% 15.85/2.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_12526,c_903]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_3,plain,
% 15.85/2.50      ( ~ r2_hidden(sK1(X0,X1),X1)
% 15.85/2.50      | ~ r2_hidden(sK1(X0,X1),X0)
% 15.85/2.50      | X1 = X0 ),
% 15.85/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_902,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r2_hidden(sK1(X1,X0),X0) != iProver_top
% 15.85/2.50      | r2_hidden(sK1(X1,X0),X1) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_13065,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r2_hidden(sK1(X0,X1),X0) != iProver_top
% 15.85/2.50      | r1_tarski(X0,X1) != iProver_top
% 15.85/2.50      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_12585,c_902]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_13363,plain,
% 15.85/2.50      ( X0 = X1
% 15.85/2.50      | r1_tarski(X0,X1) != iProver_top
% 15.85/2.50      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 15.85/2.50      inference(global_propositional_subsumption,
% 15.85/2.50                [status(thm)],
% 15.85/2.50                [c_13065,c_12526]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_13375,plain,
% 15.85/2.50      ( k2_relat_1(sK4) = sK3
% 15.85/2.50      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 15.85/2.50      inference(superposition,[status(thm)],[c_3990,c_13363]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_22,negated_conjecture,
% 15.85/2.50      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 15.85/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_10744,plain,
% 15.85/2.50      ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 15.85/2.50      | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_22]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_10745,plain,
% 15.85/2.50      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) != iProver_top
% 15.85/2.50      | r2_hidden(sK5(sK1(k2_relat_1(sK4),sK3)),sK2) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_10744]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_295,plain,
% 15.85/2.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 15.85/2.50      theory(equality) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_9806,plain,
% 15.85/2.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X1) | sK3 != X0 ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_295]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_9807,plain,
% 15.85/2.50      ( sK3 != X0
% 15.85/2.50      | r1_tarski(X0,X1) != iProver_top
% 15.85/2.50      | r1_tarski(sK3,X1) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_9806]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_9809,plain,
% 15.85/2.50      ( sK3 != k1_xboole_0
% 15.85/2.50      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 15.85/2.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_9807]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_2487,plain,
% 15.85/2.50      ( ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 15.85/2.50      | ~ r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 15.85/2.50      | sK3 = k2_relat_1(sK4) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_2488,plain,
% 15.85/2.50      ( sK3 = k2_relat_1(sK4)
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) != iProver_top
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) != iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_2487]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1259,plain,
% 15.85/2.50      ( r2_hidden(sK1(X0,sK3),X0)
% 15.85/2.50      | r2_hidden(sK1(X0,sK3),sK3)
% 15.85/2.50      | sK3 = X0 ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1984,plain,
% 15.85/2.50      ( r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3)
% 15.85/2.50      | sK3 = k2_relat_1(sK4) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_1259]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1985,plain,
% 15.85/2.50      ( sK3 = k2_relat_1(sK4)
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),k2_relat_1(sK4)) = iProver_top
% 15.85/2.50      | r2_hidden(sK1(k2_relat_1(sK4),sK3),sK3) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_294,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1140,plain,
% 15.85/2.50      ( k2_relset_1(sK2,sK3,sK4) != X0
% 15.85/2.50      | k2_relset_1(sK2,sK3,sK4) = sK3
% 15.85/2.50      | sK3 != X0 ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_294]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1545,plain,
% 15.85/2.50      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 15.85/2.50      | k2_relset_1(sK2,sK3,sK4) = sK3
% 15.85/2.50      | sK3 != k2_relat_1(sK4) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_1140]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_1159,plain,
% 15.85/2.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 15.85/2.50      | k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_13]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_77,plain,
% 15.85/2.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.85/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(c_79,plain,
% 15.85/2.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.85/2.50      inference(instantiation,[status(thm)],[c_77]) ).
% 15.85/2.50  
% 15.85/2.50  cnf(contradiction,plain,
% 15.85/2.50      ( $false ),
% 15.85/2.50      inference(minisat,
% 15.85/2.50                [status(thm)],
% 15.85/2.50                [c_51352,c_50058,c_13375,c_10745,c_9809,c_3990,c_2621,
% 15.85/2.50                 c_2488,c_1985,c_1545,c_1159,c_79,c_20,c_23]) ).
% 15.85/2.50  
% 15.85/2.50  
% 15.85/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.85/2.50  
% 15.85/2.50  ------                               Statistics
% 15.85/2.50  
% 15.85/2.50  ------ Selected
% 15.85/2.50  
% 15.85/2.50  total_time:                             1.967
% 15.85/2.50  
%------------------------------------------------------------------------------
