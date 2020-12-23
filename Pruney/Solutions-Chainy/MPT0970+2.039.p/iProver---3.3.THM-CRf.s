%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:53 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  135 (1771 expanded)
%              Number of clauses        :   82 ( 643 expanded)
%              Number of leaves         :   16 ( 404 expanded)
%              Depth                    :   29
%              Number of atoms          :  411 (7792 expanded)
%              Number of equality atoms :  158 (2167 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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

fof(f35,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f34,f33])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_891,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_304,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_305,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_391,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_305])).

cnf(c_392,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_531,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1042,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_1044,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_1117,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_1042,c_1044])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_361,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_305])).

cnf(c_362,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_362])).

cnf(c_875,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_525,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_362])).

cnf(c_562,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_563,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_305])).

cnf(c_377,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(sK1(X0,X1,sK4),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_521,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_377])).

cnf(c_1043,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_1046,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1043])).

cnf(c_1763,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_875,c_562,c_563,c_1042,c_1046])).

cnf(c_1764,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1763])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_281,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_883,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1124,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_883])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_889,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1504,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_889])).

cnf(c_1922,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_1504])).

cnf(c_3332,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_1922])).

cnf(c_3515,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4),X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_891,c_3332])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_886,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK5(X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3514,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_891,c_3332])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_887,plain,
    ( k1_funct_1(sK4,sK5(X0)) = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3844,plain,
    ( k1_funct_1(sK4,sK5(sK0(X0,k2_relat_1(sK4)))) = sK0(X0,k2_relat_1(sK4))
    | k2_relat_1(sK4) = X0
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3514,c_887])).

cnf(c_4030,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4))
    | k2_relat_1(sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_3844,c_887])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_295,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_296,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_1055,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_296])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1076,plain,
    ( k2_relat_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1055,c_16])).

cnf(c_4062,plain,
    ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4030,c_1076])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_256,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_260,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(X0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_21,c_19])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_884,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_1351,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_884,c_1055])).

cnf(c_4065,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4062,c_1351])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1333,plain,
    ( ~ r2_hidden(sK0(X0,k2_relat_1(sK4)),X0)
    | ~ r2_hidden(sK0(X0,k2_relat_1(sK4)),k2_relat_1(sK4))
    | k2_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1339,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) != iProver_top
    | r2_hidden(sK0(X0,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_1341,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_3593,plain,
    ( k2_relat_1(sK4) = sK3
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3514])).

cnf(c_4471,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4065,c_1076,c_1341,c_3593])).

cnf(c_4477,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_886,c_4471])).

cnf(c_4524,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4477,c_1076,c_3593])).

cnf(c_5069,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4),X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3515,c_4524])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_885,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_5073,plain,
    ( k2_relat_1(sK4) = X0
    | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5069,c_885])).

cnf(c_5076,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5073,c_885])).

cnf(c_4551,plain,
    ( k2_relat_1(sK4) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4524,c_1076])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5076,c_4551])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.20/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.06  
% 3.20/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/1.06  
% 3.20/1.06  ------  iProver source info
% 3.20/1.06  
% 3.20/1.06  git: date: 2020-06-30 10:37:57 +0100
% 3.20/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/1.06  git: non_committed_changes: false
% 3.20/1.06  git: last_make_outside_of_git: false
% 3.20/1.06  
% 3.20/1.06  ------ 
% 3.20/1.06  
% 3.20/1.06  ------ Input Options
% 3.20/1.06  
% 3.20/1.06  --out_options                           all
% 3.20/1.06  --tptp_safe_out                         true
% 3.20/1.06  --problem_path                          ""
% 3.20/1.06  --include_path                          ""
% 3.20/1.06  --clausifier                            res/vclausify_rel
% 3.20/1.06  --clausifier_options                    --mode clausify
% 3.20/1.06  --stdin                                 false
% 3.20/1.06  --stats_out                             all
% 3.20/1.06  
% 3.20/1.06  ------ General Options
% 3.20/1.06  
% 3.20/1.06  --fof                                   false
% 3.20/1.06  --time_out_real                         305.
% 3.20/1.06  --time_out_virtual                      -1.
% 3.20/1.06  --symbol_type_check                     false
% 3.20/1.06  --clausify_out                          false
% 3.20/1.06  --sig_cnt_out                           false
% 3.20/1.06  --trig_cnt_out                          false
% 3.20/1.06  --trig_cnt_out_tolerance                1.
% 3.20/1.06  --trig_cnt_out_sk_spl                   false
% 3.20/1.06  --abstr_cl_out                          false
% 3.20/1.06  
% 3.20/1.06  ------ Global Options
% 3.20/1.06  
% 3.20/1.06  --schedule                              default
% 3.20/1.06  --add_important_lit                     false
% 3.20/1.06  --prop_solver_per_cl                    1000
% 3.20/1.06  --min_unsat_core                        false
% 3.20/1.06  --soft_assumptions                      false
% 3.20/1.06  --soft_lemma_size                       3
% 3.20/1.06  --prop_impl_unit_size                   0
% 3.20/1.06  --prop_impl_unit                        []
% 3.20/1.06  --share_sel_clauses                     true
% 3.20/1.06  --reset_solvers                         false
% 3.20/1.06  --bc_imp_inh                            [conj_cone]
% 3.20/1.06  --conj_cone_tolerance                   3.
% 3.20/1.06  --extra_neg_conj                        none
% 3.20/1.06  --large_theory_mode                     true
% 3.20/1.06  --prolific_symb_bound                   200
% 3.20/1.06  --lt_threshold                          2000
% 3.20/1.06  --clause_weak_htbl                      true
% 3.20/1.06  --gc_record_bc_elim                     false
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing Options
% 3.20/1.06  
% 3.20/1.06  --preprocessing_flag                    true
% 3.20/1.06  --time_out_prep_mult                    0.1
% 3.20/1.06  --splitting_mode                        input
% 3.20/1.06  --splitting_grd                         true
% 3.20/1.06  --splitting_cvd                         false
% 3.20/1.06  --splitting_cvd_svl                     false
% 3.20/1.06  --splitting_nvd                         32
% 3.20/1.06  --sub_typing                            true
% 3.20/1.06  --prep_gs_sim                           true
% 3.20/1.06  --prep_unflatten                        true
% 3.20/1.06  --prep_res_sim                          true
% 3.20/1.06  --prep_upred                            true
% 3.20/1.06  --prep_sem_filter                       exhaustive
% 3.20/1.06  --prep_sem_filter_out                   false
% 3.20/1.06  --pred_elim                             true
% 3.20/1.06  --res_sim_input                         true
% 3.20/1.06  --eq_ax_congr_red                       true
% 3.20/1.06  --pure_diseq_elim                       true
% 3.20/1.06  --brand_transform                       false
% 3.20/1.06  --non_eq_to_eq                          false
% 3.20/1.06  --prep_def_merge                        true
% 3.20/1.06  --prep_def_merge_prop_impl              false
% 3.20/1.06  --prep_def_merge_mbd                    true
% 3.20/1.06  --prep_def_merge_tr_red                 false
% 3.20/1.06  --prep_def_merge_tr_cl                  false
% 3.20/1.06  --smt_preprocessing                     true
% 3.20/1.06  --smt_ac_axioms                         fast
% 3.20/1.06  --preprocessed_out                      false
% 3.20/1.06  --preprocessed_stats                    false
% 3.20/1.06  
% 3.20/1.06  ------ Abstraction refinement Options
% 3.20/1.06  
% 3.20/1.06  --abstr_ref                             []
% 3.20/1.06  --abstr_ref_prep                        false
% 3.20/1.06  --abstr_ref_until_sat                   false
% 3.20/1.06  --abstr_ref_sig_restrict                funpre
% 3.20/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.06  --abstr_ref_under                       []
% 3.20/1.06  
% 3.20/1.06  ------ SAT Options
% 3.20/1.06  
% 3.20/1.06  --sat_mode                              false
% 3.20/1.06  --sat_fm_restart_options                ""
% 3.20/1.06  --sat_gr_def                            false
% 3.20/1.06  --sat_epr_types                         true
% 3.20/1.06  --sat_non_cyclic_types                  false
% 3.20/1.06  --sat_finite_models                     false
% 3.20/1.06  --sat_fm_lemmas                         false
% 3.20/1.06  --sat_fm_prep                           false
% 3.20/1.06  --sat_fm_uc_incr                        true
% 3.20/1.06  --sat_out_model                         small
% 3.20/1.06  --sat_out_clauses                       false
% 3.20/1.06  
% 3.20/1.06  ------ QBF Options
% 3.20/1.06  
% 3.20/1.06  --qbf_mode                              false
% 3.20/1.06  --qbf_elim_univ                         false
% 3.20/1.06  --qbf_dom_inst                          none
% 3.20/1.06  --qbf_dom_pre_inst                      false
% 3.20/1.06  --qbf_sk_in                             false
% 3.20/1.06  --qbf_pred_elim                         true
% 3.20/1.06  --qbf_split                             512
% 3.20/1.06  
% 3.20/1.06  ------ BMC1 Options
% 3.20/1.06  
% 3.20/1.06  --bmc1_incremental                      false
% 3.20/1.06  --bmc1_axioms                           reachable_all
% 3.20/1.06  --bmc1_min_bound                        0
% 3.20/1.06  --bmc1_max_bound                        -1
% 3.20/1.06  --bmc1_max_bound_default                -1
% 3.20/1.06  --bmc1_symbol_reachability              true
% 3.20/1.06  --bmc1_property_lemmas                  false
% 3.20/1.06  --bmc1_k_induction                      false
% 3.20/1.06  --bmc1_non_equiv_states                 false
% 3.20/1.06  --bmc1_deadlock                         false
% 3.20/1.06  --bmc1_ucm                              false
% 3.20/1.06  --bmc1_add_unsat_core                   none
% 3.20/1.06  --bmc1_unsat_core_children              false
% 3.20/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.06  --bmc1_out_stat                         full
% 3.20/1.06  --bmc1_ground_init                      false
% 3.20/1.06  --bmc1_pre_inst_next_state              false
% 3.20/1.06  --bmc1_pre_inst_state                   false
% 3.20/1.06  --bmc1_pre_inst_reach_state             false
% 3.20/1.06  --bmc1_out_unsat_core                   false
% 3.20/1.06  --bmc1_aig_witness_out                  false
% 3.20/1.06  --bmc1_verbose                          false
% 3.20/1.06  --bmc1_dump_clauses_tptp                false
% 3.20/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.06  --bmc1_dump_file                        -
% 3.20/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.06  --bmc1_ucm_extend_mode                  1
% 3.20/1.06  --bmc1_ucm_init_mode                    2
% 3.20/1.06  --bmc1_ucm_cone_mode                    none
% 3.20/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.06  --bmc1_ucm_relax_model                  4
% 3.20/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.06  --bmc1_ucm_layered_model                none
% 3.20/1.06  --bmc1_ucm_max_lemma_size               10
% 3.20/1.06  
% 3.20/1.06  ------ AIG Options
% 3.20/1.06  
% 3.20/1.06  --aig_mode                              false
% 3.20/1.06  
% 3.20/1.06  ------ Instantiation Options
% 3.20/1.06  
% 3.20/1.06  --instantiation_flag                    true
% 3.20/1.06  --inst_sos_flag                         false
% 3.20/1.06  --inst_sos_phase                        true
% 3.20/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel_side                     num_symb
% 3.20/1.06  --inst_solver_per_active                1400
% 3.20/1.06  --inst_solver_calls_frac                1.
% 3.20/1.06  --inst_passive_queue_type               priority_queues
% 3.20/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.06  --inst_passive_queues_freq              [25;2]
% 3.20/1.06  --inst_dismatching                      true
% 3.20/1.06  --inst_eager_unprocessed_to_passive     true
% 3.20/1.06  --inst_prop_sim_given                   true
% 3.20/1.06  --inst_prop_sim_new                     false
% 3.20/1.06  --inst_subs_new                         false
% 3.20/1.06  --inst_eq_res_simp                      false
% 3.20/1.06  --inst_subs_given                       false
% 3.20/1.06  --inst_orphan_elimination               true
% 3.20/1.06  --inst_learning_loop_flag               true
% 3.20/1.06  --inst_learning_start                   3000
% 3.20/1.06  --inst_learning_factor                  2
% 3.20/1.06  --inst_start_prop_sim_after_learn       3
% 3.20/1.06  --inst_sel_renew                        solver
% 3.20/1.06  --inst_lit_activity_flag                true
% 3.20/1.06  --inst_restr_to_given                   false
% 3.20/1.06  --inst_activity_threshold               500
% 3.20/1.06  --inst_out_proof                        true
% 3.20/1.06  
% 3.20/1.06  ------ Resolution Options
% 3.20/1.06  
% 3.20/1.06  --resolution_flag                       true
% 3.20/1.06  --res_lit_sel                           adaptive
% 3.20/1.06  --res_lit_sel_side                      none
% 3.20/1.06  --res_ordering                          kbo
% 3.20/1.06  --res_to_prop_solver                    active
% 3.20/1.06  --res_prop_simpl_new                    false
% 3.20/1.06  --res_prop_simpl_given                  true
% 3.20/1.06  --res_passive_queue_type                priority_queues
% 3.20/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.06  --res_passive_queues_freq               [15;5]
% 3.20/1.06  --res_forward_subs                      full
% 3.20/1.06  --res_backward_subs                     full
% 3.20/1.06  --res_forward_subs_resolution           true
% 3.20/1.06  --res_backward_subs_resolution          true
% 3.20/1.06  --res_orphan_elimination                true
% 3.20/1.06  --res_time_limit                        2.
% 3.20/1.06  --res_out_proof                         true
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Options
% 3.20/1.06  
% 3.20/1.06  --superposition_flag                    true
% 3.20/1.06  --sup_passive_queue_type                priority_queues
% 3.20/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.06  --demod_completeness_check              fast
% 3.20/1.06  --demod_use_ground                      true
% 3.20/1.06  --sup_to_prop_solver                    passive
% 3.20/1.06  --sup_prop_simpl_new                    true
% 3.20/1.06  --sup_prop_simpl_given                  true
% 3.20/1.06  --sup_fun_splitting                     false
% 3.20/1.06  --sup_smt_interval                      50000
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Simplification Setup
% 3.20/1.06  
% 3.20/1.06  --sup_indices_passive                   []
% 3.20/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_full_bw                           [BwDemod]
% 3.20/1.06  --sup_immed_triv                        [TrivRules]
% 3.20/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_immed_bw_main                     []
% 3.20/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  
% 3.20/1.06  ------ Combination Options
% 3.20/1.06  
% 3.20/1.06  --comb_res_mult                         3
% 3.20/1.06  --comb_sup_mult                         2
% 3.20/1.06  --comb_inst_mult                        10
% 3.20/1.06  
% 3.20/1.06  ------ Debug Options
% 3.20/1.06  
% 3.20/1.06  --dbg_backtrace                         false
% 3.20/1.06  --dbg_dump_prop_clauses                 false
% 3.20/1.06  --dbg_dump_prop_clauses_file            -
% 3.20/1.06  --dbg_out_stat                          false
% 3.20/1.06  ------ Parsing...
% 3.20/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/1.06  ------ Proving...
% 3.20/1.06  ------ Problem Properties 
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  clauses                                 25
% 3.20/1.06  conjectures                             3
% 3.20/1.06  EPR                                     5
% 3.20/1.06  Horn                                    19
% 3.20/1.06  unary                                   2
% 3.20/1.06  binary                                  14
% 3.20/1.06  lits                                    59
% 3.20/1.06  lits eq                                 14
% 3.20/1.06  fd_pure                                 0
% 3.20/1.06  fd_pseudo                               0
% 3.20/1.06  fd_cond                                 0
% 3.20/1.06  fd_pseudo_cond                          2
% 3.20/1.06  AC symbols                              0
% 3.20/1.06  
% 3.20/1.06  ------ Schedule dynamic 5 is on 
% 3.20/1.06  
% 3.20/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  ------ 
% 3.20/1.06  Current options:
% 3.20/1.06  ------ 
% 3.20/1.06  
% 3.20/1.06  ------ Input Options
% 3.20/1.06  
% 3.20/1.06  --out_options                           all
% 3.20/1.06  --tptp_safe_out                         true
% 3.20/1.06  --problem_path                          ""
% 3.20/1.06  --include_path                          ""
% 3.20/1.06  --clausifier                            res/vclausify_rel
% 3.20/1.06  --clausifier_options                    --mode clausify
% 3.20/1.06  --stdin                                 false
% 3.20/1.06  --stats_out                             all
% 3.20/1.06  
% 3.20/1.06  ------ General Options
% 3.20/1.06  
% 3.20/1.06  --fof                                   false
% 3.20/1.06  --time_out_real                         305.
% 3.20/1.06  --time_out_virtual                      -1.
% 3.20/1.06  --symbol_type_check                     false
% 3.20/1.06  --clausify_out                          false
% 3.20/1.06  --sig_cnt_out                           false
% 3.20/1.06  --trig_cnt_out                          false
% 3.20/1.06  --trig_cnt_out_tolerance                1.
% 3.20/1.06  --trig_cnt_out_sk_spl                   false
% 3.20/1.06  --abstr_cl_out                          false
% 3.20/1.06  
% 3.20/1.06  ------ Global Options
% 3.20/1.06  
% 3.20/1.06  --schedule                              default
% 3.20/1.06  --add_important_lit                     false
% 3.20/1.06  --prop_solver_per_cl                    1000
% 3.20/1.06  --min_unsat_core                        false
% 3.20/1.06  --soft_assumptions                      false
% 3.20/1.06  --soft_lemma_size                       3
% 3.20/1.06  --prop_impl_unit_size                   0
% 3.20/1.06  --prop_impl_unit                        []
% 3.20/1.06  --share_sel_clauses                     true
% 3.20/1.06  --reset_solvers                         false
% 3.20/1.06  --bc_imp_inh                            [conj_cone]
% 3.20/1.06  --conj_cone_tolerance                   3.
% 3.20/1.06  --extra_neg_conj                        none
% 3.20/1.06  --large_theory_mode                     true
% 3.20/1.06  --prolific_symb_bound                   200
% 3.20/1.06  --lt_threshold                          2000
% 3.20/1.06  --clause_weak_htbl                      true
% 3.20/1.06  --gc_record_bc_elim                     false
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing Options
% 3.20/1.06  
% 3.20/1.06  --preprocessing_flag                    true
% 3.20/1.06  --time_out_prep_mult                    0.1
% 3.20/1.06  --splitting_mode                        input
% 3.20/1.06  --splitting_grd                         true
% 3.20/1.06  --splitting_cvd                         false
% 3.20/1.06  --splitting_cvd_svl                     false
% 3.20/1.06  --splitting_nvd                         32
% 3.20/1.06  --sub_typing                            true
% 3.20/1.06  --prep_gs_sim                           true
% 3.20/1.06  --prep_unflatten                        true
% 3.20/1.06  --prep_res_sim                          true
% 3.20/1.06  --prep_upred                            true
% 3.20/1.06  --prep_sem_filter                       exhaustive
% 3.20/1.06  --prep_sem_filter_out                   false
% 3.20/1.06  --pred_elim                             true
% 3.20/1.06  --res_sim_input                         true
% 3.20/1.06  --eq_ax_congr_red                       true
% 3.20/1.06  --pure_diseq_elim                       true
% 3.20/1.06  --brand_transform                       false
% 3.20/1.06  --non_eq_to_eq                          false
% 3.20/1.06  --prep_def_merge                        true
% 3.20/1.06  --prep_def_merge_prop_impl              false
% 3.20/1.06  --prep_def_merge_mbd                    true
% 3.20/1.06  --prep_def_merge_tr_red                 false
% 3.20/1.06  --prep_def_merge_tr_cl                  false
% 3.20/1.06  --smt_preprocessing                     true
% 3.20/1.06  --smt_ac_axioms                         fast
% 3.20/1.06  --preprocessed_out                      false
% 3.20/1.06  --preprocessed_stats                    false
% 3.20/1.06  
% 3.20/1.06  ------ Abstraction refinement Options
% 3.20/1.06  
% 3.20/1.06  --abstr_ref                             []
% 3.20/1.06  --abstr_ref_prep                        false
% 3.20/1.06  --abstr_ref_until_sat                   false
% 3.20/1.06  --abstr_ref_sig_restrict                funpre
% 3.20/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.06  --abstr_ref_under                       []
% 3.20/1.06  
% 3.20/1.06  ------ SAT Options
% 3.20/1.06  
% 3.20/1.06  --sat_mode                              false
% 3.20/1.06  --sat_fm_restart_options                ""
% 3.20/1.06  --sat_gr_def                            false
% 3.20/1.06  --sat_epr_types                         true
% 3.20/1.06  --sat_non_cyclic_types                  false
% 3.20/1.06  --sat_finite_models                     false
% 3.20/1.06  --sat_fm_lemmas                         false
% 3.20/1.06  --sat_fm_prep                           false
% 3.20/1.06  --sat_fm_uc_incr                        true
% 3.20/1.06  --sat_out_model                         small
% 3.20/1.06  --sat_out_clauses                       false
% 3.20/1.06  
% 3.20/1.06  ------ QBF Options
% 3.20/1.06  
% 3.20/1.06  --qbf_mode                              false
% 3.20/1.06  --qbf_elim_univ                         false
% 3.20/1.06  --qbf_dom_inst                          none
% 3.20/1.06  --qbf_dom_pre_inst                      false
% 3.20/1.06  --qbf_sk_in                             false
% 3.20/1.06  --qbf_pred_elim                         true
% 3.20/1.06  --qbf_split                             512
% 3.20/1.06  
% 3.20/1.06  ------ BMC1 Options
% 3.20/1.06  
% 3.20/1.06  --bmc1_incremental                      false
% 3.20/1.06  --bmc1_axioms                           reachable_all
% 3.20/1.06  --bmc1_min_bound                        0
% 3.20/1.06  --bmc1_max_bound                        -1
% 3.20/1.06  --bmc1_max_bound_default                -1
% 3.20/1.06  --bmc1_symbol_reachability              true
% 3.20/1.06  --bmc1_property_lemmas                  false
% 3.20/1.06  --bmc1_k_induction                      false
% 3.20/1.06  --bmc1_non_equiv_states                 false
% 3.20/1.06  --bmc1_deadlock                         false
% 3.20/1.06  --bmc1_ucm                              false
% 3.20/1.06  --bmc1_add_unsat_core                   none
% 3.20/1.06  --bmc1_unsat_core_children              false
% 3.20/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.06  --bmc1_out_stat                         full
% 3.20/1.06  --bmc1_ground_init                      false
% 3.20/1.06  --bmc1_pre_inst_next_state              false
% 3.20/1.06  --bmc1_pre_inst_state                   false
% 3.20/1.06  --bmc1_pre_inst_reach_state             false
% 3.20/1.06  --bmc1_out_unsat_core                   false
% 3.20/1.06  --bmc1_aig_witness_out                  false
% 3.20/1.06  --bmc1_verbose                          false
% 3.20/1.06  --bmc1_dump_clauses_tptp                false
% 3.20/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.06  --bmc1_dump_file                        -
% 3.20/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.06  --bmc1_ucm_extend_mode                  1
% 3.20/1.06  --bmc1_ucm_init_mode                    2
% 3.20/1.06  --bmc1_ucm_cone_mode                    none
% 3.20/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.06  --bmc1_ucm_relax_model                  4
% 3.20/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.06  --bmc1_ucm_layered_model                none
% 3.20/1.06  --bmc1_ucm_max_lemma_size               10
% 3.20/1.06  
% 3.20/1.06  ------ AIG Options
% 3.20/1.06  
% 3.20/1.06  --aig_mode                              false
% 3.20/1.06  
% 3.20/1.06  ------ Instantiation Options
% 3.20/1.06  
% 3.20/1.06  --instantiation_flag                    true
% 3.20/1.06  --inst_sos_flag                         false
% 3.20/1.06  --inst_sos_phase                        true
% 3.20/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel_side                     none
% 3.20/1.06  --inst_solver_per_active                1400
% 3.20/1.06  --inst_solver_calls_frac                1.
% 3.20/1.06  --inst_passive_queue_type               priority_queues
% 3.20/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.06  --inst_passive_queues_freq              [25;2]
% 3.20/1.06  --inst_dismatching                      true
% 3.20/1.06  --inst_eager_unprocessed_to_passive     true
% 3.20/1.06  --inst_prop_sim_given                   true
% 3.20/1.06  --inst_prop_sim_new                     false
% 3.20/1.06  --inst_subs_new                         false
% 3.20/1.06  --inst_eq_res_simp                      false
% 3.20/1.06  --inst_subs_given                       false
% 3.20/1.06  --inst_orphan_elimination               true
% 3.20/1.06  --inst_learning_loop_flag               true
% 3.20/1.06  --inst_learning_start                   3000
% 3.20/1.06  --inst_learning_factor                  2
% 3.20/1.06  --inst_start_prop_sim_after_learn       3
% 3.20/1.06  --inst_sel_renew                        solver
% 3.20/1.06  --inst_lit_activity_flag                true
% 3.20/1.06  --inst_restr_to_given                   false
% 3.20/1.06  --inst_activity_threshold               500
% 3.20/1.06  --inst_out_proof                        true
% 3.20/1.06  
% 3.20/1.06  ------ Resolution Options
% 3.20/1.06  
% 3.20/1.06  --resolution_flag                       false
% 3.20/1.06  --res_lit_sel                           adaptive
% 3.20/1.06  --res_lit_sel_side                      none
% 3.20/1.06  --res_ordering                          kbo
% 3.20/1.06  --res_to_prop_solver                    active
% 3.20/1.06  --res_prop_simpl_new                    false
% 3.20/1.06  --res_prop_simpl_given                  true
% 3.20/1.06  --res_passive_queue_type                priority_queues
% 3.20/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.06  --res_passive_queues_freq               [15;5]
% 3.20/1.06  --res_forward_subs                      full
% 3.20/1.06  --res_backward_subs                     full
% 3.20/1.06  --res_forward_subs_resolution           true
% 3.20/1.06  --res_backward_subs_resolution          true
% 3.20/1.06  --res_orphan_elimination                true
% 3.20/1.06  --res_time_limit                        2.
% 3.20/1.06  --res_out_proof                         true
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Options
% 3.20/1.06  
% 3.20/1.06  --superposition_flag                    true
% 3.20/1.06  --sup_passive_queue_type                priority_queues
% 3.20/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.06  --demod_completeness_check              fast
% 3.20/1.06  --demod_use_ground                      true
% 3.20/1.06  --sup_to_prop_solver                    passive
% 3.20/1.06  --sup_prop_simpl_new                    true
% 3.20/1.06  --sup_prop_simpl_given                  true
% 3.20/1.06  --sup_fun_splitting                     false
% 3.20/1.06  --sup_smt_interval                      50000
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Simplification Setup
% 3.20/1.06  
% 3.20/1.06  --sup_indices_passive                   []
% 3.20/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_full_bw                           [BwDemod]
% 3.20/1.06  --sup_immed_triv                        [TrivRules]
% 3.20/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_immed_bw_main                     []
% 3.20/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  
% 3.20/1.06  ------ Combination Options
% 3.20/1.06  
% 3.20/1.06  --comb_res_mult                         3
% 3.20/1.06  --comb_sup_mult                         2
% 3.20/1.06  --comb_inst_mult                        10
% 3.20/1.06  
% 3.20/1.06  ------ Debug Options
% 3.20/1.06  
% 3.20/1.06  --dbg_backtrace                         false
% 3.20/1.06  --dbg_dump_prop_clauses                 false
% 3.20/1.06  --dbg_dump_prop_clauses_file            -
% 3.20/1.06  --dbg_out_stat                          false
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  ------ Proving...
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  % SZS status Theorem for theBenchmark.p
% 3.20/1.06  
% 3.20/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/1.06  
% 3.20/1.06  fof(f1,axiom,(
% 3.20/1.06    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f13,plain,(
% 3.20/1.06    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.20/1.06    inference(ennf_transformation,[],[f1])).
% 3.20/1.06  
% 3.20/1.06  fof(f24,plain,(
% 3.20/1.06    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.20/1.06    inference(nnf_transformation,[],[f13])).
% 3.20/1.06  
% 3.20/1.06  fof(f25,plain,(
% 3.20/1.06    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.20/1.06    introduced(choice_axiom,[])).
% 3.20/1.06  
% 3.20/1.06  fof(f26,plain,(
% 3.20/1.06    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.20/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.20/1.06  
% 3.20/1.06  fof(f36,plain,(
% 3.20/1.06    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f26])).
% 3.20/1.06  
% 3.20/1.06  fof(f6,axiom,(
% 3.20/1.06    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f16,plain,(
% 3.20/1.06    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.20/1.06    inference(ennf_transformation,[],[f6])).
% 3.20/1.06  
% 3.20/1.06  fof(f47,plain,(
% 3.20/1.06    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f16])).
% 3.20/1.06  
% 3.20/1.06  fof(f8,axiom,(
% 3.20/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f18,plain,(
% 3.20/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/1.06    inference(ennf_transformation,[],[f8])).
% 3.20/1.06  
% 3.20/1.06  fof(f49,plain,(
% 3.20/1.06    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/1.06    inference(cnf_transformation,[],[f18])).
% 3.20/1.06  
% 3.20/1.06  fof(f11,conjecture,(
% 3.20/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f12,negated_conjecture,(
% 3.20/1.06    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.20/1.06    inference(negated_conjecture,[],[f11])).
% 3.20/1.06  
% 3.20/1.06  fof(f22,plain,(
% 3.20/1.06    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.20/1.06    inference(ennf_transformation,[],[f12])).
% 3.20/1.06  
% 3.20/1.06  fof(f23,plain,(
% 3.20/1.06    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.20/1.06    inference(flattening,[],[f22])).
% 3.20/1.06  
% 3.20/1.06  fof(f34,plain,(
% 3.20/1.06    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 3.20/1.06    introduced(choice_axiom,[])).
% 3.20/1.06  
% 3.20/1.06  fof(f33,plain,(
% 3.20/1.06    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.20/1.06    introduced(choice_axiom,[])).
% 3.20/1.06  
% 3.20/1.06  fof(f35,plain,(
% 3.20/1.06    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.20/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f34,f33])).
% 3.20/1.06  
% 3.20/1.06  fof(f54,plain,(
% 3.20/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f5,axiom,(
% 3.20/1.06    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f15,plain,(
% 3.20/1.06    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.20/1.06    inference(ennf_transformation,[],[f5])).
% 3.20/1.06  
% 3.20/1.06  fof(f29,plain,(
% 3.20/1.06    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.20/1.06    inference(nnf_transformation,[],[f15])).
% 3.20/1.06  
% 3.20/1.06  fof(f30,plain,(
% 3.20/1.06    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.20/1.06    inference(rectify,[],[f29])).
% 3.20/1.06  
% 3.20/1.06  fof(f31,plain,(
% 3.20/1.06    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.20/1.06    introduced(choice_axiom,[])).
% 3.20/1.06  
% 3.20/1.06  fof(f32,plain,(
% 3.20/1.06    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.20/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.20/1.06  
% 3.20/1.06  fof(f44,plain,(
% 3.20/1.06    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f32])).
% 3.20/1.06  
% 3.20/1.06  fof(f45,plain,(
% 3.20/1.06    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f32])).
% 3.20/1.06  
% 3.20/1.06  fof(f4,axiom,(
% 3.20/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f14,plain,(
% 3.20/1.06    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.06    inference(ennf_transformation,[],[f4])).
% 3.20/1.06  
% 3.20/1.06  fof(f42,plain,(
% 3.20/1.06    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/1.06    inference(cnf_transformation,[],[f14])).
% 3.20/1.06  
% 3.20/1.06  fof(f3,axiom,(
% 3.20/1.06    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f27,plain,(
% 3.20/1.06    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.20/1.06    inference(nnf_transformation,[],[f3])).
% 3.20/1.06  
% 3.20/1.06  fof(f28,plain,(
% 3.20/1.06    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.20/1.06    inference(flattening,[],[f27])).
% 3.20/1.06  
% 3.20/1.06  fof(f40,plain,(
% 3.20/1.06    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.20/1.06    inference(cnf_transformation,[],[f28])).
% 3.20/1.06  
% 3.20/1.06  fof(f55,plain,(
% 3.20/1.06    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f56,plain,(
% 3.20/1.06    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f9,axiom,(
% 3.20/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f19,plain,(
% 3.20/1.06    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/1.06    inference(ennf_transformation,[],[f9])).
% 3.20/1.06  
% 3.20/1.06  fof(f50,plain,(
% 3.20/1.06    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/1.06    inference(cnf_transformation,[],[f19])).
% 3.20/1.06  
% 3.20/1.06  fof(f57,plain,(
% 3.20/1.06    k2_relset_1(sK2,sK3,sK4) != sK3),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f10,axiom,(
% 3.20/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f20,plain,(
% 3.20/1.06    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.20/1.06    inference(ennf_transformation,[],[f10])).
% 3.20/1.06  
% 3.20/1.06  fof(f21,plain,(
% 3.20/1.06    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.20/1.06    inference(flattening,[],[f20])).
% 3.20/1.06  
% 3.20/1.06  fof(f51,plain,(
% 3.20/1.06    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f21])).
% 3.20/1.06  
% 3.20/1.06  fof(f53,plain,(
% 3.20/1.06    v1_funct_2(sK4,sK2,sK3)),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f52,plain,(
% 3.20/1.06    v1_funct_1(sK4)),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f37,plain,(
% 3.20/1.06    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f26])).
% 3.20/1.06  
% 3.20/1.06  fof(f2,axiom,(
% 3.20/1.06    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f38,plain,(
% 3.20/1.06    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f2])).
% 3.20/1.06  
% 3.20/1.06  fof(f7,axiom,(
% 3.20/1.06    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f17,plain,(
% 3.20/1.06    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.20/1.06    inference(ennf_transformation,[],[f7])).
% 3.20/1.06  
% 3.20/1.06  fof(f48,plain,(
% 3.20/1.06    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f17])).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1,plain,
% 3.20/1.06      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.20/1.06      inference(cnf_transformation,[],[f36]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_891,plain,
% 3.20/1.06      ( X0 = X1
% 3.20/1.06      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.20/1.06      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_11,plain,
% 3.20/1.06      ( ~ v1_relat_1(X0)
% 3.20/1.06      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.20/1.06      inference(cnf_transformation,[],[f47]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_13,plain,
% 3.20/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.06      | v1_relat_1(X0) ),
% 3.20/1.06      inference(cnf_transformation,[],[f49]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_19,negated_conjecture,
% 3.20/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.20/1.06      inference(cnf_transformation,[],[f54]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_304,plain,
% 3.20/1.06      ( v1_relat_1(X0)
% 3.20/1.06      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.20/1.06      | sK4 != X0 ),
% 3.20/1.06      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_305,plain,
% 3.20/1.06      ( v1_relat_1(sK4)
% 3.20/1.06      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.06      inference(unflattening,[status(thm)],[c_304]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_391,plain,
% 3.20/1.06      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.20/1.06      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.20/1.06      | sK4 != X0 ),
% 3.20/1.06      inference(resolution_lifted,[status(thm)],[c_11,c_305]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_392,plain,
% 3.20/1.06      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 3.20/1.06      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.06      inference(unflattening,[status(thm)],[c_391]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_531,plain,( X0 = X0 ),theory(equality) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1042,plain,
% 3.20/1.06      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_531]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1044,plain,
% 3.20/1.06      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 3.20/1.06      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_392]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1117,plain,
% 3.20/1.06      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.20/1.06      inference(global_propositional_subsumption,
% 3.20/1.06                [status(thm)],
% 3.20/1.06                [c_392,c_1042,c_1044]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_9,plain,
% 3.20/1.06      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.20/1.06      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.20/1.06      | ~ v1_relat_1(X1) ),
% 3.20/1.06      inference(cnf_transformation,[],[f44]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_361,plain,
% 3.20/1.06      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.20/1.06      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.20/1.07      | sK4 != X1 ),
% 3.20/1.07      inference(resolution_lifted,[status(thm)],[c_9,c_305]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_362,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 3.20/1.07      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.07      inference(unflattening,[status(thm)],[c_361]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_524,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 3.20/1.07      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4)
% 3.20/1.07      | ~ sP2_iProver_split ),
% 3.20/1.07      inference(splitting,
% 3.20/1.07                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.20/1.07                [c_362]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_875,plain,
% 3.20/1.07      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.20/1.07      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
% 3.20/1.07      | sP2_iProver_split != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_525,plain,
% 3.20/1.07      ( sP2_iProver_split | sP0_iProver_split ),
% 3.20/1.07      inference(splitting,
% 3.20/1.07                [splitting(split),new_symbols(definition,[])],
% 3.20/1.07                [c_362]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_562,plain,
% 3.20/1.07      ( sP2_iProver_split = iProver_top
% 3.20/1.07      | sP0_iProver_split = iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_563,plain,
% 3.20/1.07      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.20/1.07      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
% 3.20/1.07      | sP2_iProver_split != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_8,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.20/1.07      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.20/1.07      | ~ v1_relat_1(X1) ),
% 3.20/1.07      inference(cnf_transformation,[],[f45]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_376,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.20/1.07      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.20/1.07      | sK4 != X1 ),
% 3.20/1.07      inference(resolution_lifted,[status(thm)],[c_8,c_305]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_377,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 3.20/1.07      | r2_hidden(sK1(X0,X1,sK4),X1)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.07      inference(unflattening,[status(thm)],[c_376]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_521,plain,
% 3.20/1.07      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.20/1.07      | ~ sP0_iProver_split ),
% 3.20/1.07      inference(splitting,
% 3.20/1.07                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.20/1.07                [c_377]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1043,plain,
% 3.20/1.07      ( ~ sP0_iProver_split
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.07      inference(instantiation,[status(thm)],[c_521]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1046,plain,
% 3.20/1.07      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.20/1.07      | sP0_iProver_split != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1763,plain,
% 3.20/1.07      ( r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top
% 3.20/1.07      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 3.20/1.07      inference(global_propositional_subsumption,
% 3.20/1.07                [status(thm)],
% 3.20/1.07                [c_875,c_562,c_563,c_1042,c_1046]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1764,plain,
% 3.20/1.07      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.20/1.07      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
% 3.20/1.07      inference(renaming,[status(thm)],[c_1763]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_6,plain,
% 3.20/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/1.07      | ~ r2_hidden(X2,X0)
% 3.20/1.07      | r2_hidden(X2,X1) ),
% 3.20/1.07      inference(cnf_transformation,[],[f42]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_280,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,X1)
% 3.20/1.07      | r2_hidden(X0,X2)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X2)
% 3.20/1.07      | sK4 != X1 ),
% 3.20/1.07      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_281,plain,
% 3.20/1.07      ( r2_hidden(X0,X1)
% 3.20/1.07      | ~ r2_hidden(X0,sK4)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
% 3.20/1.07      inference(unflattening,[status(thm)],[c_280]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_883,plain,
% 3.20/1.07      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
% 3.20/1.07      | r2_hidden(X1,X0) = iProver_top
% 3.20/1.07      | r2_hidden(X1,sK4) != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1124,plain,
% 3.20/1.07      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) = iProver_top
% 3.20/1.07      | r2_hidden(X0,sK4) != iProver_top ),
% 3.20/1.07      inference(equality_resolution,[status(thm)],[c_883]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4,plain,
% 3.20/1.07      ( r2_hidden(X0,X1)
% 3.20/1.07      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.20/1.07      inference(cnf_transformation,[],[f40]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_889,plain,
% 3.20/1.07      ( r2_hidden(X0,X1) = iProver_top
% 3.20/1.07      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1504,plain,
% 3.20/1.07      ( r2_hidden(X0,sK3) = iProver_top
% 3.20/1.07      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_1124,c_889]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1922,plain,
% 3.20/1.07      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.20/1.07      | r2_hidden(X0,sK3) = iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_1764,c_1504]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_3332,plain,
% 3.20/1.07      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 3.20/1.07      | r2_hidden(X0,sK3) = iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_1117,c_1922]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_3515,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = X0
% 3.20/1.07      | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top
% 3.20/1.07      | r2_hidden(sK0(k2_relat_1(sK4),X0),sK3) = iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_891,c_3332]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_18,negated_conjecture,
% 3.20/1.07      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 3.20/1.07      inference(cnf_transformation,[],[f55]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_886,plain,
% 3.20/1.07      ( r2_hidden(X0,sK3) != iProver_top
% 3.20/1.07      | r2_hidden(sK5(X0),sK2) = iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_3514,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = X0
% 3.20/1.07      | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top
% 3.20/1.07      | r2_hidden(sK0(X0,k2_relat_1(sK4)),sK3) = iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_891,c_3332]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_17,negated_conjecture,
% 3.20/1.07      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 3.20/1.07      inference(cnf_transformation,[],[f56]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_887,plain,
% 3.20/1.07      ( k1_funct_1(sK4,sK5(X0)) = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_3844,plain,
% 3.20/1.07      ( k1_funct_1(sK4,sK5(sK0(X0,k2_relat_1(sK4)))) = sK0(X0,k2_relat_1(sK4))
% 3.20/1.07      | k2_relat_1(sK4) = X0
% 3.20/1.07      | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) = iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_3514,c_887]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4030,plain,
% 3.20/1.07      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4))
% 3.20/1.07      | k2_relat_1(sK4) = sK3 ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_3844,c_887]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_14,plain,
% 3.20/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.07      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.20/1.07      inference(cnf_transformation,[],[f50]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_295,plain,
% 3.20/1.07      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.20/1.07      | sK4 != X2 ),
% 3.20/1.07      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_296,plain,
% 3.20/1.07      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 3.20/1.07      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.20/1.07      inference(unflattening,[status(thm)],[c_295]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1055,plain,
% 3.20/1.07      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.20/1.07      inference(equality_resolution,[status(thm)],[c_296]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_16,negated_conjecture,
% 3.20/1.07      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 3.20/1.07      inference(cnf_transformation,[],[f57]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1076,plain,
% 3.20/1.07      ( k2_relat_1(sK4) != sK3 ),
% 3.20/1.07      inference(demodulation,[status(thm)],[c_1055,c_16]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4062,plain,
% 3.20/1.07      ( k1_funct_1(sK4,sK5(sK0(sK3,k2_relat_1(sK4)))) = sK0(sK3,k2_relat_1(sK4)) ),
% 3.20/1.07      inference(global_propositional_subsumption,
% 3.20/1.07                [status(thm)],
% 3.20/1.07                [c_4030,c_1076]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_15,plain,
% 3.20/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.07      | ~ r2_hidden(X3,X1)
% 3.20/1.07      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.20/1.07      | ~ v1_funct_1(X0)
% 3.20/1.07      | k1_xboole_0 = X2 ),
% 3.20/1.07      inference(cnf_transformation,[],[f51]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_20,negated_conjecture,
% 3.20/1.07      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.20/1.07      inference(cnf_transformation,[],[f53]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_255,plain,
% 3.20/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/1.07      | ~ r2_hidden(X3,X1)
% 3.20/1.07      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.20/1.07      | ~ v1_funct_1(X0)
% 3.20/1.07      | sK4 != X0
% 3.20/1.07      | sK3 != X2
% 3.20/1.07      | sK2 != X1
% 3.20/1.07      | k1_xboole_0 = X2 ),
% 3.20/1.07      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_256,plain,
% 3.20/1.07      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.20/1.07      | ~ r2_hidden(X0,sK2)
% 3.20/1.07      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.20/1.07      | ~ v1_funct_1(sK4)
% 3.20/1.07      | k1_xboole_0 = sK3 ),
% 3.20/1.07      inference(unflattening,[status(thm)],[c_255]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_21,negated_conjecture,
% 3.20/1.07      ( v1_funct_1(sK4) ),
% 3.20/1.07      inference(cnf_transformation,[],[f52]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_260,plain,
% 3.20/1.07      ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.20/1.07      | ~ r2_hidden(X0,sK2)
% 3.20/1.07      | k1_xboole_0 = sK3 ),
% 3.20/1.07      inference(global_propositional_subsumption,
% 3.20/1.07                [status(thm)],
% 3.20/1.07                [c_256,c_21,c_19]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_261,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,sK2)
% 3.20/1.07      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.20/1.07      | k1_xboole_0 = sK3 ),
% 3.20/1.07      inference(renaming,[status(thm)],[c_260]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_884,plain,
% 3.20/1.07      ( k1_xboole_0 = sK3
% 3.20/1.07      | r2_hidden(X0,sK2) != iProver_top
% 3.20/1.07      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1351,plain,
% 3.20/1.07      ( sK3 = k1_xboole_0
% 3.20/1.07      | r2_hidden(X0,sK2) != iProver_top
% 3.20/1.07      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 3.20/1.07      inference(light_normalisation,[status(thm)],[c_884,c_1055]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4065,plain,
% 3.20/1.07      ( sK3 = k1_xboole_0
% 3.20/1.07      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) = iProver_top
% 3.20/1.07      | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_4062,c_1351]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_0,plain,
% 3.20/1.07      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.20/1.07      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.20/1.07      | X1 = X0 ),
% 3.20/1.07      inference(cnf_transformation,[],[f37]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1333,plain,
% 3.20/1.07      ( ~ r2_hidden(sK0(X0,k2_relat_1(sK4)),X0)
% 3.20/1.07      | ~ r2_hidden(sK0(X0,k2_relat_1(sK4)),k2_relat_1(sK4))
% 3.20/1.07      | k2_relat_1(sK4) = X0 ),
% 3.20/1.07      inference(instantiation,[status(thm)],[c_0]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1339,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = X0
% 3.20/1.07      | r2_hidden(sK0(X0,k2_relat_1(sK4)),X0) != iProver_top
% 3.20/1.07      | r2_hidden(sK0(X0,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_1341,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = sK3
% 3.20/1.07      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),k2_relat_1(sK4)) != iProver_top
% 3.20/1.07      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
% 3.20/1.07      inference(instantiation,[status(thm)],[c_1339]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_3593,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = sK3
% 3.20/1.07      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) = iProver_top ),
% 3.20/1.07      inference(instantiation,[status(thm)],[c_3514]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4471,plain,
% 3.20/1.07      ( sK3 = k1_xboole_0
% 3.20/1.07      | r2_hidden(sK5(sK0(sK3,k2_relat_1(sK4))),sK2) != iProver_top ),
% 3.20/1.07      inference(global_propositional_subsumption,
% 3.20/1.07                [status(thm)],
% 3.20/1.07                [c_4065,c_1076,c_1341,c_3593]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4477,plain,
% 3.20/1.07      ( sK3 = k1_xboole_0
% 3.20/1.07      | r2_hidden(sK0(sK3,k2_relat_1(sK4)),sK3) != iProver_top ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_886,c_4471]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4524,plain,
% 3.20/1.07      ( sK3 = k1_xboole_0 ),
% 3.20/1.07      inference(global_propositional_subsumption,
% 3.20/1.07                [status(thm)],
% 3.20/1.07                [c_4477,c_1076,c_3593]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_5069,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = X0
% 3.20/1.07      | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top
% 3.20/1.07      | r2_hidden(sK0(k2_relat_1(sK4),X0),k1_xboole_0) = iProver_top ),
% 3.20/1.07      inference(light_normalisation,[status(thm)],[c_3515,c_4524]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_2,plain,
% 3.20/1.07      ( r1_tarski(k1_xboole_0,X0) ),
% 3.20/1.07      inference(cnf_transformation,[],[f38]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_12,plain,
% 3.20/1.07      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.20/1.07      inference(cnf_transformation,[],[f48]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_244,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.20/1.07      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_245,plain,
% 3.20/1.07      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.20/1.07      inference(unflattening,[status(thm)],[c_244]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_885,plain,
% 3.20/1.07      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.20/1.07      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_5073,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = X0
% 3.20/1.07      | r2_hidden(sK0(k2_relat_1(sK4),X0),X0) = iProver_top ),
% 3.20/1.07      inference(forward_subsumption_resolution,
% 3.20/1.07                [status(thm)],
% 3.20/1.07                [c_5069,c_885]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_5076,plain,
% 3.20/1.07      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 3.20/1.07      inference(superposition,[status(thm)],[c_5073,c_885]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(c_4551,plain,
% 3.20/1.07      ( k2_relat_1(sK4) != k1_xboole_0 ),
% 3.20/1.07      inference(demodulation,[status(thm)],[c_4524,c_1076]) ).
% 3.20/1.07  
% 3.20/1.07  cnf(contradiction,plain,
% 3.20/1.07      ( $false ),
% 3.20/1.07      inference(minisat,[status(thm)],[c_5076,c_4551]) ).
% 3.20/1.07  
% 3.20/1.07  
% 3.20/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.07  
% 3.20/1.07  ------                               Statistics
% 3.20/1.07  
% 3.20/1.07  ------ General
% 3.20/1.07  
% 3.20/1.07  abstr_ref_over_cycles:                  0
% 3.20/1.07  abstr_ref_under_cycles:                 0
% 3.20/1.07  gc_basic_clause_elim:                   0
% 3.20/1.07  forced_gc_time:                         0
% 3.20/1.07  parsing_time:                           0.007
% 3.20/1.07  unif_index_cands_time:                  0.
% 3.20/1.07  unif_index_add_time:                    0.
% 3.20/1.07  orderings_time:                         0.
% 3.20/1.07  out_proof_time:                         0.007
% 3.20/1.07  total_time:                             0.172
% 3.20/1.07  num_of_symbols:                         57
% 3.20/1.07  num_of_terms:                           5025
% 3.20/1.07  
% 3.20/1.07  ------ Preprocessing
% 3.20/1.07  
% 3.20/1.07  num_of_splits:                          8
% 3.20/1.07  num_of_split_atoms:                     5
% 3.20/1.07  num_of_reused_defs:                     3
% 3.20/1.07  num_eq_ax_congr_red:                    24
% 3.20/1.07  num_of_sem_filtered_clauses:            1
% 3.20/1.07  num_of_subtypes:                        0
% 3.20/1.07  monotx_restored_types:                  0
% 3.20/1.07  sat_num_of_epr_types:                   0
% 3.20/1.07  sat_num_of_non_cyclic_types:            0
% 3.20/1.07  sat_guarded_non_collapsed_types:        0
% 3.20/1.07  num_pure_diseq_elim:                    0
% 3.20/1.07  simp_replaced_by:                       0
% 3.20/1.07  res_preprocessed:                       108
% 3.20/1.07  prep_upred:                             0
% 3.20/1.07  prep_unflattend:                        13
% 3.20/1.07  smt_new_axioms:                         0
% 3.20/1.07  pred_elim_cands:                        1
% 3.20/1.07  pred_elim:                              5
% 3.20/1.07  pred_elim_cl:                           5
% 3.20/1.07  pred_elim_cycles:                       7
% 3.20/1.07  merged_defs:                            0
% 3.20/1.07  merged_defs_ncl:                        0
% 3.20/1.07  bin_hyper_res:                          0
% 3.20/1.07  prep_cycles:                            4
% 3.20/1.07  pred_elim_time:                         0.004
% 3.20/1.07  splitting_time:                         0.
% 3.20/1.07  sem_filter_time:                        0.
% 3.20/1.07  monotx_time:                            0.
% 3.20/1.07  subtype_inf_time:                       0.
% 3.20/1.07  
% 3.20/1.07  ------ Problem properties
% 3.20/1.07  
% 3.20/1.07  clauses:                                25
% 3.20/1.07  conjectures:                            3
% 3.20/1.07  epr:                                    5
% 3.20/1.07  horn:                                   19
% 3.20/1.07  ground:                                 5
% 3.20/1.07  unary:                                  2
% 3.20/1.07  binary:                                 14
% 3.20/1.07  lits:                                   59
% 3.20/1.07  lits_eq:                                14
% 3.20/1.07  fd_pure:                                0
% 3.20/1.07  fd_pseudo:                              0
% 3.20/1.07  fd_cond:                                0
% 3.20/1.07  fd_pseudo_cond:                         2
% 3.20/1.07  ac_symbols:                             0
% 3.20/1.07  
% 3.20/1.07  ------ Propositional Solver
% 3.20/1.07  
% 3.20/1.07  prop_solver_calls:                      28
% 3.20/1.07  prop_fast_solver_calls:                 746
% 3.20/1.07  smt_solver_calls:                       0
% 3.20/1.07  smt_fast_solver_calls:                  0
% 3.20/1.07  prop_num_of_clauses:                    1998
% 3.20/1.07  prop_preprocess_simplified:             6315
% 3.20/1.07  prop_fo_subsumed:                       16
% 3.20/1.07  prop_solver_time:                       0.
% 3.20/1.07  smt_solver_time:                        0.
% 3.20/1.07  smt_fast_solver_time:                   0.
% 3.20/1.07  prop_fast_solver_time:                  0.
% 3.20/1.07  prop_unsat_core_time:                   0.
% 3.20/1.07  
% 3.20/1.07  ------ QBF
% 3.20/1.07  
% 3.20/1.07  qbf_q_res:                              0
% 3.20/1.07  qbf_num_tautologies:                    0
% 3.20/1.07  qbf_prep_cycles:                        0
% 3.20/1.07  
% 3.20/1.07  ------ BMC1
% 3.20/1.07  
% 3.20/1.07  bmc1_current_bound:                     -1
% 3.20/1.07  bmc1_last_solved_bound:                 -1
% 3.20/1.07  bmc1_unsat_core_size:                   -1
% 3.20/1.07  bmc1_unsat_core_parents_size:           -1
% 3.20/1.07  bmc1_merge_next_fun:                    0
% 3.20/1.07  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.07  
% 3.20/1.07  ------ Instantiation
% 3.20/1.07  
% 3.20/1.07  inst_num_of_clauses:                    596
% 3.20/1.07  inst_num_in_passive:                    337
% 3.20/1.07  inst_num_in_active:                     259
% 3.20/1.07  inst_num_in_unprocessed:                0
% 3.20/1.07  inst_num_of_loops:                      320
% 3.20/1.07  inst_num_of_learning_restarts:          0
% 3.20/1.07  inst_num_moves_active_passive:          58
% 3.20/1.07  inst_lit_activity:                      0
% 3.20/1.07  inst_lit_activity_moves:                0
% 3.20/1.07  inst_num_tautologies:                   0
% 3.20/1.07  inst_num_prop_implied:                  0
% 3.20/1.07  inst_num_existing_simplified:           0
% 3.20/1.07  inst_num_eq_res_simplified:             0
% 3.20/1.07  inst_num_child_elim:                    0
% 3.20/1.07  inst_num_of_dismatching_blockings:      87
% 3.20/1.07  inst_num_of_non_proper_insts:           472
% 3.20/1.07  inst_num_of_duplicates:                 0
% 3.20/1.07  inst_inst_num_from_inst_to_res:         0
% 3.20/1.07  inst_dismatching_checking_time:         0.
% 3.20/1.07  
% 3.20/1.07  ------ Resolution
% 3.20/1.07  
% 3.20/1.07  res_num_of_clauses:                     0
% 3.20/1.07  res_num_in_passive:                     0
% 3.20/1.07  res_num_in_active:                      0
% 3.20/1.07  res_num_of_loops:                       112
% 3.20/1.07  res_forward_subset_subsumed:            94
% 3.20/1.07  res_backward_subset_subsumed:           0
% 3.20/1.07  res_forward_subsumed:                   0
% 3.20/1.07  res_backward_subsumed:                  0
% 3.20/1.07  res_forward_subsumption_resolution:     0
% 3.20/1.07  res_backward_subsumption_resolution:    0
% 3.20/1.07  res_clause_to_clause_subsumption:       334
% 3.20/1.07  res_orphan_elimination:                 0
% 3.20/1.07  res_tautology_del:                      17
% 3.20/1.07  res_num_eq_res_simplified:              0
% 3.20/1.07  res_num_sel_changes:                    0
% 3.20/1.07  res_moves_from_active_to_pass:          0
% 3.20/1.07  
% 3.20/1.07  ------ Superposition
% 3.20/1.07  
% 3.20/1.07  sup_time_total:                         0.
% 3.20/1.07  sup_time_generating:                    0.
% 3.20/1.07  sup_time_sim_full:                      0.
% 3.20/1.07  sup_time_sim_immed:                     0.
% 3.20/1.07  
% 3.20/1.07  sup_num_of_clauses:                     107
% 3.20/1.07  sup_num_in_active:                      30
% 3.20/1.07  sup_num_in_passive:                     77
% 3.20/1.07  sup_num_of_loops:                       63
% 3.20/1.07  sup_fw_superposition:                   84
% 3.20/1.07  sup_bw_superposition:                   88
% 3.20/1.07  sup_immediate_simplified:               19
% 3.20/1.07  sup_given_eliminated:                   2
% 3.20/1.07  comparisons_done:                       0
% 3.20/1.07  comparisons_avoided:                    56
% 3.20/1.07  
% 3.20/1.07  ------ Simplifications
% 3.20/1.07  
% 3.20/1.07  
% 3.20/1.07  sim_fw_subset_subsumed:                 12
% 3.20/1.07  sim_bw_subset_subsumed:                 10
% 3.20/1.07  sim_fw_subsumed:                        6
% 3.20/1.07  sim_bw_subsumed:                        0
% 3.20/1.07  sim_fw_subsumption_res:                 1
% 3.20/1.07  sim_bw_subsumption_res:                 0
% 3.20/1.07  sim_tautology_del:                      6
% 3.20/1.07  sim_eq_tautology_del:                   21
% 3.20/1.07  sim_eq_res_simp:                        1
% 3.20/1.07  sim_fw_demodulated:                     0
% 3.20/1.07  sim_bw_demodulated:                     33
% 3.20/1.07  sim_light_normalised:                   3
% 3.20/1.07  sim_joinable_taut:                      0
% 3.20/1.07  sim_joinable_simp:                      0
% 3.20/1.07  sim_ac_normalised:                      0
% 3.20/1.07  sim_smt_subsumption:                    0
% 3.20/1.07  
%------------------------------------------------------------------------------
