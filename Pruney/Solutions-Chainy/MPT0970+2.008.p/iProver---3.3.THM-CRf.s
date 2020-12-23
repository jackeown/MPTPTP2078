%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:46 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 467 expanded)
%              Number of clauses        :   91 ( 165 expanded)
%              Number of leaves         :   19 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          :  443 (1931 expanded)
%              Number of equality atoms :  159 ( 521 expanded)
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

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK4(X3)) = X3
        & r2_hidden(sK4(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
   => ( k2_relset_1(sK1,sK2,sK3) != sK2
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK3,X4) = X3
              & r2_hidden(X4,sK1) )
          | ~ r2_hidden(X3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    & ! [X3] :
        ( ( k1_funct_1(sK3,sK4(X3)) = X3
          & r2_hidden(sK4(X3),sK1) )
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f39,f38])).

fof(f68,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,sK4(X3)) = X3
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f51,plain,(
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

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X3] :
      ( r2_hidden(sK4(X3),sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2028,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2020,plain,
    ( k1_funct_1(sK3,sK4(X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2455,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,X0))) = sK0(sK2,X0)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_2020])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2018,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_412,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_13])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_2016,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_2714,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2018,c_2016])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2026,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2878,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2714,c_2026])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2177,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_2178,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2177])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2204,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2233,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2371,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2233])).

cnf(c_2372,plain,
    ( sK2 = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2371])).

cnf(c_1528,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2195,plain,
    ( k2_relset_1(sK1,sK2,sK3) != X0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_2654,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_3216,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2878,c_26,c_31,c_23,c_2178,c_2204,c_2372,c_2654])).

cnf(c_3221,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,k2_relat_1(sK3)))) = sK0(sK2,k2_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_2455,c_3216])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_904,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_905,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_907,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2022,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2751,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2018,c_2022])).

cnf(c_3119,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_907,c_2751])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_87,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_91,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2186,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
    | k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1529,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2258,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_2260,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_1527,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2279,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_2325,plain,
    ( r2_hidden(sK0(sK2,k2_relset_1(sK1,sK2,sK3)),sK2)
    | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_220,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_221])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_276])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_2516,plain,
    ( ~ r2_hidden(sK0(sK2,k2_relset_1(sK1,sK2,sK3)),sK2)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_2228,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | k2_relset_1(sK1,sK2,sK3) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_2592,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_2838,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_3121,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3119,c_26,c_23,c_87,c_91,c_2177,c_2186,c_2204,c_2260,c_2279,c_2325,c_2516,c_2838])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_389,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_390,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_390])).

cnf(c_430,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X2),k2_relat_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1523,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_430])).

cnf(c_2015,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_1525,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_430])).

cnf(c_1553,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_1557,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_1524,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_430])).

cnf(c_2161,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_2162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_2340,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2015,c_31,c_1553,c_1557,c_2162])).

cnf(c_2341,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2340])).

cnf(c_3126,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3121,c_2341])).

cnf(c_3954,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3221,c_3126])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2914,plain,
    ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2915,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_2559,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
    | r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2566,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) = iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2559])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2560,plain,
    ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3))
    | r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2564,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2560])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3954,c_2915,c_2654,c_2566,c_2564,c_2372,c_2204,c_2178,c_23,c_31,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.93/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/0.98  
% 2.93/0.98  ------  iProver source info
% 2.93/0.98  
% 2.93/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.93/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/0.98  git: non_committed_changes: false
% 2.93/0.98  git: last_make_outside_of_git: false
% 2.93/0.98  
% 2.93/0.98  ------ 
% 2.93/0.98  
% 2.93/0.98  ------ Input Options
% 2.93/0.98  
% 2.93/0.98  --out_options                           all
% 2.93/0.98  --tptp_safe_out                         true
% 2.93/0.98  --problem_path                          ""
% 2.93/0.98  --include_path                          ""
% 2.93/0.98  --clausifier                            res/vclausify_rel
% 2.93/0.98  --clausifier_options                    --mode clausify
% 2.93/0.98  --stdin                                 false
% 2.93/0.98  --stats_out                             all
% 2.93/0.98  
% 2.93/0.98  ------ General Options
% 2.93/0.98  
% 2.93/0.98  --fof                                   false
% 2.93/0.98  --time_out_real                         305.
% 2.93/0.98  --time_out_virtual                      -1.
% 2.93/0.98  --symbol_type_check                     false
% 2.93/0.98  --clausify_out                          false
% 2.93/0.98  --sig_cnt_out                           false
% 2.93/0.98  --trig_cnt_out                          false
% 2.93/0.98  --trig_cnt_out_tolerance                1.
% 2.93/0.98  --trig_cnt_out_sk_spl                   false
% 2.93/0.98  --abstr_cl_out                          false
% 2.93/0.98  
% 2.93/0.98  ------ Global Options
% 2.93/0.98  
% 2.93/0.98  --schedule                              default
% 2.93/0.98  --add_important_lit                     false
% 2.93/0.98  --prop_solver_per_cl                    1000
% 2.93/0.98  --min_unsat_core                        false
% 2.93/0.98  --soft_assumptions                      false
% 2.93/0.98  --soft_lemma_size                       3
% 2.93/0.98  --prop_impl_unit_size                   0
% 2.93/0.98  --prop_impl_unit                        []
% 2.93/0.98  --share_sel_clauses                     true
% 2.93/0.98  --reset_solvers                         false
% 2.93/0.98  --bc_imp_inh                            [conj_cone]
% 2.93/0.98  --conj_cone_tolerance                   3.
% 2.93/0.98  --extra_neg_conj                        none
% 2.93/0.98  --large_theory_mode                     true
% 2.93/0.98  --prolific_symb_bound                   200
% 2.93/0.98  --lt_threshold                          2000
% 2.93/0.98  --clause_weak_htbl                      true
% 2.93/0.98  --gc_record_bc_elim                     false
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing Options
% 2.93/0.98  
% 2.93/0.98  --preprocessing_flag                    true
% 2.93/0.98  --time_out_prep_mult                    0.1
% 2.93/0.98  --splitting_mode                        input
% 2.93/0.98  --splitting_grd                         true
% 2.93/0.98  --splitting_cvd                         false
% 2.93/0.98  --splitting_cvd_svl                     false
% 2.93/0.98  --splitting_nvd                         32
% 2.93/0.98  --sub_typing                            true
% 2.93/0.98  --prep_gs_sim                           true
% 2.93/0.98  --prep_unflatten                        true
% 2.93/0.98  --prep_res_sim                          true
% 2.93/0.98  --prep_upred                            true
% 2.93/0.98  --prep_sem_filter                       exhaustive
% 2.93/0.98  --prep_sem_filter_out                   false
% 2.93/0.98  --pred_elim                             true
% 2.93/0.98  --res_sim_input                         true
% 2.93/0.98  --eq_ax_congr_red                       true
% 2.93/0.98  --pure_diseq_elim                       true
% 2.93/0.98  --brand_transform                       false
% 2.93/0.98  --non_eq_to_eq                          false
% 2.93/0.98  --prep_def_merge                        true
% 2.93/0.98  --prep_def_merge_prop_impl              false
% 2.93/0.98  --prep_def_merge_mbd                    true
% 2.93/0.98  --prep_def_merge_tr_red                 false
% 2.93/0.98  --prep_def_merge_tr_cl                  false
% 2.93/0.98  --smt_preprocessing                     true
% 2.93/0.98  --smt_ac_axioms                         fast
% 2.93/0.98  --preprocessed_out                      false
% 2.93/0.98  --preprocessed_stats                    false
% 2.93/0.98  
% 2.93/0.98  ------ Abstraction refinement Options
% 2.93/0.98  
% 2.93/0.98  --abstr_ref                             []
% 2.93/0.98  --abstr_ref_prep                        false
% 2.93/0.98  --abstr_ref_until_sat                   false
% 2.93/0.98  --abstr_ref_sig_restrict                funpre
% 2.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.98  --abstr_ref_under                       []
% 2.93/0.98  
% 2.93/0.98  ------ SAT Options
% 2.93/0.98  
% 2.93/0.98  --sat_mode                              false
% 2.93/0.98  --sat_fm_restart_options                ""
% 2.93/0.98  --sat_gr_def                            false
% 2.93/0.98  --sat_epr_types                         true
% 2.93/0.98  --sat_non_cyclic_types                  false
% 2.93/0.98  --sat_finite_models                     false
% 2.93/0.98  --sat_fm_lemmas                         false
% 2.93/0.98  --sat_fm_prep                           false
% 2.93/0.98  --sat_fm_uc_incr                        true
% 2.93/0.98  --sat_out_model                         small
% 2.93/0.98  --sat_out_clauses                       false
% 2.93/0.98  
% 2.93/0.98  ------ QBF Options
% 2.93/0.98  
% 2.93/0.98  --qbf_mode                              false
% 2.93/0.98  --qbf_elim_univ                         false
% 2.93/0.98  --qbf_dom_inst                          none
% 2.93/0.98  --qbf_dom_pre_inst                      false
% 2.93/0.98  --qbf_sk_in                             false
% 2.93/0.98  --qbf_pred_elim                         true
% 2.93/0.98  --qbf_split                             512
% 2.93/0.98  
% 2.93/0.98  ------ BMC1 Options
% 2.93/0.98  
% 2.93/0.98  --bmc1_incremental                      false
% 2.93/0.98  --bmc1_axioms                           reachable_all
% 2.93/0.98  --bmc1_min_bound                        0
% 2.93/0.98  --bmc1_max_bound                        -1
% 2.93/0.98  --bmc1_max_bound_default                -1
% 2.93/0.98  --bmc1_symbol_reachability              true
% 2.93/0.98  --bmc1_property_lemmas                  false
% 2.93/0.98  --bmc1_k_induction                      false
% 2.93/0.98  --bmc1_non_equiv_states                 false
% 2.93/0.98  --bmc1_deadlock                         false
% 2.93/0.98  --bmc1_ucm                              false
% 2.93/0.98  --bmc1_add_unsat_core                   none
% 2.93/0.98  --bmc1_unsat_core_children              false
% 2.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.98  --bmc1_out_stat                         full
% 2.93/0.98  --bmc1_ground_init                      false
% 2.93/0.98  --bmc1_pre_inst_next_state              false
% 2.93/0.98  --bmc1_pre_inst_state                   false
% 2.93/0.98  --bmc1_pre_inst_reach_state             false
% 2.93/0.98  --bmc1_out_unsat_core                   false
% 2.93/0.98  --bmc1_aig_witness_out                  false
% 2.93/0.98  --bmc1_verbose                          false
% 2.93/0.98  --bmc1_dump_clauses_tptp                false
% 2.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.98  --bmc1_dump_file                        -
% 2.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.98  --bmc1_ucm_extend_mode                  1
% 2.93/0.98  --bmc1_ucm_init_mode                    2
% 2.93/0.98  --bmc1_ucm_cone_mode                    none
% 2.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.98  --bmc1_ucm_relax_model                  4
% 2.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.98  --bmc1_ucm_layered_model                none
% 2.93/0.99  --bmc1_ucm_max_lemma_size               10
% 2.93/0.99  
% 2.93/0.99  ------ AIG Options
% 2.93/0.99  
% 2.93/0.99  --aig_mode                              false
% 2.93/0.99  
% 2.93/0.99  ------ Instantiation Options
% 2.93/0.99  
% 2.93/0.99  --instantiation_flag                    true
% 2.93/0.99  --inst_sos_flag                         false
% 2.93/0.99  --inst_sos_phase                        true
% 2.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.99  --inst_lit_sel_side                     num_symb
% 2.93/0.99  --inst_solver_per_active                1400
% 2.93/0.99  --inst_solver_calls_frac                1.
% 2.93/0.99  --inst_passive_queue_type               priority_queues
% 2.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.99  --inst_passive_queues_freq              [25;2]
% 2.93/0.99  --inst_dismatching                      true
% 2.93/0.99  --inst_eager_unprocessed_to_passive     true
% 2.93/0.99  --inst_prop_sim_given                   true
% 2.93/0.99  --inst_prop_sim_new                     false
% 2.93/0.99  --inst_subs_new                         false
% 2.93/0.99  --inst_eq_res_simp                      false
% 2.93/0.99  --inst_subs_given                       false
% 2.93/0.99  --inst_orphan_elimination               true
% 2.93/0.99  --inst_learning_loop_flag               true
% 2.93/0.99  --inst_learning_start                   3000
% 2.93/0.99  --inst_learning_factor                  2
% 2.93/0.99  --inst_start_prop_sim_after_learn       3
% 2.93/0.99  --inst_sel_renew                        solver
% 2.93/0.99  --inst_lit_activity_flag                true
% 2.93/0.99  --inst_restr_to_given                   false
% 2.93/0.99  --inst_activity_threshold               500
% 2.93/0.99  --inst_out_proof                        true
% 2.93/0.99  
% 2.93/0.99  ------ Resolution Options
% 2.93/0.99  
% 2.93/0.99  --resolution_flag                       true
% 2.93/0.99  --res_lit_sel                           adaptive
% 2.93/0.99  --res_lit_sel_side                      none
% 2.93/0.99  --res_ordering                          kbo
% 2.93/0.99  --res_to_prop_solver                    active
% 2.93/0.99  --res_prop_simpl_new                    false
% 2.93/0.99  --res_prop_simpl_given                  true
% 2.93/0.99  --res_passive_queue_type                priority_queues
% 2.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.99  --res_passive_queues_freq               [15;5]
% 2.93/0.99  --res_forward_subs                      full
% 2.93/0.99  --res_backward_subs                     full
% 2.93/0.99  --res_forward_subs_resolution           true
% 2.93/0.99  --res_backward_subs_resolution          true
% 2.93/0.99  --res_orphan_elimination                true
% 2.93/0.99  --res_time_limit                        2.
% 2.93/0.99  --res_out_proof                         true
% 2.93/0.99  
% 2.93/0.99  ------ Superposition Options
% 2.93/0.99  
% 2.93/0.99  --superposition_flag                    true
% 2.93/0.99  --sup_passive_queue_type                priority_queues
% 2.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.99  --demod_completeness_check              fast
% 2.93/0.99  --demod_use_ground                      true
% 2.93/0.99  --sup_to_prop_solver                    passive
% 2.93/0.99  --sup_prop_simpl_new                    true
% 2.93/0.99  --sup_prop_simpl_given                  true
% 2.93/0.99  --sup_fun_splitting                     false
% 2.93/0.99  --sup_smt_interval                      50000
% 2.93/0.99  
% 2.93/0.99  ------ Superposition Simplification Setup
% 2.93/0.99  
% 2.93/0.99  --sup_indices_passive                   []
% 2.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.99  --sup_full_bw                           [BwDemod]
% 2.93/0.99  --sup_immed_triv                        [TrivRules]
% 2.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.99  --sup_immed_bw_main                     []
% 2.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.99  
% 2.93/0.99  ------ Combination Options
% 2.93/0.99  
% 2.93/0.99  --comb_res_mult                         3
% 2.93/0.99  --comb_sup_mult                         2
% 2.93/0.99  --comb_inst_mult                        10
% 2.93/0.99  
% 2.93/0.99  ------ Debug Options
% 2.93/0.99  
% 2.93/0.99  --dbg_backtrace                         false
% 2.93/0.99  --dbg_dump_prop_clauses                 false
% 2.93/0.99  --dbg_dump_prop_clauses_file            -
% 2.93/0.99  --dbg_out_stat                          false
% 2.93/0.99  ------ Parsing...
% 2.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/0.99  
% 2.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.93/0.99  
% 2.93/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/0.99  
% 2.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/0.99  ------ Proving...
% 2.93/0.99  ------ Problem Properties 
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  clauses                                 21
% 2.93/0.99  conjectures                             4
% 2.93/0.99  EPR                                     5
% 2.93/0.99  Horn                                    17
% 2.93/0.99  unary                                   3
% 2.93/0.99  binary                                  13
% 2.93/0.99  lits                                    45
% 2.93/0.99  lits eq                                 12
% 2.93/0.99  fd_pure                                 0
% 2.93/0.99  fd_pseudo                               0
% 2.93/0.99  fd_cond                                 0
% 2.93/0.99  fd_pseudo_cond                          1
% 2.93/0.99  AC symbols                              0
% 2.93/0.99  
% 2.93/0.99  ------ Schedule dynamic 5 is on 
% 2.93/0.99  
% 2.93/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  ------ 
% 2.93/0.99  Current options:
% 2.93/0.99  ------ 
% 2.93/0.99  
% 2.93/0.99  ------ Input Options
% 2.93/0.99  
% 2.93/0.99  --out_options                           all
% 2.93/0.99  --tptp_safe_out                         true
% 2.93/0.99  --problem_path                          ""
% 2.93/0.99  --include_path                          ""
% 2.93/0.99  --clausifier                            res/vclausify_rel
% 2.93/0.99  --clausifier_options                    --mode clausify
% 2.93/0.99  --stdin                                 false
% 2.93/0.99  --stats_out                             all
% 2.93/0.99  
% 2.93/0.99  ------ General Options
% 2.93/0.99  
% 2.93/0.99  --fof                                   false
% 2.93/0.99  --time_out_real                         305.
% 2.93/0.99  --time_out_virtual                      -1.
% 2.93/0.99  --symbol_type_check                     false
% 2.93/0.99  --clausify_out                          false
% 2.93/0.99  --sig_cnt_out                           false
% 2.93/0.99  --trig_cnt_out                          false
% 2.93/0.99  --trig_cnt_out_tolerance                1.
% 2.93/0.99  --trig_cnt_out_sk_spl                   false
% 2.93/0.99  --abstr_cl_out                          false
% 2.93/0.99  
% 2.93/0.99  ------ Global Options
% 2.93/0.99  
% 2.93/0.99  --schedule                              default
% 2.93/0.99  --add_important_lit                     false
% 2.93/0.99  --prop_solver_per_cl                    1000
% 2.93/0.99  --min_unsat_core                        false
% 2.93/0.99  --soft_assumptions                      false
% 2.93/0.99  --soft_lemma_size                       3
% 2.93/0.99  --prop_impl_unit_size                   0
% 2.93/0.99  --prop_impl_unit                        []
% 2.93/0.99  --share_sel_clauses                     true
% 2.93/0.99  --reset_solvers                         false
% 2.93/0.99  --bc_imp_inh                            [conj_cone]
% 2.93/0.99  --conj_cone_tolerance                   3.
% 2.93/0.99  --extra_neg_conj                        none
% 2.93/0.99  --large_theory_mode                     true
% 2.93/0.99  --prolific_symb_bound                   200
% 2.93/0.99  --lt_threshold                          2000
% 2.93/0.99  --clause_weak_htbl                      true
% 2.93/0.99  --gc_record_bc_elim                     false
% 2.93/0.99  
% 2.93/0.99  ------ Preprocessing Options
% 2.93/0.99  
% 2.93/0.99  --preprocessing_flag                    true
% 2.93/0.99  --time_out_prep_mult                    0.1
% 2.93/0.99  --splitting_mode                        input
% 2.93/0.99  --splitting_grd                         true
% 2.93/0.99  --splitting_cvd                         false
% 2.93/0.99  --splitting_cvd_svl                     false
% 2.93/0.99  --splitting_nvd                         32
% 2.93/0.99  --sub_typing                            true
% 2.93/0.99  --prep_gs_sim                           true
% 2.93/0.99  --prep_unflatten                        true
% 2.93/0.99  --prep_res_sim                          true
% 2.93/0.99  --prep_upred                            true
% 2.93/0.99  --prep_sem_filter                       exhaustive
% 2.93/0.99  --prep_sem_filter_out                   false
% 2.93/0.99  --pred_elim                             true
% 2.93/0.99  --res_sim_input                         true
% 2.93/0.99  --eq_ax_congr_red                       true
% 2.93/0.99  --pure_diseq_elim                       true
% 2.93/0.99  --brand_transform                       false
% 2.93/0.99  --non_eq_to_eq                          false
% 2.93/0.99  --prep_def_merge                        true
% 2.93/0.99  --prep_def_merge_prop_impl              false
% 2.93/0.99  --prep_def_merge_mbd                    true
% 2.93/0.99  --prep_def_merge_tr_red                 false
% 2.93/0.99  --prep_def_merge_tr_cl                  false
% 2.93/0.99  --smt_preprocessing                     true
% 2.93/0.99  --smt_ac_axioms                         fast
% 2.93/0.99  --preprocessed_out                      false
% 2.93/0.99  --preprocessed_stats                    false
% 2.93/0.99  
% 2.93/0.99  ------ Abstraction refinement Options
% 2.93/0.99  
% 2.93/0.99  --abstr_ref                             []
% 2.93/0.99  --abstr_ref_prep                        false
% 2.93/0.99  --abstr_ref_until_sat                   false
% 2.93/0.99  --abstr_ref_sig_restrict                funpre
% 2.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.99  --abstr_ref_under                       []
% 2.93/0.99  
% 2.93/0.99  ------ SAT Options
% 2.93/0.99  
% 2.93/0.99  --sat_mode                              false
% 2.93/0.99  --sat_fm_restart_options                ""
% 2.93/0.99  --sat_gr_def                            false
% 2.93/0.99  --sat_epr_types                         true
% 2.93/0.99  --sat_non_cyclic_types                  false
% 2.93/0.99  --sat_finite_models                     false
% 2.93/0.99  --sat_fm_lemmas                         false
% 2.93/0.99  --sat_fm_prep                           false
% 2.93/0.99  --sat_fm_uc_incr                        true
% 2.93/0.99  --sat_out_model                         small
% 2.93/0.99  --sat_out_clauses                       false
% 2.93/0.99  
% 2.93/0.99  ------ QBF Options
% 2.93/0.99  
% 2.93/0.99  --qbf_mode                              false
% 2.93/0.99  --qbf_elim_univ                         false
% 2.93/0.99  --qbf_dom_inst                          none
% 2.93/0.99  --qbf_dom_pre_inst                      false
% 2.93/0.99  --qbf_sk_in                             false
% 2.93/0.99  --qbf_pred_elim                         true
% 2.93/0.99  --qbf_split                             512
% 2.93/0.99  
% 2.93/0.99  ------ BMC1 Options
% 2.93/0.99  
% 2.93/0.99  --bmc1_incremental                      false
% 2.93/0.99  --bmc1_axioms                           reachable_all
% 2.93/0.99  --bmc1_min_bound                        0
% 2.93/0.99  --bmc1_max_bound                        -1
% 2.93/0.99  --bmc1_max_bound_default                -1
% 2.93/0.99  --bmc1_symbol_reachability              true
% 2.93/0.99  --bmc1_property_lemmas                  false
% 2.93/0.99  --bmc1_k_induction                      false
% 2.93/0.99  --bmc1_non_equiv_states                 false
% 2.93/0.99  --bmc1_deadlock                         false
% 2.93/0.99  --bmc1_ucm                              false
% 2.93/0.99  --bmc1_add_unsat_core                   none
% 2.93/0.99  --bmc1_unsat_core_children              false
% 2.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.99  --bmc1_out_stat                         full
% 2.93/0.99  --bmc1_ground_init                      false
% 2.93/0.99  --bmc1_pre_inst_next_state              false
% 2.93/0.99  --bmc1_pre_inst_state                   false
% 2.93/0.99  --bmc1_pre_inst_reach_state             false
% 2.93/0.99  --bmc1_out_unsat_core                   false
% 2.93/0.99  --bmc1_aig_witness_out                  false
% 2.93/0.99  --bmc1_verbose                          false
% 2.93/0.99  --bmc1_dump_clauses_tptp                false
% 2.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.99  --bmc1_dump_file                        -
% 2.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.99  --bmc1_ucm_extend_mode                  1
% 2.93/0.99  --bmc1_ucm_init_mode                    2
% 2.93/0.99  --bmc1_ucm_cone_mode                    none
% 2.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.99  --bmc1_ucm_relax_model                  4
% 2.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.99  --bmc1_ucm_layered_model                none
% 2.93/0.99  --bmc1_ucm_max_lemma_size               10
% 2.93/0.99  
% 2.93/0.99  ------ AIG Options
% 2.93/0.99  
% 2.93/0.99  --aig_mode                              false
% 2.93/0.99  
% 2.93/0.99  ------ Instantiation Options
% 2.93/0.99  
% 2.93/0.99  --instantiation_flag                    true
% 2.93/0.99  --inst_sos_flag                         false
% 2.93/0.99  --inst_sos_phase                        true
% 2.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.99  --inst_lit_sel_side                     none
% 2.93/0.99  --inst_solver_per_active                1400
% 2.93/0.99  --inst_solver_calls_frac                1.
% 2.93/0.99  --inst_passive_queue_type               priority_queues
% 2.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.99  --inst_passive_queues_freq              [25;2]
% 2.93/0.99  --inst_dismatching                      true
% 2.93/0.99  --inst_eager_unprocessed_to_passive     true
% 2.93/0.99  --inst_prop_sim_given                   true
% 2.93/0.99  --inst_prop_sim_new                     false
% 2.93/0.99  --inst_subs_new                         false
% 2.93/0.99  --inst_eq_res_simp                      false
% 2.93/0.99  --inst_subs_given                       false
% 2.93/0.99  --inst_orphan_elimination               true
% 2.93/0.99  --inst_learning_loop_flag               true
% 2.93/0.99  --inst_learning_start                   3000
% 2.93/0.99  --inst_learning_factor                  2
% 2.93/0.99  --inst_start_prop_sim_after_learn       3
% 2.93/0.99  --inst_sel_renew                        solver
% 2.93/0.99  --inst_lit_activity_flag                true
% 2.93/0.99  --inst_restr_to_given                   false
% 2.93/0.99  --inst_activity_threshold               500
% 2.93/0.99  --inst_out_proof                        true
% 2.93/0.99  
% 2.93/0.99  ------ Resolution Options
% 2.93/0.99  
% 2.93/0.99  --resolution_flag                       false
% 2.93/0.99  --res_lit_sel                           adaptive
% 2.93/0.99  --res_lit_sel_side                      none
% 2.93/0.99  --res_ordering                          kbo
% 2.93/0.99  --res_to_prop_solver                    active
% 2.93/0.99  --res_prop_simpl_new                    false
% 2.93/0.99  --res_prop_simpl_given                  true
% 2.93/0.99  --res_passive_queue_type                priority_queues
% 2.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.99  --res_passive_queues_freq               [15;5]
% 2.93/0.99  --res_forward_subs                      full
% 2.93/0.99  --res_backward_subs                     full
% 2.93/0.99  --res_forward_subs_resolution           true
% 2.93/0.99  --res_backward_subs_resolution          true
% 2.93/0.99  --res_orphan_elimination                true
% 2.93/0.99  --res_time_limit                        2.
% 2.93/0.99  --res_out_proof                         true
% 2.93/0.99  
% 2.93/0.99  ------ Superposition Options
% 2.93/0.99  
% 2.93/0.99  --superposition_flag                    true
% 2.93/0.99  --sup_passive_queue_type                priority_queues
% 2.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.99  --demod_completeness_check              fast
% 2.93/0.99  --demod_use_ground                      true
% 2.93/0.99  --sup_to_prop_solver                    passive
% 2.93/0.99  --sup_prop_simpl_new                    true
% 2.93/0.99  --sup_prop_simpl_given                  true
% 2.93/0.99  --sup_fun_splitting                     false
% 2.93/0.99  --sup_smt_interval                      50000
% 2.93/0.99  
% 2.93/0.99  ------ Superposition Simplification Setup
% 2.93/0.99  
% 2.93/0.99  --sup_indices_passive                   []
% 2.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.99  --sup_full_bw                           [BwDemod]
% 2.93/0.99  --sup_immed_triv                        [TrivRules]
% 2.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.99  --sup_immed_bw_main                     []
% 2.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.99  
% 2.93/0.99  ------ Combination Options
% 2.93/0.99  
% 2.93/0.99  --comb_res_mult                         3
% 2.93/0.99  --comb_sup_mult                         2
% 2.93/0.99  --comb_inst_mult                        10
% 2.93/0.99  
% 2.93/0.99  ------ Debug Options
% 2.93/0.99  
% 2.93/0.99  --dbg_backtrace                         false
% 2.93/0.99  --dbg_dump_prop_clauses                 false
% 2.93/0.99  --dbg_dump_prop_clauses_file            -
% 2.93/0.99  --dbg_out_stat                          false
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  ------ Proving...
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  % SZS status Theorem for theBenchmark.p
% 2.93/0.99  
% 2.93/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/0.99  
% 2.93/0.99  fof(f1,axiom,(
% 2.93/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f16,plain,(
% 2.93/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.93/0.99    inference(ennf_transformation,[],[f1])).
% 2.93/0.99  
% 2.93/0.99  fof(f29,plain,(
% 2.93/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/0.99    inference(nnf_transformation,[],[f16])).
% 2.93/0.99  
% 2.93/0.99  fof(f30,plain,(
% 2.93/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/0.99    inference(rectify,[],[f29])).
% 2.93/0.99  
% 2.93/0.99  fof(f31,plain,(
% 2.93/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.93/0.99    introduced(choice_axiom,[])).
% 2.93/0.99  
% 2.93/0.99  fof(f32,plain,(
% 2.93/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.93/0.99  
% 2.93/0.99  fof(f42,plain,(
% 2.93/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f32])).
% 2.93/0.99  
% 2.93/0.99  fof(f13,conjecture,(
% 2.93/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f14,negated_conjecture,(
% 2.93/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.93/0.99    inference(negated_conjecture,[],[f13])).
% 2.93/0.99  
% 2.93/0.99  fof(f27,plain,(
% 2.93/0.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.93/0.99    inference(ennf_transformation,[],[f14])).
% 2.93/0.99  
% 2.93/0.99  fof(f28,plain,(
% 2.93/0.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.93/0.99    inference(flattening,[],[f27])).
% 2.93/0.99  
% 2.93/0.99  fof(f39,plain,(
% 2.93/0.99    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK4(X3)) = X3 & r2_hidden(sK4(X3),X0)))) )),
% 2.93/0.99    introduced(choice_axiom,[])).
% 2.93/0.99  
% 2.93/0.99  fof(f38,plain,(
% 2.93/0.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : (? [X4] : (k1_funct_1(sK3,X4) = X3 & r2_hidden(X4,sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.93/0.99    introduced(choice_axiom,[])).
% 2.93/0.99  
% 2.93/0.99  fof(f40,plain,(
% 2.93/0.99    k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : ((k1_funct_1(sK3,sK4(X3)) = X3 & r2_hidden(sK4(X3),sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f39,f38])).
% 2.93/0.99  
% 2.93/0.99  fof(f68,plain,(
% 2.93/0.99    ( ! [X3] : (k1_funct_1(sK3,sK4(X3)) = X3 | ~r2_hidden(X3,sK2)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f40])).
% 2.93/0.99  
% 2.93/0.99  fof(f66,plain,(
% 2.93/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.93/0.99    inference(cnf_transformation,[],[f40])).
% 2.93/0.99  
% 2.93/0.99  fof(f9,axiom,(
% 2.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f15,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.93/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.93/0.99  
% 2.93/0.99  fof(f22,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.99    inference(ennf_transformation,[],[f15])).
% 2.93/0.99  
% 2.93/0.99  fof(f55,plain,(
% 2.93/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.99    inference(cnf_transformation,[],[f22])).
% 2.93/0.99  
% 2.93/0.99  fof(f6,axiom,(
% 2.93/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f18,plain,(
% 2.93/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.93/0.99    inference(ennf_transformation,[],[f6])).
% 2.93/0.99  
% 2.93/0.99  fof(f36,plain,(
% 2.93/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.93/0.99    inference(nnf_transformation,[],[f18])).
% 2.93/0.99  
% 2.93/0.99  fof(f51,plain,(
% 2.93/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f36])).
% 2.93/0.99  
% 2.93/0.99  fof(f8,axiom,(
% 2.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f21,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.99    inference(ennf_transformation,[],[f8])).
% 2.93/0.99  
% 2.93/0.99  fof(f54,plain,(
% 2.93/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.99    inference(cnf_transformation,[],[f21])).
% 2.93/0.99  
% 2.93/0.99  fof(f3,axiom,(
% 2.93/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f33,plain,(
% 2.93/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.93/0.99    inference(nnf_transformation,[],[f3])).
% 2.93/0.99  
% 2.93/0.99  fof(f34,plain,(
% 2.93/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.93/0.99    inference(flattening,[],[f33])).
% 2.93/0.99  
% 2.93/0.99  fof(f47,plain,(
% 2.93/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f34])).
% 2.93/0.99  
% 2.93/0.99  fof(f69,plain,(
% 2.93/0.99    k2_relset_1(sK1,sK2,sK3) != sK2),
% 2.93/0.99    inference(cnf_transformation,[],[f40])).
% 2.93/0.99  
% 2.93/0.99  fof(f11,axiom,(
% 2.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f24,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.99    inference(ennf_transformation,[],[f11])).
% 2.93/0.99  
% 2.93/0.99  fof(f57,plain,(
% 2.93/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.99    inference(cnf_transformation,[],[f24])).
% 2.93/0.99  
% 2.93/0.99  fof(f12,axiom,(
% 2.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f25,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.99    inference(ennf_transformation,[],[f12])).
% 2.93/0.99  
% 2.93/0.99  fof(f26,plain,(
% 2.93/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.99    inference(flattening,[],[f25])).
% 2.93/0.99  
% 2.93/0.99  fof(f37,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.99    inference(nnf_transformation,[],[f26])).
% 2.93/0.99  
% 2.93/0.99  fof(f58,plain,(
% 2.93/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.99    inference(cnf_transformation,[],[f37])).
% 2.93/0.99  
% 2.93/0.99  fof(f65,plain,(
% 2.93/0.99    v1_funct_2(sK3,sK1,sK2)),
% 2.93/0.99    inference(cnf_transformation,[],[f40])).
% 2.93/0.99  
% 2.93/0.99  fof(f10,axiom,(
% 2.93/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f23,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.99    inference(ennf_transformation,[],[f10])).
% 2.93/0.99  
% 2.93/0.99  fof(f56,plain,(
% 2.93/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.99    inference(cnf_transformation,[],[f23])).
% 2.93/0.99  
% 2.93/0.99  fof(f45,plain,(
% 2.93/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.93/0.99    inference(cnf_transformation,[],[f34])).
% 2.93/0.99  
% 2.93/0.99  fof(f71,plain,(
% 2.93/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.93/0.99    inference(equality_resolution,[],[f45])).
% 2.93/0.99  
% 2.93/0.99  fof(f2,axiom,(
% 2.93/0.99    v1_xboole_0(k1_xboole_0)),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f44,plain,(
% 2.93/0.99    v1_xboole_0(k1_xboole_0)),
% 2.93/0.99    inference(cnf_transformation,[],[f2])).
% 2.93/0.99  
% 2.93/0.99  fof(f5,axiom,(
% 2.93/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f17,plain,(
% 2.93/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.93/0.99    inference(ennf_transformation,[],[f5])).
% 2.93/0.99  
% 2.93/0.99  fof(f50,plain,(
% 2.93/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f17])).
% 2.93/0.99  
% 2.93/0.99  fof(f4,axiom,(
% 2.93/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f35,plain,(
% 2.93/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.93/0.99    inference(nnf_transformation,[],[f4])).
% 2.93/0.99  
% 2.93/0.99  fof(f49,plain,(
% 2.93/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f35])).
% 2.93/0.99  
% 2.93/0.99  fof(f7,axiom,(
% 2.93/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.93/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.99  
% 2.93/0.99  fof(f19,plain,(
% 2.93/0.99    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.93/0.99    inference(ennf_transformation,[],[f7])).
% 2.93/0.99  
% 2.93/0.99  fof(f20,plain,(
% 2.93/0.99    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.93/0.99    inference(flattening,[],[f19])).
% 2.93/0.99  
% 2.93/0.99  fof(f53,plain,(
% 2.93/0.99    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f20])).
% 2.93/0.99  
% 2.93/0.99  fof(f64,plain,(
% 2.93/0.99    v1_funct_1(sK3)),
% 2.93/0.99    inference(cnf_transformation,[],[f40])).
% 2.93/0.99  
% 2.93/0.99  fof(f67,plain,(
% 2.93/0.99    ( ! [X3] : (r2_hidden(sK4(X3),sK1) | ~r2_hidden(X3,sK2)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f40])).
% 2.93/0.99  
% 2.93/0.99  fof(f43,plain,(
% 2.93/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.93/0.99    inference(cnf_transformation,[],[f32])).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1,plain,
% 2.93/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.93/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2028,plain,
% 2.93/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.93/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_24,negated_conjecture,
% 2.93/0.99      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4(X0)) = X0 ),
% 2.93/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2020,plain,
% 2.93/0.99      ( k1_funct_1(sK3,sK4(X0)) = X0 | r2_hidden(X0,sK2) != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2455,plain,
% 2.93/0.99      ( k1_funct_1(sK3,sK4(sK0(sK2,X0))) = sK0(sK2,X0)
% 2.93/0.99      | r1_tarski(sK2,X0) = iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_2028,c_2020]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_26,negated_conjecture,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.93/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2018,plain,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_14,plain,
% 2.93/0.99      ( v5_relat_1(X0,X1)
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.93/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_11,plain,
% 2.93/0.99      ( ~ v5_relat_1(X0,X1)
% 2.93/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 2.93/0.99      | ~ v1_relat_1(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_408,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 2.93/0.99      | ~ v1_relat_1(X0) ),
% 2.93/0.99      inference(resolution,[status(thm)],[c_14,c_11]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_13,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | v1_relat_1(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_412,plain,
% 2.93/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.93/0.99      inference(global_propositional_subsumption,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_408,c_13]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_413,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.93/0.99      inference(renaming,[status(thm)],[c_412]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2016,plain,
% 2.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.93/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2714,plain,
% 2.93/0.99      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_2018,c_2016]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_4,plain,
% 2.93/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.93/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2026,plain,
% 2.93/0.99      ( X0 = X1
% 2.93/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.93/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2878,plain,
% 2.93/0.99      ( k2_relat_1(sK3) = sK2
% 2.93/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_2714,c_2026]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_31,plain,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_23,negated_conjecture,
% 2.93/0.99      ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 2.93/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2177,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/0.99      | r1_tarski(k2_relat_1(sK3),sK2) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_413]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2178,plain,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.93/0.99      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2177]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_16,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2204,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/0.99      | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2233,plain,
% 2.93/0.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2371,plain,
% 2.93/0.99      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.93/0.99      | ~ r1_tarski(sK2,k2_relat_1(sK3))
% 2.93/0.99      | sK2 = k2_relat_1(sK3) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_2233]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2372,plain,
% 2.93/0.99      ( sK2 = k2_relat_1(sK3)
% 2.93/0.99      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 2.93/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2371]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1528,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2195,plain,
% 2.93/0.99      ( k2_relset_1(sK1,sK2,sK3) != X0
% 2.93/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.93/0.99      | sK2 != X0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1528]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2654,plain,
% 2.93/0.99      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 2.93/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.93/0.99      | sK2 != k2_relat_1(sK3) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_2195]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3216,plain,
% 2.93/0.99      ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 2.93/0.99      inference(global_propositional_subsumption,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_2878,c_26,c_31,c_23,c_2178,c_2204,c_2372,c_2654]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3221,plain,
% 2.93/0.99      ( k1_funct_1(sK3,sK4(sK0(sK2,k2_relat_1(sK3)))) = sK0(sK2,k2_relat_1(sK3)) ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_2455,c_3216]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_22,plain,
% 2.93/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.93/0.99      | k1_xboole_0 = X2 ),
% 2.93/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_27,negated_conjecture,
% 2.93/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.93/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_904,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.93/0.99      | sK3 != X0
% 2.93/0.99      | sK2 != X2
% 2.93/0.99      | sK1 != X1
% 2.93/0.99      | k1_xboole_0 = X2 ),
% 2.93/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_905,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.93/0.99      | k1_xboole_0 = sK2 ),
% 2.93/0.99      inference(unflattening,[status(thm)],[c_904]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_907,plain,
% 2.93/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.93/0.99      inference(global_propositional_subsumption,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_905,c_26]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_15,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2022,plain,
% 2.93/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.93/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2751,plain,
% 2.93/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_2018,c_2022]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3119,plain,
% 2.93/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_907,c_2751]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_6,plain,
% 2.93/0.99      ( r1_tarski(X0,X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_87,plain,
% 2.93/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_91,plain,
% 2.93/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.93/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2186,plain,
% 2.93/0.99      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 2.93/0.99      | ~ r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3))
% 2.93/0.99      | k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1529,plain,
% 2.93/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.93/0.99      theory(equality) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2258,plain,
% 2.93/0.99      ( ~ r1_tarski(X0,X1)
% 2.93/0.99      | r1_tarski(sK2,k1_xboole_0)
% 2.93/0.99      | sK2 != X0
% 2.93/0.99      | k1_xboole_0 != X1 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2260,plain,
% 2.93/0.99      ( r1_tarski(sK2,k1_xboole_0)
% 2.93/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.93/0.99      | sK2 != k1_xboole_0
% 2.93/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_2258]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1527,plain,( X0 = X0 ),theory(equality) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2279,plain,
% 2.93/0.99      ( sK2 = sK2 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1527]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2325,plain,
% 2.93/0.99      ( r2_hidden(sK0(sK2,k2_relset_1(sK1,sK2,sK3)),sK2)
% 2.93/0.99      | r1_tarski(sK2,k2_relset_1(sK1,sK2,sK3)) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3,plain,
% 2.93/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_9,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.93/0.99      | ~ r2_hidden(X2,X0)
% 2.93/0.99      | ~ v1_xboole_0(X1) ),
% 2.93/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_7,plain,
% 2.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.93/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_220,plain,
% 2.93/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.93/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_221,plain,
% 2.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.93/0.99      inference(renaming,[status(thm)],[c_220]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_276,plain,
% 2.93/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.93/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_221]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_374,plain,
% 2.93/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 2.93/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_276]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_375,plain,
% 2.93/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 2.93/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2516,plain,
% 2.93/0.99      ( ~ r2_hidden(sK0(sK2,k2_relset_1(sK1,sK2,sK3)),sK2)
% 2.93/0.99      | ~ r1_tarski(sK2,k1_xboole_0) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_375]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2228,plain,
% 2.93/0.99      ( ~ r1_tarski(X0,X1)
% 2.93/0.99      | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 2.93/0.99      | k2_relset_1(sK1,sK2,sK3) != X0
% 2.93/0.99      | sK2 != X1 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2592,plain,
% 2.93/0.99      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 2.93/0.99      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.93/0.99      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 2.93/0.99      | sK2 != X0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_2228]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2838,plain,
% 2.93/0.99      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 2.93/0.99      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.93/0.99      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 2.93/0.99      | sK2 != sK2 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_2592]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3121,plain,
% 2.93/0.99      ( k1_relat_1(sK3) = sK1 ),
% 2.93/0.99      inference(global_propositional_subsumption,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_3119,c_26,c_23,c_87,c_91,c_2177,c_2186,c_2204,c_2260,
% 2.93/0.99                 c_2279,c_2325,c_2516,c_2838]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_12,plain,
% 2.93/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.93/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.93/0.99      | ~ v1_funct_1(X1)
% 2.93/0.99      | ~ v1_relat_1(X1) ),
% 2.93/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_28,negated_conjecture,
% 2.93/0.99      ( v1_funct_1(sK3) ),
% 2.93/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_389,plain,
% 2.93/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.93/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.93/0.99      | ~ v1_relat_1(X1)
% 2.93/0.99      | sK3 != X1 ),
% 2.93/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_390,plain,
% 2.93/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 2.93/0.99      | ~ v1_relat_1(sK3) ),
% 2.93/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_429,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | ~ r2_hidden(X3,k1_relat_1(sK3))
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
% 2.93/0.99      | sK3 != X0 ),
% 2.93/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_390]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_430,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.99      | ~ r2_hidden(X2,k1_relat_1(sK3))
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X2),k2_relat_1(sK3)) ),
% 2.93/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1523,plain,
% 2.93/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 2.93/0.99      | ~ sP0_iProver_split ),
% 2.93/0.99      inference(splitting,
% 2.93/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.93/0.99                [c_430]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2015,plain,
% 2.93/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.93/0.99      | sP0_iProver_split != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1525,plain,
% 2.93/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.93/0.99      inference(splitting,
% 2.93/0.99                [splitting(split),new_symbols(definition,[])],
% 2.93/0.99                [c_430]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1553,plain,
% 2.93/0.99      ( sP1_iProver_split = iProver_top
% 2.93/0.99      | sP0_iProver_split = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1557,plain,
% 2.93/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.93/0.99      | sP0_iProver_split != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1524,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.99      | ~ sP1_iProver_split ),
% 2.93/0.99      inference(splitting,
% 2.93/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.93/0.99                [c_430]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2161,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/0.99      | ~ sP1_iProver_split ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1524]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2162,plain,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.93/0.99      | sP1_iProver_split != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2340,plain,
% 2.93/0.99      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.93/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.93/0.99      inference(global_propositional_subsumption,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_2015,c_31,c_1553,c_1557,c_2162]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2341,plain,
% 2.93/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 2.93/0.99      inference(renaming,[status(thm)],[c_2340]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3126,plain,
% 2.93/0.99      ( r2_hidden(X0,sK1) != iProver_top
% 2.93/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 2.93/0.99      inference(demodulation,[status(thm)],[c_3121,c_2341]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3954,plain,
% 2.93/0.99      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) = iProver_top
% 2.93/0.99      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) != iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_3221,c_3126]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_25,negated_conjecture,
% 2.93/0.99      ( ~ r2_hidden(X0,sK2) | r2_hidden(sK4(X0),sK1) ),
% 2.93/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2914,plain,
% 2.93/0.99      ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
% 2.93/0.99      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2915,plain,
% 2.93/0.99      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
% 2.93/0.99      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2914]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2559,plain,
% 2.93/0.99      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
% 2.93/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2566,plain,
% 2.93/0.99      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) = iProver_top
% 2.93/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2559]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_0,plain,
% 2.93/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.93/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2560,plain,
% 2.93/0.99      ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3))
% 2.93/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2564,plain,
% 2.93/0.99      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) != iProver_top
% 2.93/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2560]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(contradiction,plain,
% 2.93/0.99      ( $false ),
% 2.93/0.99      inference(minisat,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_3954,c_2915,c_2654,c_2566,c_2564,c_2372,c_2204,c_2178,
% 2.93/0.99                 c_23,c_31,c_26]) ).
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/0.99  
% 2.93/0.99  ------                               Statistics
% 2.93/0.99  
% 2.93/0.99  ------ General
% 2.93/0.99  
% 2.93/0.99  abstr_ref_over_cycles:                  0
% 2.93/0.99  abstr_ref_under_cycles:                 0
% 2.93/0.99  gc_basic_clause_elim:                   0
% 2.93/0.99  forced_gc_time:                         0
% 2.93/0.99  parsing_time:                           0.017
% 2.93/0.99  unif_index_cands_time:                  0.
% 2.93/0.99  unif_index_add_time:                    0.
% 2.93/0.99  orderings_time:                         0.
% 2.93/0.99  out_proof_time:                         0.013
% 2.93/0.99  total_time:                             0.159
% 2.93/0.99  num_of_symbols:                         54
% 2.93/0.99  num_of_terms:                           2710
% 2.93/0.99  
% 2.93/0.99  ------ Preprocessing
% 2.93/0.99  
% 2.93/0.99  num_of_splits:                          2
% 2.93/0.99  num_of_split_atoms:                     2
% 2.93/0.99  num_of_reused_defs:                     0
% 2.93/0.99  num_eq_ax_congr_red:                    17
% 2.93/0.99  num_of_sem_filtered_clauses:            1
% 2.93/0.99  num_of_subtypes:                        0
% 2.93/0.99  monotx_restored_types:                  0
% 2.93/0.99  sat_num_of_epr_types:                   0
% 2.93/0.99  sat_num_of_non_cyclic_types:            0
% 2.93/0.99  sat_guarded_non_collapsed_types:        0
% 2.93/0.99  num_pure_diseq_elim:                    0
% 2.93/0.99  simp_replaced_by:                       0
% 2.93/0.99  res_preprocessed:                       114
% 2.93/0.99  prep_upred:                             0
% 2.93/0.99  prep_unflattend:                        69
% 2.93/0.99  smt_new_axioms:                         0
% 2.93/0.99  pred_elim_cands:                        3
% 2.93/0.99  pred_elim:                              5
% 2.93/0.99  pred_elim_cl:                           9
% 2.93/0.99  pred_elim_cycles:                       8
% 2.93/0.99  merged_defs:                            8
% 2.93/0.99  merged_defs_ncl:                        0
% 2.93/0.99  bin_hyper_res:                          9
% 2.93/0.99  prep_cycles:                            4
% 2.93/0.99  pred_elim_time:                         0.025
% 2.93/0.99  splitting_time:                         0.
% 2.93/0.99  sem_filter_time:                        0.
% 2.93/0.99  monotx_time:                            0.
% 2.93/0.99  subtype_inf_time:                       0.
% 2.93/0.99  
% 2.93/0.99  ------ Problem properties
% 2.93/0.99  
% 2.93/0.99  clauses:                                21
% 2.93/0.99  conjectures:                            4
% 2.93/0.99  epr:                                    5
% 2.93/0.99  horn:                                   17
% 2.93/0.99  ground:                                 6
% 2.93/0.99  unary:                                  3
% 2.93/0.99  binary:                                 13
% 2.93/0.99  lits:                                   45
% 2.93/0.99  lits_eq:                                12
% 2.93/0.99  fd_pure:                                0
% 2.93/0.99  fd_pseudo:                              0
% 2.93/0.99  fd_cond:                                0
% 2.93/0.99  fd_pseudo_cond:                         1
% 2.93/0.99  ac_symbols:                             0
% 2.93/0.99  
% 2.93/0.99  ------ Propositional Solver
% 2.93/0.99  
% 2.93/0.99  prop_solver_calls:                      28
% 2.93/0.99  prop_fast_solver_calls:                 819
% 2.93/0.99  smt_solver_calls:                       0
% 2.93/0.99  smt_fast_solver_calls:                  0
% 2.93/0.99  prop_num_of_clauses:                    1153
% 2.93/0.99  prop_preprocess_simplified:             4503
% 2.93/0.99  prop_fo_subsumed:                       9
% 2.93/0.99  prop_solver_time:                       0.
% 2.93/0.99  smt_solver_time:                        0.
% 2.93/0.99  smt_fast_solver_time:                   0.
% 2.93/0.99  prop_fast_solver_time:                  0.
% 2.93/0.99  prop_unsat_core_time:                   0.
% 2.93/0.99  
% 2.93/0.99  ------ QBF
% 2.93/0.99  
% 2.93/0.99  qbf_q_res:                              0
% 2.93/0.99  qbf_num_tautologies:                    0
% 2.93/0.99  qbf_prep_cycles:                        0
% 2.93/0.99  
% 2.93/0.99  ------ BMC1
% 2.93/0.99  
% 2.93/0.99  bmc1_current_bound:                     -1
% 2.93/0.99  bmc1_last_solved_bound:                 -1
% 2.93/0.99  bmc1_unsat_core_size:                   -1
% 2.93/0.99  bmc1_unsat_core_parents_size:           -1
% 2.93/0.99  bmc1_merge_next_fun:                    0
% 2.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.93/0.99  
% 2.93/0.99  ------ Instantiation
% 2.93/0.99  
% 2.93/0.99  inst_num_of_clauses:                    314
% 2.93/0.99  inst_num_in_passive:                    153
% 2.93/0.99  inst_num_in_active:                     136
% 2.93/0.99  inst_num_in_unprocessed:                25
% 2.93/0.99  inst_num_of_loops:                      210
% 2.93/0.99  inst_num_of_learning_restarts:          0
% 2.93/0.99  inst_num_moves_active_passive:          71
% 2.93/0.99  inst_lit_activity:                      0
% 2.93/0.99  inst_lit_activity_moves:                0
% 2.93/0.99  inst_num_tautologies:                   0
% 2.93/0.99  inst_num_prop_implied:                  0
% 2.93/0.99  inst_num_existing_simplified:           0
% 2.93/0.99  inst_num_eq_res_simplified:             0
% 2.93/0.99  inst_num_child_elim:                    0
% 2.93/0.99  inst_num_of_dismatching_blockings:      45
% 2.93/0.99  inst_num_of_non_proper_insts:           216
% 2.93/0.99  inst_num_of_duplicates:                 0
% 2.93/0.99  inst_inst_num_from_inst_to_res:         0
% 2.93/0.99  inst_dismatching_checking_time:         0.
% 2.93/0.99  
% 2.93/0.99  ------ Resolution
% 2.93/0.99  
% 2.93/0.99  res_num_of_clauses:                     0
% 2.93/0.99  res_num_in_passive:                     0
% 2.93/0.99  res_num_in_active:                      0
% 2.93/0.99  res_num_of_loops:                       118
% 2.93/0.99  res_forward_subset_subsumed:            15
% 2.93/0.99  res_backward_subset_subsumed:           0
% 2.93/0.99  res_forward_subsumed:                   0
% 2.93/0.99  res_backward_subsumed:                  0
% 2.93/0.99  res_forward_subsumption_resolution:     0
% 2.93/0.99  res_backward_subsumption_resolution:    0
% 2.93/0.99  res_clause_to_clause_subsumption:       217
% 2.93/0.99  res_orphan_elimination:                 0
% 2.93/0.99  res_tautology_del:                      40
% 2.93/0.99  res_num_eq_res_simplified:              0
% 2.93/0.99  res_num_sel_changes:                    0
% 2.93/0.99  res_moves_from_active_to_pass:          0
% 2.93/0.99  
% 2.93/0.99  ------ Superposition
% 2.93/0.99  
% 2.93/0.99  sup_time_total:                         0.
% 2.93/0.99  sup_time_generating:                    0.
% 2.93/0.99  sup_time_sim_full:                      0.
% 2.93/0.99  sup_time_sim_immed:                     0.
% 2.93/0.99  
% 2.93/0.99  sup_num_of_clauses:                     50
% 2.93/0.99  sup_num_in_active:                      37
% 2.93/0.99  sup_num_in_passive:                     13
% 2.93/0.99  sup_num_of_loops:                       41
% 2.93/0.99  sup_fw_superposition:                   28
% 2.93/0.99  sup_bw_superposition:                   12
% 2.93/0.99  sup_immediate_simplified:               1
% 2.93/0.99  sup_given_eliminated:                   0
% 2.93/0.99  comparisons_done:                       0
% 2.93/0.99  comparisons_avoided:                    0
% 2.93/0.99  
% 2.93/0.99  ------ Simplifications
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  sim_fw_subset_subsumed:                 0
% 2.93/0.99  sim_bw_subset_subsumed:                 1
% 2.93/0.99  sim_fw_subsumed:                        1
% 2.93/0.99  sim_bw_subsumed:                        0
% 2.93/0.99  sim_fw_subsumption_res:                 0
% 2.93/0.99  sim_bw_subsumption_res:                 0
% 2.93/0.99  sim_tautology_del:                      1
% 2.93/0.99  sim_eq_tautology_del:                   3
% 2.93/0.99  sim_eq_res_simp:                        0
% 2.93/0.99  sim_fw_demodulated:                     0
% 2.93/0.99  sim_bw_demodulated:                     4
% 2.93/0.99  sim_light_normalised:                   1
% 2.93/0.99  sim_joinable_taut:                      0
% 2.93/0.99  sim_joinable_simp:                      0
% 2.93/0.99  sim_ac_normalised:                      0
% 2.93/0.99  sim_smt_subsumption:                    0
% 2.93/0.99  
%------------------------------------------------------------------------------
