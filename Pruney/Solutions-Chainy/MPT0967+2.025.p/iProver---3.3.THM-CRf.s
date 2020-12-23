%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:42 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  148 (8781 expanded)
%              Number of clauses        :   97 (3078 expanded)
%              Number of leaves         :   12 (1636 expanded)
%              Depth                    :   27
%              Number of atoms          :  451 (46093 expanded)
%              Number of equality atoms :  197 (11236 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f33])).

fof(f58,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_904,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_905,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_907,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_25])).

cnf(c_1611,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1613,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2484,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1611,c_1613])).

cnf(c_2630,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_907,c_2484])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1612,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_9])).

cnf(c_1609,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_2438,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_1609])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1818,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1922,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_1923,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1944,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1945,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_2721,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_30,c_1923,c_1945])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1620,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1619,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3050,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1619])).

cnf(c_3171,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3050,c_1619])).

cnf(c_3189,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2721,c_3171])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1621,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3502,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3189,c_1621])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_301,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_302,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ r1_tarski(k2_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_1610,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_2485,plain,
    ( k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1610,c_1613])).

cnf(c_2906,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2485,c_30,c_1923,c_1945])).

cnf(c_2907,plain,
    ( k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2906])).

cnf(c_3701,plain,
    ( k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_2907])).

cnf(c_4010,plain,
    ( k1_relset_1(k1_relat_1(sK4),sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1612,c_3701])).

cnf(c_4014,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2630,c_4010])).

cnf(c_31,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2829,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2630,c_1610])).

cnf(c_3598,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2829,c_30,c_1923,c_1945])).

cnf(c_3599,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3598])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_144,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_27])).

cnf(c_145,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_286,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_287,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | ~ r1_tarski(k2_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_954,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != sK1
    | sK3 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_287])).

cnf(c_955,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_965,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_955,c_324])).

cnf(c_1599,plain,
    ( k1_relat_1(sK4) != sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_969,plain,
    ( k1_relat_1(sK4) != sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_2176,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | k1_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1599,c_30,c_969,c_1923,c_1945])).

cnf(c_2177,plain,
    ( k1_relat_1(sK4) != sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2176])).

cnf(c_2828,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2630,c_2177])).

cnf(c_3609,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3599,c_2828])).

cnf(c_3961,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_3609])).

cnf(c_4104,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4014,c_31,c_3961])).

cnf(c_4120,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_4104,c_2484])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4127,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4104,c_23])).

cnf(c_4128,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4127])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_855,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_856,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_1604,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_4123,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4104,c_1604])).

cnf(c_4135,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4123,c_4128])).

cnf(c_4136,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4135])).

cnf(c_4125,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4104,c_1611])).

cnf(c_4132,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4125,c_4128])).

cnf(c_4139,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4136,c_4132])).

cnf(c_4147,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4120,c_4128,c_4139])).

cnf(c_4273,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4147,c_1610])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_74,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4111,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4104,c_3502])).

cnf(c_4710,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4273,c_30,c_74,c_1923,c_1945,c_4111])).

cnf(c_939,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK2 != sK3
    | sK1 != sK1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_26])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK2 != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_939])).

cnf(c_1598,plain,
    ( sK2 != sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_4122,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4104,c_1598])).

cnf(c_4141,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4122,c_4128])).

cnf(c_4198,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4128,c_2177])).

cnf(c_4699,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4141,c_4147,c_4198])).

cnf(c_4718,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4710,c_4699])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.44/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/1.00  
% 2.44/1.00  ------  iProver source info
% 2.44/1.00  
% 2.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/1.00  git: non_committed_changes: false
% 2.44/1.00  git: last_make_outside_of_git: false
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     num_symb
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       true
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  ------ Parsing...
% 2.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.00  ------ Proving...
% 2.44/1.00  ------ Problem Properties 
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  clauses                                 26
% 2.44/1.00  conjectures                             3
% 2.44/1.00  EPR                                     6
% 2.44/1.00  Horn                                    21
% 2.44/1.00  unary                                   5
% 2.44/1.00  binary                                  6
% 2.44/1.00  lits                                    68
% 2.44/1.00  lits eq                                 26
% 2.44/1.00  fd_pure                                 0
% 2.44/1.00  fd_pseudo                               0
% 2.44/1.00  fd_cond                                 1
% 2.44/1.00  fd_pseudo_cond                          1
% 2.44/1.00  AC symbols                              0
% 2.44/1.00  
% 2.44/1.00  ------ Schedule dynamic 5 is on 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  Current options:
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     none
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       false
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ Proving...
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS status Theorem for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00   Resolution empty clause
% 2.44/1.00  
% 2.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  fof(f9,axiom,(
% 2.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f19,plain,(
% 2.44/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.00    inference(ennf_transformation,[],[f9])).
% 2.44/1.00  
% 2.44/1.00  fof(f20,plain,(
% 2.44/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.00    inference(flattening,[],[f19])).
% 2.44/1.00  
% 2.44/1.00  fof(f32,plain,(
% 2.44/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.00    inference(nnf_transformation,[],[f20])).
% 2.44/1.00  
% 2.44/1.00  fof(f48,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.00    inference(cnf_transformation,[],[f32])).
% 2.44/1.00  
% 2.44/1.00  fof(f11,conjecture,(
% 2.44/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f12,negated_conjecture,(
% 2.44/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.44/1.00    inference(negated_conjecture,[],[f11])).
% 2.44/1.00  
% 2.44/1.00  fof(f23,plain,(
% 2.44/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.44/1.00    inference(ennf_transformation,[],[f12])).
% 2.44/1.00  
% 2.44/1.00  fof(f24,plain,(
% 2.44/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.44/1.00    inference(flattening,[],[f23])).
% 2.44/1.00  
% 2.44/1.00  fof(f33,plain,(
% 2.44/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f34,plain,(
% 2.44/1.00    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f33])).
% 2.44/1.00  
% 2.44/1.00  fof(f58,plain,(
% 2.44/1.00    v1_funct_2(sK4,sK1,sK2)),
% 2.44/1.00    inference(cnf_transformation,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f59,plain,(
% 2.44/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.44/1.00    inference(cnf_transformation,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f8,axiom,(
% 2.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f18,plain,(
% 2.44/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.00    inference(ennf_transformation,[],[f8])).
% 2.44/1.00  
% 2.44/1.00  fof(f47,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.00    inference(cnf_transformation,[],[f18])).
% 2.44/1.00  
% 2.44/1.00  fof(f60,plain,(
% 2.44/1.00    r1_tarski(sK2,sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f7,axiom,(
% 2.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f13,plain,(
% 2.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.44/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.44/1.00  
% 2.44/1.00  fof(f17,plain,(
% 2.44/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/1.00    inference(ennf_transformation,[],[f13])).
% 2.44/1.00  
% 2.44/1.00  fof(f46,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.00    inference(cnf_transformation,[],[f17])).
% 2.44/1.00  
% 2.44/1.00  fof(f5,axiom,(
% 2.44/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f16,plain,(
% 2.44/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.44/1.00    inference(ennf_transformation,[],[f5])).
% 2.44/1.00  
% 2.44/1.00  fof(f31,plain,(
% 2.44/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.44/1.00    inference(nnf_transformation,[],[f16])).
% 2.44/1.00  
% 2.44/1.00  fof(f43,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f31])).
% 2.44/1.00  
% 2.44/1.00  fof(f4,axiom,(
% 2.44/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f15,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f4])).
% 2.44/1.00  
% 2.44/1.00  fof(f42,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f15])).
% 2.44/1.00  
% 2.44/1.00  fof(f6,axiom,(
% 2.44/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f45,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.44/1.00    inference(cnf_transformation,[],[f6])).
% 2.44/1.00  
% 2.44/1.00  fof(f1,axiom,(
% 2.44/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f14,plain,(
% 2.44/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f1])).
% 2.44/1.00  
% 2.44/1.00  fof(f25,plain,(
% 2.44/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/1.00    inference(nnf_transformation,[],[f14])).
% 2.44/1.00  
% 2.44/1.00  fof(f26,plain,(
% 2.44/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/1.00    inference(rectify,[],[f25])).
% 2.44/1.00  
% 2.44/1.00  fof(f27,plain,(
% 2.44/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f28,plain,(
% 2.44/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.44/1.00  
% 2.44/1.00  fof(f36,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f28])).
% 2.44/1.00  
% 2.44/1.00  fof(f35,plain,(
% 2.44/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f28])).
% 2.44/1.00  
% 2.44/1.00  fof(f37,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f28])).
% 2.44/1.00  
% 2.44/1.00  fof(f10,axiom,(
% 2.44/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f21,plain,(
% 2.44/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.44/1.00    inference(ennf_transformation,[],[f10])).
% 2.44/1.00  
% 2.44/1.00  fof(f22,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.44/1.00    inference(flattening,[],[f21])).
% 2.44/1.00  
% 2.44/1.00  fof(f56,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f22])).
% 2.44/1.00  
% 2.44/1.00  fof(f57,plain,(
% 2.44/1.00    v1_funct_1(sK4)),
% 2.44/1.00    inference(cnf_transformation,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f62,plain,(
% 2.44/1.00    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 2.44/1.00    inference(cnf_transformation,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f55,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f22])).
% 2.44/1.00  
% 2.44/1.00  fof(f61,plain,(
% 2.44/1.00    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 2.44/1.00    inference(cnf_transformation,[],[f34])).
% 2.44/1.00  
% 2.44/1.00  fof(f49,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/1.00    inference(cnf_transformation,[],[f32])).
% 2.44/1.00  
% 2.44/1.00  fof(f69,plain,(
% 2.44/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.44/1.00    inference(equality_resolution,[],[f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f3,axiom,(
% 2.44/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f41,plain,(
% 2.44/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f3])).
% 2.44/1.00  
% 2.44/1.00  cnf(c_18,plain,
% 2.44/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.44/1.00      | k1_xboole_0 = X2 ),
% 2.44/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_26,negated_conjecture,
% 2.44/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.44/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_904,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.44/1.00      | sK2 != X2
% 2.44/1.00      | sK1 != X1
% 2.44/1.00      | sK4 != X0
% 2.44/1.00      | k1_xboole_0 = X2 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_905,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.44/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.44/1.00      | k1_xboole_0 = sK2 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_904]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_25,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_907,plain,
% 2.44/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_905,c_25]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1611,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_12,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1613,plain,
% 2.44/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.44/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2484,plain,
% 2.44/1.00      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1611,c_1613]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2630,plain,
% 2.44/1.00      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_907,c_2484]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_24,negated_conjecture,
% 2.44/1.00      ( r1_tarski(sK2,sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1612,plain,
% 2.44/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_11,plain,
% 2.44/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_9,plain,
% 2.44/1.00      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_324,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 2.44/1.00      | ~ v1_relat_1(X0) ),
% 2.44/1.00      inference(resolution,[status(thm)],[c_11,c_9]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1609,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 2.44/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2438,plain,
% 2.44/1.00      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top
% 2.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1611,c_1609]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_30,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_7,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1818,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/1.00      | v1_relat_1(X0)
% 2.44/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1922,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.44/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.44/1.00      | v1_relat_1(sK4) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1818]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1923,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.44/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.44/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_10,plain,
% 2.44/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1944,plain,
% 2.44/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1945,plain,
% 2.44/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2721,plain,
% 2.44/1.00      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2438,c_30,c_1923,c_1945]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1,plain,
% 2.44/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1620,plain,
% 2.44/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2,plain,
% 2.44/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.44/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1619,plain,
% 2.44/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.44/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.44/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3050,plain,
% 2.44/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.44/1.00      | r1_tarski(X0,X2) != iProver_top
% 2.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1620,c_1619]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3171,plain,
% 2.44/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.44/1.00      | r1_tarski(X0,X3) != iProver_top
% 2.44/1.00      | r1_tarski(X3,X2) != iProver_top
% 2.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3050,c_1619]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3189,plain,
% 2.44/1.00      ( r2_hidden(sK0(k2_relat_1(sK4),X0),X1) = iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 2.44/1.00      | r1_tarski(sK2,X1) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2721,c_3171]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_0,plain,
% 2.44/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1621,plain,
% 2.44/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3502,plain,
% 2.44/1.00      ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 2.44/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3189,c_1621]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_19,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.44/1.00      | ~ v1_funct_1(X0)
% 2.44/1.00      | ~ v1_relat_1(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_27,negated_conjecture,
% 2.44/1.00      ( v1_funct_1(sK4) ),
% 2.44/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_301,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.44/1.00      | ~ v1_relat_1(X0)
% 2.44/1.00      | sK4 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_302,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(sK4),X0)
% 2.44/1.00      | ~ v1_relat_1(sK4) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_301]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1610,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 2.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2485,plain,
% 2.44/1.00      ( k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4)
% 2.44/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 2.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1610,c_1613]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2906,plain,
% 2.44/1.00      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 2.44/1.00      | k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2485,c_30,c_1923,c_1945]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2907,plain,
% 2.44/1.00      ( k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4)
% 2.44/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_2906]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3701,plain,
% 2.44/1.00      ( k1_relset_1(k1_relat_1(sK4),X0,sK4) = k1_relat_1(sK4)
% 2.44/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3502,c_2907]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4010,plain,
% 2.44/1.00      ( k1_relset_1(k1_relat_1(sK4),sK3,sK4) = k1_relat_1(sK4) ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1612,c_3701]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4014,plain,
% 2.44/1.00      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) | sK2 = k1_xboole_0 ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2630,c_4010]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_31,plain,
% 2.44/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2829,plain,
% 2.44/1.00      ( sK2 = k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 2.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2630,c_1610]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3598,plain,
% 2.44/1.00      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 2.44/1.00      | sK2 = k1_xboole_0 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2829,c_30,c_1923,c_1945]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3599,plain,
% 2.44/1.00      ( sK2 = k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_3598]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_22,negated_conjecture,
% 2.44/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 2.44/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.44/1.00      | ~ v1_funct_1(sK4) ),
% 2.44/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_144,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.44/1.00      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 2.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_22,c_27]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_145,negated_conjecture,
% 2.44/1.00      ( ~ v1_funct_2(sK4,sK1,sK3)
% 2.44/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_144]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_20,plain,
% 2.44/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.44/1.00      | ~ v1_funct_1(X0)
% 2.44/1.00      | ~ v1_relat_1(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_286,plain,
% 2.44/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.44/1.00      | ~ v1_relat_1(X0)
% 2.44/1.00      | sK4 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_287,plain,
% 2.44/1.00      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(sK4),X0)
% 2.44/1.00      | ~ v1_relat_1(sK4) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_954,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(sK4),X0)
% 2.44/1.00      | ~ v1_relat_1(sK4)
% 2.44/1.00      | k1_relat_1(sK4) != sK1
% 2.44/1.00      | sK3 != X0
% 2.44/1.00      | sK4 != sK4 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_145,c_287]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_955,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.44/1.00      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 2.44/1.00      | ~ v1_relat_1(sK4)
% 2.44/1.00      | k1_relat_1(sK4) != sK1 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_954]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_965,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.44/1.00      | ~ v1_relat_1(sK4)
% 2.44/1.00      | k1_relat_1(sK4) != sK1 ),
% 2.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_955,c_324]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1599,plain,
% 2.44/1.00      ( k1_relat_1(sK4) != sK1
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 2.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_969,plain,
% 2.44/1.00      ( k1_relat_1(sK4) != sK1
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 2.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2176,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 2.44/1.00      | k1_relat_1(sK4) != sK1 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_1599,c_30,c_969,c_1923,c_1945]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2177,plain,
% 2.44/1.00      ( k1_relat_1(sK4) != sK1
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_2176]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2828,plain,
% 2.44/1.00      ( sK2 = k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2630,c_2177]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3609,plain,
% 2.44/1.00      ( sK2 = k1_xboole_0 | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3599,c_2828]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3961,plain,
% 2.44/1.00      ( sK2 = k1_xboole_0 | r1_tarski(sK2,sK3) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3502,c_3609]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4104,plain,
% 2.44/1.00      ( sK2 = k1_xboole_0 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4014,c_31,c_3961]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4120,plain,
% 2.44/1.00      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4104,c_2484]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_23,negated_conjecture,
% 2.44/1.00      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 2.44/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4127,plain,
% 2.44/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4104,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4128,plain,
% 2.44/1.00      ( sK1 = k1_xboole_0 ),
% 2.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_4127]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_17,plain,
% 2.44/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.44/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.44/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_855,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.44/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.44/1.00      | sK2 != X1
% 2.44/1.00      | sK1 != k1_xboole_0
% 2.44/1.00      | sK4 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_856,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.44/1.00      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.44/1.00      | sK1 != k1_xboole_0 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_855]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1604,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 2.44/1.00      | sK1 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4123,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.44/1.00      | sK1 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4104,c_1604]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4135,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.44/1.00      | k1_xboole_0 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_4123,c_4128]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4136,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_4135]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4125,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4104,c_1611]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4132,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_4125,c_4128]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4139,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 2.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4136,c_4132]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4147,plain,
% 2.44/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_4120,c_4128,c_4139]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4273,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 2.44/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4147,c_1610]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_6,plain,
% 2.44/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_74,plain,
% 2.44/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4111,plain,
% 2.44/1.00      ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 2.44/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4104,c_3502]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4710,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4273,c_30,c_74,c_1923,c_1945,c_4111]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_939,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.44/1.00      | sK2 != sK3
% 2.44/1.00      | sK1 != sK1
% 2.44/1.00      | sK4 != sK4 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_145,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1044,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | sK2 != sK3 ),
% 2.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_939]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1598,plain,
% 2.44/1.00      ( sK2 != sK3
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4122,plain,
% 2.44/1.00      ( sK3 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4104,c_1598]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4141,plain,
% 2.44/1.00      ( sK3 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_4122,c_4128]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4198,plain,
% 2.44/1.00      ( k1_relat_1(sK4) != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_4128,c_2177]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4699,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4141,c_4147,c_4198]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4718,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_4710,c_4699]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.009
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.009
% 2.44/1.00  total_time:                             0.162
% 2.44/1.00  num_of_symbols:                         50
% 2.44/1.00  num_of_terms:                           2833
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          1
% 2.44/1.00  num_of_split_atoms:                     1
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    15
% 2.44/1.00  num_of_sem_filtered_clauses:            1
% 2.44/1.00  num_of_subtypes:                        0
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        0
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       126
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        60
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        4
% 2.44/1.00  pred_elim:                              3
% 2.44/1.00  pred_elim_cl:                           1
% 2.44/1.00  pred_elim_cycles:                       6
% 2.44/1.00  merged_defs:                            0
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          0
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.02
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                26
% 2.44/1.00  conjectures:                            3
% 2.44/1.00  epr:                                    6
% 2.44/1.00  horn:                                   21
% 2.44/1.00  ground:                                 13
% 2.44/1.00  unary:                                  5
% 2.44/1.00  binary:                                 6
% 2.44/1.00  lits:                                   68
% 2.44/1.00  lits_eq:                                26
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                1
% 2.44/1.00  fd_pseudo_cond:                         1
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      29
% 2.44/1.00  prop_fast_solver_calls:                 988
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    1365
% 2.44/1.00  prop_preprocess_simplified:             4528
% 2.44/1.00  prop_fo_subsumed:                       21
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    417
% 2.44/1.00  inst_num_in_passive:                    64
% 2.44/1.00  inst_num_in_active:                     263
% 2.44/1.00  inst_num_in_unprocessed:                90
% 2.44/1.00  inst_num_of_loops:                      330
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          63
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      170
% 2.44/1.00  inst_num_of_non_proper_insts:           500
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       130
% 2.44/1.00  res_forward_subset_subsumed:            48
% 2.44/1.00  res_backward_subset_subsumed:           0
% 2.44/1.00  res_forward_subsumed:                   0
% 2.44/1.00  res_backward_subsumed:                  0
% 2.44/1.00  res_forward_subsumption_resolution:     2
% 2.44/1.00  res_backward_subsumption_resolution:    0
% 2.44/1.00  res_clause_to_clause_subsumption:       361
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      43
% 2.44/1.00  res_num_eq_res_simplified:              1
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     34
% 2.44/1.00  sup_num_in_active:                      24
% 2.44/1.00  sup_num_in_passive:                     10
% 2.44/1.00  sup_num_of_loops:                       65
% 2.44/1.00  sup_fw_superposition:                   40
% 2.44/1.00  sup_bw_superposition:                   41
% 2.44/1.00  sup_immediate_simplified:               31
% 2.44/1.00  sup_given_eliminated:                   2
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    10
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 16
% 2.44/1.00  sim_bw_subset_subsumed:                 11
% 2.44/1.00  sim_fw_subsumed:                        7
% 2.44/1.00  sim_bw_subsumed:                        4
% 2.44/1.00  sim_fw_subsumption_res:                 1
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      4
% 2.44/1.00  sim_eq_tautology_del:                   11
% 2.44/1.00  sim_eq_res_simp:                        5
% 2.44/1.00  sim_fw_demodulated:                     0
% 2.44/1.00  sim_bw_demodulated:                     37
% 2.44/1.00  sim_light_normalised:                   9
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
