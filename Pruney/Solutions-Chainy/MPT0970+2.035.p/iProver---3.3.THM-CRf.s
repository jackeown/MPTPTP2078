%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:52 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  130 (1007 expanded)
%              Number of clauses        :   81 ( 349 expanded)
%              Number of leaves         :   15 ( 238 expanded)
%              Depth                    :   24
%              Number of atoms          :  373 (4395 expanded)
%              Number of equality atoms :  180 (1453 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK4(X3)) = X3
        & r2_hidden(sK4(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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

fof(f32,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    & ! [X3] :
        ( ( k1_funct_1(sK3,sK4(X3)) = X3
          & r2_hidden(sK4(X3),sK1) )
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30])).

fof(f52,plain,(
    ! [X3] :
      ( r2_hidden(sK4(X3),sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f22])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,sK4(X3)) = X3
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_748,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_740,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_1611,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_740])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_742,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4(X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_339,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_341,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_19])).

cnf(c_741,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_745,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1169,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_741,c_745])).

cnf(c_1351,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_341,c_1169])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_743,plain,
    ( k1_funct_1(sK3,sK4(X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1244,plain,
    ( k1_funct_1(sK3,sK4(sK0(X0,sK2))) = sK0(X0,sK2)
    | sK2 = X0
    | r2_hidden(sK0(X0,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_743])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_744,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1059,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_741,c_744])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_746,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1267,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_746])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1544,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1267,c_24])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_747,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1639,plain,
    ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_747])).

cnf(c_2148,plain,
    ( k1_funct_1(sK3,sK4(sK0(k2_relat_1(sK3),sK2))) = sK0(k2_relat_1(sK3),sK2)
    | k2_relat_1(sK3) = sK2
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1639])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1266,plain,
    ( k2_relat_1(sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_1059,c_16])).

cnf(c_2202,plain,
    ( k1_funct_1(sK3,sK4(sK0(k2_relat_1(sK3),sK2))) = sK0(k2_relat_1(sK3),sK2)
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2148,c_1266])).

cnf(c_2208,plain,
    ( k1_funct_1(sK3,sK4(sK0(k2_relat_1(sK3),sK2))) = sK0(k2_relat_1(sK3),sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2202,c_743])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_255,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_256,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_256])).

cnf(c_275,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X2),k2_relat_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_455,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_275])).

cnf(c_739,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_457,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_275])).

cnf(c_483,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_487,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_456,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_275])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_859,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_1048,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_24,c_483,c_487,c_859])).

cnf(c_1049,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1048])).

cnf(c_2209,plain,
    ( r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4(sK0(k2_relat_1(sK3),sK2)),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2208,c_1049])).

cnf(c_2317,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4(sK0(k2_relat_1(sK3),sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_2209])).

cnf(c_874,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_460,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_864,plain,
    ( k2_relset_1(sK1,sK2,sK3) != X0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_944,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1007,plain,
    ( ~ r2_hidden(sK0(X0,sK2),X0)
    | ~ r2_hidden(sK0(X0,sK2),sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1506,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3))
    | ~ r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2)
    | sK2 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1507,plain,
    ( sK2 = k2_relat_1(sK3)
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_2146,plain,
    ( k2_relat_1(sK3) = X0
    | r2_hidden(sK0(k2_relat_1(sK3),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK3),X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_1639])).

cnf(c_2388,plain,
    ( k2_relat_1(sK3) = sK2
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2146])).

cnf(c_2390,plain,
    ( k2_relat_1(sK3) = sK2
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2388])).

cnf(c_2686,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK4(sK0(k2_relat_1(sK3),sK2)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2317,c_19,c_16,c_874,c_944,c_1266,c_1507,c_2390])).

cnf(c_2692,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_742,c_2686])).

cnf(c_2764,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_1266,c_2390])).

cnf(c_2773,plain,
    ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2764,c_1639])).

cnf(c_246,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_3546,plain,
    ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2773,c_246])).

cnf(c_3556,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1611,c_3546])).

cnf(c_1013,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1515,plain,
    ( k2_relat_1(sK3) != X0
    | sK2 != X0
    | sK2 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_1516,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK2 = k2_relat_1(sK3)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3556,c_2692,c_2390,c_1516,c_1266,c_944,c_874,c_16,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.26  % Computer   : n020.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 12:49:07 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  % Running in FOF mode
% 2.33/0.85  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.85  
% 2.33/0.85  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.85  
% 2.33/0.85  ------  iProver source info
% 2.33/0.85  
% 2.33/0.85  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.85  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.85  git: non_committed_changes: false
% 2.33/0.85  git: last_make_outside_of_git: false
% 2.33/0.85  
% 2.33/0.85  ------ 
% 2.33/0.85  
% 2.33/0.85  ------ Input Options
% 2.33/0.85  
% 2.33/0.85  --out_options                           all
% 2.33/0.85  --tptp_safe_out                         true
% 2.33/0.85  --problem_path                          ""
% 2.33/0.85  --include_path                          ""
% 2.33/0.85  --clausifier                            res/vclausify_rel
% 2.33/0.85  --clausifier_options                    --mode clausify
% 2.33/0.85  --stdin                                 false
% 2.33/0.85  --stats_out                             all
% 2.33/0.85  
% 2.33/0.85  ------ General Options
% 2.33/0.85  
% 2.33/0.85  --fof                                   false
% 2.33/0.85  --time_out_real                         305.
% 2.33/0.85  --time_out_virtual                      -1.
% 2.33/0.85  --symbol_type_check                     false
% 2.33/0.85  --clausify_out                          false
% 2.33/0.85  --sig_cnt_out                           false
% 2.33/0.85  --trig_cnt_out                          false
% 2.33/0.85  --trig_cnt_out_tolerance                1.
% 2.33/0.85  --trig_cnt_out_sk_spl                   false
% 2.33/0.85  --abstr_cl_out                          false
% 2.33/0.85  
% 2.33/0.85  ------ Global Options
% 2.33/0.85  
% 2.33/0.85  --schedule                              default
% 2.33/0.85  --add_important_lit                     false
% 2.33/0.85  --prop_solver_per_cl                    1000
% 2.33/0.85  --min_unsat_core                        false
% 2.33/0.85  --soft_assumptions                      false
% 2.33/0.85  --soft_lemma_size                       3
% 2.33/0.85  --prop_impl_unit_size                   0
% 2.33/0.85  --prop_impl_unit                        []
% 2.33/0.85  --share_sel_clauses                     true
% 2.33/0.85  --reset_solvers                         false
% 2.33/0.85  --bc_imp_inh                            [conj_cone]
% 2.33/0.85  --conj_cone_tolerance                   3.
% 2.33/0.85  --extra_neg_conj                        none
% 2.33/0.85  --large_theory_mode                     true
% 2.33/0.85  --prolific_symb_bound                   200
% 2.33/0.85  --lt_threshold                          2000
% 2.33/0.85  --clause_weak_htbl                      true
% 2.33/0.85  --gc_record_bc_elim                     false
% 2.33/0.85  
% 2.33/0.85  ------ Preprocessing Options
% 2.33/0.85  
% 2.33/0.85  --preprocessing_flag                    true
% 2.33/0.85  --time_out_prep_mult                    0.1
% 2.33/0.85  --splitting_mode                        input
% 2.33/0.85  --splitting_grd                         true
% 2.33/0.85  --splitting_cvd                         false
% 2.33/0.85  --splitting_cvd_svl                     false
% 2.33/0.85  --splitting_nvd                         32
% 2.33/0.85  --sub_typing                            true
% 2.33/0.85  --prep_gs_sim                           true
% 2.33/0.85  --prep_unflatten                        true
% 2.33/0.85  --prep_res_sim                          true
% 2.33/0.85  --prep_upred                            true
% 2.33/0.85  --prep_sem_filter                       exhaustive
% 2.33/0.85  --prep_sem_filter_out                   false
% 2.33/0.85  --pred_elim                             true
% 2.33/0.85  --res_sim_input                         true
% 2.33/0.85  --eq_ax_congr_red                       true
% 2.33/0.85  --pure_diseq_elim                       true
% 2.33/0.85  --brand_transform                       false
% 2.33/0.85  --non_eq_to_eq                          false
% 2.33/0.85  --prep_def_merge                        true
% 2.33/0.85  --prep_def_merge_prop_impl              false
% 2.33/0.85  --prep_def_merge_mbd                    true
% 2.33/0.85  --prep_def_merge_tr_red                 false
% 2.33/0.85  --prep_def_merge_tr_cl                  false
% 2.33/0.85  --smt_preprocessing                     true
% 2.33/0.85  --smt_ac_axioms                         fast
% 2.33/0.85  --preprocessed_out                      false
% 2.33/0.85  --preprocessed_stats                    false
% 2.33/0.85  
% 2.33/0.85  ------ Abstraction refinement Options
% 2.33/0.85  
% 2.33/0.85  --abstr_ref                             []
% 2.33/0.85  --abstr_ref_prep                        false
% 2.33/0.85  --abstr_ref_until_sat                   false
% 2.33/0.85  --abstr_ref_sig_restrict                funpre
% 2.33/0.85  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.85  --abstr_ref_under                       []
% 2.33/0.85  
% 2.33/0.85  ------ SAT Options
% 2.33/0.85  
% 2.33/0.85  --sat_mode                              false
% 2.33/0.85  --sat_fm_restart_options                ""
% 2.33/0.85  --sat_gr_def                            false
% 2.33/0.85  --sat_epr_types                         true
% 2.33/0.85  --sat_non_cyclic_types                  false
% 2.33/0.85  --sat_finite_models                     false
% 2.33/0.85  --sat_fm_lemmas                         false
% 2.33/0.85  --sat_fm_prep                           false
% 2.33/0.85  --sat_fm_uc_incr                        true
% 2.33/0.85  --sat_out_model                         small
% 2.33/0.85  --sat_out_clauses                       false
% 2.33/0.85  
% 2.33/0.85  ------ QBF Options
% 2.33/0.85  
% 2.33/0.85  --qbf_mode                              false
% 2.33/0.85  --qbf_elim_univ                         false
% 2.33/0.85  --qbf_dom_inst                          none
% 2.33/0.85  --qbf_dom_pre_inst                      false
% 2.33/0.85  --qbf_sk_in                             false
% 2.33/0.85  --qbf_pred_elim                         true
% 2.33/0.85  --qbf_split                             512
% 2.33/0.85  
% 2.33/0.85  ------ BMC1 Options
% 2.33/0.85  
% 2.33/0.85  --bmc1_incremental                      false
% 2.33/0.85  --bmc1_axioms                           reachable_all
% 2.33/0.85  --bmc1_min_bound                        0
% 2.33/0.85  --bmc1_max_bound                        -1
% 2.33/0.85  --bmc1_max_bound_default                -1
% 2.33/0.85  --bmc1_symbol_reachability              true
% 2.33/0.85  --bmc1_property_lemmas                  false
% 2.33/0.85  --bmc1_k_induction                      false
% 2.33/0.85  --bmc1_non_equiv_states                 false
% 2.33/0.85  --bmc1_deadlock                         false
% 2.33/0.85  --bmc1_ucm                              false
% 2.33/0.85  --bmc1_add_unsat_core                   none
% 2.33/0.85  --bmc1_unsat_core_children              false
% 2.33/0.85  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.85  --bmc1_out_stat                         full
% 2.33/0.85  --bmc1_ground_init                      false
% 2.33/0.85  --bmc1_pre_inst_next_state              false
% 2.33/0.85  --bmc1_pre_inst_state                   false
% 2.33/0.85  --bmc1_pre_inst_reach_state             false
% 2.33/0.85  --bmc1_out_unsat_core                   false
% 2.33/0.85  --bmc1_aig_witness_out                  false
% 2.33/0.85  --bmc1_verbose                          false
% 2.33/0.85  --bmc1_dump_clauses_tptp                false
% 2.33/0.85  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.85  --bmc1_dump_file                        -
% 2.33/0.85  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.85  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.85  --bmc1_ucm_extend_mode                  1
% 2.33/0.85  --bmc1_ucm_init_mode                    2
% 2.33/0.85  --bmc1_ucm_cone_mode                    none
% 2.33/0.85  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.85  --bmc1_ucm_relax_model                  4
% 2.33/0.85  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.85  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.85  --bmc1_ucm_layered_model                none
% 2.33/0.85  --bmc1_ucm_max_lemma_size               10
% 2.33/0.85  
% 2.33/0.85  ------ AIG Options
% 2.33/0.85  
% 2.33/0.85  --aig_mode                              false
% 2.33/0.85  
% 2.33/0.85  ------ Instantiation Options
% 2.33/0.85  
% 2.33/0.85  --instantiation_flag                    true
% 2.33/0.85  --inst_sos_flag                         false
% 2.33/0.85  --inst_sos_phase                        true
% 2.33/0.85  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.85  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.85  --inst_lit_sel_side                     num_symb
% 2.33/0.85  --inst_solver_per_active                1400
% 2.33/0.85  --inst_solver_calls_frac                1.
% 2.33/0.85  --inst_passive_queue_type               priority_queues
% 2.33/0.85  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.85  --inst_passive_queues_freq              [25;2]
% 2.33/0.85  --inst_dismatching                      true
% 2.33/0.85  --inst_eager_unprocessed_to_passive     true
% 2.33/0.85  --inst_prop_sim_given                   true
% 2.33/0.85  --inst_prop_sim_new                     false
% 2.33/0.85  --inst_subs_new                         false
% 2.33/0.85  --inst_eq_res_simp                      false
% 2.33/0.85  --inst_subs_given                       false
% 2.33/0.85  --inst_orphan_elimination               true
% 2.33/0.85  --inst_learning_loop_flag               true
% 2.33/0.85  --inst_learning_start                   3000
% 2.33/0.85  --inst_learning_factor                  2
% 2.33/0.85  --inst_start_prop_sim_after_learn       3
% 2.33/0.85  --inst_sel_renew                        solver
% 2.33/0.85  --inst_lit_activity_flag                true
% 2.33/0.85  --inst_restr_to_given                   false
% 2.33/0.85  --inst_activity_threshold               500
% 2.33/0.85  --inst_out_proof                        true
% 2.33/0.85  
% 2.33/0.85  ------ Resolution Options
% 2.33/0.85  
% 2.33/0.85  --resolution_flag                       true
% 2.33/0.85  --res_lit_sel                           adaptive
% 2.33/0.85  --res_lit_sel_side                      none
% 2.33/0.85  --res_ordering                          kbo
% 2.33/0.85  --res_to_prop_solver                    active
% 2.33/0.85  --res_prop_simpl_new                    false
% 2.33/0.85  --res_prop_simpl_given                  true
% 2.33/0.85  --res_passive_queue_type                priority_queues
% 2.33/0.85  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.85  --res_passive_queues_freq               [15;5]
% 2.33/0.85  --res_forward_subs                      full
% 2.33/0.85  --res_backward_subs                     full
% 2.33/0.85  --res_forward_subs_resolution           true
% 2.33/0.85  --res_backward_subs_resolution          true
% 2.33/0.85  --res_orphan_elimination                true
% 2.33/0.85  --res_time_limit                        2.
% 2.33/0.85  --res_out_proof                         true
% 2.33/0.85  
% 2.33/0.85  ------ Superposition Options
% 2.33/0.85  
% 2.33/0.85  --superposition_flag                    true
% 2.33/0.85  --sup_passive_queue_type                priority_queues
% 2.33/0.85  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.85  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.85  --demod_completeness_check              fast
% 2.33/0.85  --demod_use_ground                      true
% 2.33/0.85  --sup_to_prop_solver                    passive
% 2.33/0.85  --sup_prop_simpl_new                    true
% 2.33/0.85  --sup_prop_simpl_given                  true
% 2.33/0.85  --sup_fun_splitting                     false
% 2.33/0.85  --sup_smt_interval                      50000
% 2.33/0.85  
% 2.33/0.85  ------ Superposition Simplification Setup
% 2.33/0.85  
% 2.33/0.85  --sup_indices_passive                   []
% 2.33/0.85  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.85  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.85  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.85  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.85  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.85  --sup_full_bw                           [BwDemod]
% 2.33/0.85  --sup_immed_triv                        [TrivRules]
% 2.33/0.85  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.85  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.85  --sup_immed_bw_main                     []
% 2.33/0.85  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.85  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.85  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.85  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.85  
% 2.33/0.85  ------ Combination Options
% 2.33/0.85  
% 2.33/0.85  --comb_res_mult                         3
% 2.33/0.85  --comb_sup_mult                         2
% 2.33/0.85  --comb_inst_mult                        10
% 2.33/0.85  
% 2.33/0.85  ------ Debug Options
% 2.33/0.85  
% 2.33/0.85  --dbg_backtrace                         false
% 2.33/0.85  --dbg_dump_prop_clauses                 false
% 2.33/0.85  --dbg_dump_prop_clauses_file            -
% 2.33/0.85  --dbg_out_stat                          false
% 2.33/0.85  ------ Parsing...
% 2.33/0.85  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.85  
% 2.33/0.85  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.33/0.85  
% 2.33/0.85  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.85  
% 2.33/0.85  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.85  ------ Proving...
% 2.33/0.85  ------ Problem Properties 
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  clauses                                 17
% 2.33/0.85  conjectures                             4
% 2.33/0.85  EPR                                     2
% 2.33/0.85  Horn                                    13
% 2.33/0.85  unary                                   3
% 2.33/0.85  binary                                  8
% 2.33/0.85  lits                                    38
% 2.33/0.85  lits eq                                 13
% 2.33/0.85  fd_pure                                 0
% 2.33/0.85  fd_pseudo                               0
% 2.33/0.85  fd_cond                                 0
% 2.33/0.85  fd_pseudo_cond                          2
% 2.33/0.85  AC symbols                              0
% 2.33/0.85  
% 2.33/0.85  ------ Schedule dynamic 5 is on 
% 2.33/0.85  
% 2.33/0.85  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  ------ 
% 2.33/0.85  Current options:
% 2.33/0.85  ------ 
% 2.33/0.85  
% 2.33/0.85  ------ Input Options
% 2.33/0.85  
% 2.33/0.85  --out_options                           all
% 2.33/0.85  --tptp_safe_out                         true
% 2.33/0.85  --problem_path                          ""
% 2.33/0.85  --include_path                          ""
% 2.33/0.85  --clausifier                            res/vclausify_rel
% 2.33/0.85  --clausifier_options                    --mode clausify
% 2.33/0.85  --stdin                                 false
% 2.33/0.85  --stats_out                             all
% 2.33/0.85  
% 2.33/0.85  ------ General Options
% 2.33/0.85  
% 2.33/0.85  --fof                                   false
% 2.33/0.85  --time_out_real                         305.
% 2.33/0.85  --time_out_virtual                      -1.
% 2.33/0.85  --symbol_type_check                     false
% 2.33/0.85  --clausify_out                          false
% 2.33/0.85  --sig_cnt_out                           false
% 2.33/0.85  --trig_cnt_out                          false
% 2.33/0.85  --trig_cnt_out_tolerance                1.
% 2.33/0.85  --trig_cnt_out_sk_spl                   false
% 2.33/0.85  --abstr_cl_out                          false
% 2.33/0.85  
% 2.33/0.85  ------ Global Options
% 2.33/0.85  
% 2.33/0.85  --schedule                              default
% 2.33/0.85  --add_important_lit                     false
% 2.33/0.85  --prop_solver_per_cl                    1000
% 2.33/0.85  --min_unsat_core                        false
% 2.33/0.85  --soft_assumptions                      false
% 2.33/0.85  --soft_lemma_size                       3
% 2.33/0.85  --prop_impl_unit_size                   0
% 2.33/0.85  --prop_impl_unit                        []
% 2.33/0.85  --share_sel_clauses                     true
% 2.33/0.85  --reset_solvers                         false
% 2.33/0.85  --bc_imp_inh                            [conj_cone]
% 2.33/0.85  --conj_cone_tolerance                   3.
% 2.33/0.85  --extra_neg_conj                        none
% 2.33/0.85  --large_theory_mode                     true
% 2.33/0.85  --prolific_symb_bound                   200
% 2.33/0.85  --lt_threshold                          2000
% 2.33/0.85  --clause_weak_htbl                      true
% 2.33/0.85  --gc_record_bc_elim                     false
% 2.33/0.85  
% 2.33/0.85  ------ Preprocessing Options
% 2.33/0.85  
% 2.33/0.85  --preprocessing_flag                    true
% 2.33/0.85  --time_out_prep_mult                    0.1
% 2.33/0.85  --splitting_mode                        input
% 2.33/0.85  --splitting_grd                         true
% 2.33/0.85  --splitting_cvd                         false
% 2.33/0.85  --splitting_cvd_svl                     false
% 2.33/0.85  --splitting_nvd                         32
% 2.33/0.85  --sub_typing                            true
% 2.33/0.85  --prep_gs_sim                           true
% 2.33/0.85  --prep_unflatten                        true
% 2.33/0.85  --prep_res_sim                          true
% 2.33/0.85  --prep_upred                            true
% 2.33/0.85  --prep_sem_filter                       exhaustive
% 2.33/0.85  --prep_sem_filter_out                   false
% 2.33/0.85  --pred_elim                             true
% 2.33/0.85  --res_sim_input                         true
% 2.33/0.85  --eq_ax_congr_red                       true
% 2.33/0.85  --pure_diseq_elim                       true
% 2.33/0.85  --brand_transform                       false
% 2.33/0.85  --non_eq_to_eq                          false
% 2.33/0.85  --prep_def_merge                        true
% 2.33/0.85  --prep_def_merge_prop_impl              false
% 2.33/0.85  --prep_def_merge_mbd                    true
% 2.33/0.85  --prep_def_merge_tr_red                 false
% 2.33/0.85  --prep_def_merge_tr_cl                  false
% 2.33/0.85  --smt_preprocessing                     true
% 2.33/0.85  --smt_ac_axioms                         fast
% 2.33/0.85  --preprocessed_out                      false
% 2.33/0.85  --preprocessed_stats                    false
% 2.33/0.85  
% 2.33/0.85  ------ Abstraction refinement Options
% 2.33/0.85  
% 2.33/0.85  --abstr_ref                             []
% 2.33/0.85  --abstr_ref_prep                        false
% 2.33/0.85  --abstr_ref_until_sat                   false
% 2.33/0.85  --abstr_ref_sig_restrict                funpre
% 2.33/0.85  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.85  --abstr_ref_under                       []
% 2.33/0.85  
% 2.33/0.85  ------ SAT Options
% 2.33/0.85  
% 2.33/0.85  --sat_mode                              false
% 2.33/0.85  --sat_fm_restart_options                ""
% 2.33/0.85  --sat_gr_def                            false
% 2.33/0.85  --sat_epr_types                         true
% 2.33/0.85  --sat_non_cyclic_types                  false
% 2.33/0.85  --sat_finite_models                     false
% 2.33/0.85  --sat_fm_lemmas                         false
% 2.33/0.85  --sat_fm_prep                           false
% 2.33/0.85  --sat_fm_uc_incr                        true
% 2.33/0.85  --sat_out_model                         small
% 2.33/0.85  --sat_out_clauses                       false
% 2.33/0.85  
% 2.33/0.85  ------ QBF Options
% 2.33/0.85  
% 2.33/0.85  --qbf_mode                              false
% 2.33/0.85  --qbf_elim_univ                         false
% 2.33/0.85  --qbf_dom_inst                          none
% 2.33/0.85  --qbf_dom_pre_inst                      false
% 2.33/0.85  --qbf_sk_in                             false
% 2.33/0.85  --qbf_pred_elim                         true
% 2.33/0.85  --qbf_split                             512
% 2.33/0.85  
% 2.33/0.85  ------ BMC1 Options
% 2.33/0.85  
% 2.33/0.85  --bmc1_incremental                      false
% 2.33/0.85  --bmc1_axioms                           reachable_all
% 2.33/0.85  --bmc1_min_bound                        0
% 2.33/0.85  --bmc1_max_bound                        -1
% 2.33/0.85  --bmc1_max_bound_default                -1
% 2.33/0.85  --bmc1_symbol_reachability              true
% 2.33/0.85  --bmc1_property_lemmas                  false
% 2.33/0.85  --bmc1_k_induction                      false
% 2.33/0.85  --bmc1_non_equiv_states                 false
% 2.33/0.85  --bmc1_deadlock                         false
% 2.33/0.85  --bmc1_ucm                              false
% 2.33/0.85  --bmc1_add_unsat_core                   none
% 2.33/0.85  --bmc1_unsat_core_children              false
% 2.33/0.85  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.85  --bmc1_out_stat                         full
% 2.33/0.85  --bmc1_ground_init                      false
% 2.33/0.85  --bmc1_pre_inst_next_state              false
% 2.33/0.85  --bmc1_pre_inst_state                   false
% 2.33/0.85  --bmc1_pre_inst_reach_state             false
% 2.33/0.85  --bmc1_out_unsat_core                   false
% 2.33/0.85  --bmc1_aig_witness_out                  false
% 2.33/0.85  --bmc1_verbose                          false
% 2.33/0.85  --bmc1_dump_clauses_tptp                false
% 2.33/0.85  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.85  --bmc1_dump_file                        -
% 2.33/0.85  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.85  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.85  --bmc1_ucm_extend_mode                  1
% 2.33/0.85  --bmc1_ucm_init_mode                    2
% 2.33/0.85  --bmc1_ucm_cone_mode                    none
% 2.33/0.85  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.85  --bmc1_ucm_relax_model                  4
% 2.33/0.85  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.85  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.85  --bmc1_ucm_layered_model                none
% 2.33/0.85  --bmc1_ucm_max_lemma_size               10
% 2.33/0.85  
% 2.33/0.85  ------ AIG Options
% 2.33/0.85  
% 2.33/0.85  --aig_mode                              false
% 2.33/0.85  
% 2.33/0.85  ------ Instantiation Options
% 2.33/0.85  
% 2.33/0.85  --instantiation_flag                    true
% 2.33/0.85  --inst_sos_flag                         false
% 2.33/0.85  --inst_sos_phase                        true
% 2.33/0.85  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.85  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.85  --inst_lit_sel_side                     none
% 2.33/0.85  --inst_solver_per_active                1400
% 2.33/0.85  --inst_solver_calls_frac                1.
% 2.33/0.85  --inst_passive_queue_type               priority_queues
% 2.33/0.85  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.85  --inst_passive_queues_freq              [25;2]
% 2.33/0.85  --inst_dismatching                      true
% 2.33/0.85  --inst_eager_unprocessed_to_passive     true
% 2.33/0.85  --inst_prop_sim_given                   true
% 2.33/0.85  --inst_prop_sim_new                     false
% 2.33/0.85  --inst_subs_new                         false
% 2.33/0.85  --inst_eq_res_simp                      false
% 2.33/0.85  --inst_subs_given                       false
% 2.33/0.85  --inst_orphan_elimination               true
% 2.33/0.85  --inst_learning_loop_flag               true
% 2.33/0.85  --inst_learning_start                   3000
% 2.33/0.85  --inst_learning_factor                  2
% 2.33/0.85  --inst_start_prop_sim_after_learn       3
% 2.33/0.85  --inst_sel_renew                        solver
% 2.33/0.85  --inst_lit_activity_flag                true
% 2.33/0.85  --inst_restr_to_given                   false
% 2.33/0.85  --inst_activity_threshold               500
% 2.33/0.85  --inst_out_proof                        true
% 2.33/0.85  
% 2.33/0.85  ------ Resolution Options
% 2.33/0.85  
% 2.33/0.85  --resolution_flag                       false
% 2.33/0.85  --res_lit_sel                           adaptive
% 2.33/0.85  --res_lit_sel_side                      none
% 2.33/0.85  --res_ordering                          kbo
% 2.33/0.85  --res_to_prop_solver                    active
% 2.33/0.85  --res_prop_simpl_new                    false
% 2.33/0.85  --res_prop_simpl_given                  true
% 2.33/0.85  --res_passive_queue_type                priority_queues
% 2.33/0.85  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.85  --res_passive_queues_freq               [15;5]
% 2.33/0.85  --res_forward_subs                      full
% 2.33/0.85  --res_backward_subs                     full
% 2.33/0.85  --res_forward_subs_resolution           true
% 2.33/0.85  --res_backward_subs_resolution          true
% 2.33/0.85  --res_orphan_elimination                true
% 2.33/0.85  --res_time_limit                        2.
% 2.33/0.85  --res_out_proof                         true
% 2.33/0.85  
% 2.33/0.85  ------ Superposition Options
% 2.33/0.85  
% 2.33/0.85  --superposition_flag                    true
% 2.33/0.85  --sup_passive_queue_type                priority_queues
% 2.33/0.85  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.85  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.85  --demod_completeness_check              fast
% 2.33/0.85  --demod_use_ground                      true
% 2.33/0.85  --sup_to_prop_solver                    passive
% 2.33/0.85  --sup_prop_simpl_new                    true
% 2.33/0.85  --sup_prop_simpl_given                  true
% 2.33/0.85  --sup_fun_splitting                     false
% 2.33/0.85  --sup_smt_interval                      50000
% 2.33/0.85  
% 2.33/0.85  ------ Superposition Simplification Setup
% 2.33/0.85  
% 2.33/0.85  --sup_indices_passive                   []
% 2.33/0.85  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.85  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.85  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.85  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.85  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.85  --sup_full_bw                           [BwDemod]
% 2.33/0.85  --sup_immed_triv                        [TrivRules]
% 2.33/0.85  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.85  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.85  --sup_immed_bw_main                     []
% 2.33/0.85  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.85  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.85  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.85  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.85  
% 2.33/0.85  ------ Combination Options
% 2.33/0.85  
% 2.33/0.85  --comb_res_mult                         3
% 2.33/0.85  --comb_sup_mult                         2
% 2.33/0.85  --comb_inst_mult                        10
% 2.33/0.85  
% 2.33/0.85  ------ Debug Options
% 2.33/0.85  
% 2.33/0.85  --dbg_backtrace                         false
% 2.33/0.85  --dbg_dump_prop_clauses                 false
% 2.33/0.85  --dbg_dump_prop_clauses_file            -
% 2.33/0.85  --dbg_out_stat                          false
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  ------ Proving...
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  % SZS status Theorem for theBenchmark.p
% 2.33/0.85  
% 2.33/0.85  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.85  
% 2.33/0.85  fof(f1,axiom,(
% 2.33/0.85    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f13,plain,(
% 2.33/0.85    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.33/0.85    inference(ennf_transformation,[],[f1])).
% 2.33/0.85  
% 2.33/0.85  fof(f26,plain,(
% 2.33/0.85    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.33/0.85    inference(nnf_transformation,[],[f13])).
% 2.33/0.85  
% 2.33/0.85  fof(f27,plain,(
% 2.33/0.85    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.33/0.85    introduced(choice_axiom,[])).
% 2.33/0.85  
% 2.33/0.85  fof(f28,plain,(
% 2.33/0.85    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.33/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.33/0.85  
% 2.33/0.85  fof(f33,plain,(
% 2.33/0.85    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.33/0.85    inference(cnf_transformation,[],[f28])).
% 2.33/0.85  
% 2.33/0.85  fof(f2,axiom,(
% 2.33/0.85    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f35,plain,(
% 2.33/0.85    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.33/0.85    inference(cnf_transformation,[],[f2])).
% 2.33/0.85  
% 2.33/0.85  fof(f5,axiom,(
% 2.33/0.85    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f17,plain,(
% 2.33/0.85    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.33/0.85    inference(ennf_transformation,[],[f5])).
% 2.33/0.85  
% 2.33/0.85  fof(f38,plain,(
% 2.33/0.85    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.33/0.85    inference(cnf_transformation,[],[f17])).
% 2.33/0.85  
% 2.33/0.85  fof(f11,conjecture,(
% 2.33/0.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f12,negated_conjecture,(
% 2.33/0.85    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 2.33/0.85    inference(negated_conjecture,[],[f11])).
% 2.33/0.85  
% 2.33/0.85  fof(f24,plain,(
% 2.33/0.85    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.33/0.85    inference(ennf_transformation,[],[f12])).
% 2.33/0.85  
% 2.33/0.85  fof(f25,plain,(
% 2.33/0.85    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.33/0.85    inference(flattening,[],[f24])).
% 2.33/0.85  
% 2.33/0.85  fof(f31,plain,(
% 2.33/0.85    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK4(X3)) = X3 & r2_hidden(sK4(X3),X0)))) )),
% 2.33/0.85    introduced(choice_axiom,[])).
% 2.33/0.85  
% 2.33/0.85  fof(f30,plain,(
% 2.33/0.85    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : (? [X4] : (k1_funct_1(sK3,X4) = X3 & r2_hidden(X4,sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.33/0.85    introduced(choice_axiom,[])).
% 2.33/0.85  
% 2.33/0.85  fof(f32,plain,(
% 2.33/0.85    k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : ((k1_funct_1(sK3,sK4(X3)) = X3 & r2_hidden(sK4(X3),sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.33/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30])).
% 2.33/0.85  
% 2.33/0.85  fof(f52,plain,(
% 2.33/0.85    ( ! [X3] : (r2_hidden(sK4(X3),sK1) | ~r2_hidden(X3,sK2)) )),
% 2.33/0.85    inference(cnf_transformation,[],[f32])).
% 2.33/0.85  
% 2.33/0.85  fof(f10,axiom,(
% 2.33/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f22,plain,(
% 2.33/0.85    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.85    inference(ennf_transformation,[],[f10])).
% 2.33/0.85  
% 2.33/0.85  fof(f23,plain,(
% 2.33/0.85    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.85    inference(flattening,[],[f22])).
% 2.33/0.85  
% 2.33/0.85  fof(f29,plain,(
% 2.33/0.85    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.85    inference(nnf_transformation,[],[f23])).
% 2.33/0.85  
% 2.33/0.85  fof(f43,plain,(
% 2.33/0.85    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.85    inference(cnf_transformation,[],[f29])).
% 2.33/0.85  
% 2.33/0.85  fof(f50,plain,(
% 2.33/0.85    v1_funct_2(sK3,sK1,sK2)),
% 2.33/0.85    inference(cnf_transformation,[],[f32])).
% 2.33/0.85  
% 2.33/0.85  fof(f51,plain,(
% 2.33/0.85    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.33/0.85    inference(cnf_transformation,[],[f32])).
% 2.33/0.85  
% 2.33/0.85  fof(f8,axiom,(
% 2.33/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f20,plain,(
% 2.33/0.85    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.85    inference(ennf_transformation,[],[f8])).
% 2.33/0.85  
% 2.33/0.85  fof(f41,plain,(
% 2.33/0.85    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.85    inference(cnf_transformation,[],[f20])).
% 2.33/0.85  
% 2.33/0.85  fof(f53,plain,(
% 2.33/0.85    ( ! [X3] : (k1_funct_1(sK3,sK4(X3)) = X3 | ~r2_hidden(X3,sK2)) )),
% 2.33/0.85    inference(cnf_transformation,[],[f32])).
% 2.33/0.85  
% 2.33/0.85  fof(f9,axiom,(
% 2.33/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f21,plain,(
% 2.33/0.85    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.85    inference(ennf_transformation,[],[f9])).
% 2.33/0.85  
% 2.33/0.85  fof(f42,plain,(
% 2.33/0.85    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.85    inference(cnf_transformation,[],[f21])).
% 2.33/0.85  
% 2.33/0.85  fof(f7,axiom,(
% 2.33/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f19,plain,(
% 2.33/0.85    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.85    inference(ennf_transformation,[],[f7])).
% 2.33/0.85  
% 2.33/0.85  fof(f40,plain,(
% 2.33/0.85    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.85    inference(cnf_transformation,[],[f19])).
% 2.33/0.85  
% 2.33/0.85  fof(f3,axiom,(
% 2.33/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f14,plain,(
% 2.33/0.85    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.33/0.85    inference(ennf_transformation,[],[f3])).
% 2.33/0.85  
% 2.33/0.85  fof(f36,plain,(
% 2.33/0.85    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.33/0.85    inference(cnf_transformation,[],[f14])).
% 2.33/0.85  
% 2.33/0.85  fof(f54,plain,(
% 2.33/0.85    k2_relset_1(sK1,sK2,sK3) != sK2),
% 2.33/0.85    inference(cnf_transformation,[],[f32])).
% 2.33/0.85  
% 2.33/0.85  fof(f6,axiom,(
% 2.33/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f18,plain,(
% 2.33/0.85    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.85    inference(ennf_transformation,[],[f6])).
% 2.33/0.85  
% 2.33/0.85  fof(f39,plain,(
% 2.33/0.85    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.85    inference(cnf_transformation,[],[f18])).
% 2.33/0.85  
% 2.33/0.85  fof(f4,axiom,(
% 2.33/0.85    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.33/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.85  
% 2.33/0.85  fof(f15,plain,(
% 2.33/0.85    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.33/0.85    inference(ennf_transformation,[],[f4])).
% 2.33/0.85  
% 2.33/0.85  fof(f16,plain,(
% 2.33/0.85    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.33/0.85    inference(flattening,[],[f15])).
% 2.33/0.85  
% 2.33/0.85  fof(f37,plain,(
% 2.33/0.85    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.33/0.85    inference(cnf_transformation,[],[f16])).
% 2.33/0.85  
% 2.33/0.85  fof(f49,plain,(
% 2.33/0.85    v1_funct_1(sK3)),
% 2.33/0.85    inference(cnf_transformation,[],[f32])).
% 2.33/0.85  
% 2.33/0.85  fof(f34,plain,(
% 2.33/0.85    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 2.33/0.85    inference(cnf_transformation,[],[f28])).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1,plain,
% 2.33/0.85      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.33/0.85      inference(cnf_transformation,[],[f33]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_748,plain,
% 2.33/0.85      ( X0 = X1
% 2.33/0.85      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.33/0.85      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2,plain,
% 2.33/0.85      ( r1_tarski(k1_xboole_0,X0) ),
% 2.33/0.85      inference(cnf_transformation,[],[f35]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_5,plain,
% 2.33/0.85      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.33/0.85      inference(cnf_transformation,[],[f38]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_244,plain,
% 2.33/0.85      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.33/0.85      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_245,plain,
% 2.33/0.85      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.33/0.85      inference(unflattening,[status(thm)],[c_244]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_740,plain,
% 2.33/0.85      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1611,plain,
% 2.33/0.85      ( k1_xboole_0 = X0
% 2.33/0.85      | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_748,c_740]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_18,negated_conjecture,
% 2.33/0.85      ( ~ r2_hidden(X0,sK2) | r2_hidden(sK4(X0),sK1) ),
% 2.33/0.85      inference(cnf_transformation,[],[f52]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_742,plain,
% 2.33/0.85      ( r2_hidden(X0,sK2) != iProver_top
% 2.33/0.85      | r2_hidden(sK4(X0),sK1) = iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_15,plain,
% 2.33/0.85      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/0.85      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.85      | k1_relset_1(X1,X2,X0) = X1
% 2.33/0.85      | k1_xboole_0 = X2 ),
% 2.33/0.85      inference(cnf_transformation,[],[f43]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_20,negated_conjecture,
% 2.33/0.85      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.33/0.85      inference(cnf_transformation,[],[f50]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_338,plain,
% 2.33/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.85      | k1_relset_1(X1,X2,X0) = X1
% 2.33/0.85      | sK3 != X0
% 2.33/0.85      | sK2 != X2
% 2.33/0.85      | sK1 != X1
% 2.33/0.85      | k1_xboole_0 = X2 ),
% 2.33/0.85      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_339,plain,
% 2.33/0.85      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.33/0.85      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.33/0.85      | k1_xboole_0 = sK2 ),
% 2.33/0.85      inference(unflattening,[status(thm)],[c_338]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_19,negated_conjecture,
% 2.33/0.85      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.33/0.85      inference(cnf_transformation,[],[f51]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_341,plain,
% 2.33/0.85      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.33/0.85      inference(global_propositional_subsumption,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_339,c_19]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_741,plain,
% 2.33/0.85      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_8,plain,
% 2.33/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.85      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.33/0.85      inference(cnf_transformation,[],[f41]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_745,plain,
% 2.33/0.85      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.33/0.85      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1169,plain,
% 2.33/0.85      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_741,c_745]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1351,plain,
% 2.33/0.85      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_341,c_1169]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_17,negated_conjecture,
% 2.33/0.85      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4(X0)) = X0 ),
% 2.33/0.85      inference(cnf_transformation,[],[f53]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_743,plain,
% 2.33/0.85      ( k1_funct_1(sK3,sK4(X0)) = X0 | r2_hidden(X0,sK2) != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1244,plain,
% 2.33/0.85      ( k1_funct_1(sK3,sK4(sK0(X0,sK2))) = sK0(X0,sK2)
% 2.33/0.85      | sK2 = X0
% 2.33/0.85      | r2_hidden(sK0(X0,sK2),X0) = iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_748,c_743]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_9,plain,
% 2.33/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.85      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.33/0.85      inference(cnf_transformation,[],[f42]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_744,plain,
% 2.33/0.85      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.33/0.85      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1059,plain,
% 2.33/0.85      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_741,c_744]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_7,plain,
% 2.33/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.85      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.33/0.85      inference(cnf_transformation,[],[f40]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_746,plain,
% 2.33/0.85      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.33/0.85      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1267,plain,
% 2.33/0.85      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.33/0.85      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_1059,c_746]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_24,plain,
% 2.33/0.85      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1544,plain,
% 2.33/0.85      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.33/0.85      inference(global_propositional_subsumption,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_1267,c_24]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_3,plain,
% 2.33/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/0.85      | ~ r2_hidden(X2,X0)
% 2.33/0.85      | r2_hidden(X2,X1) ),
% 2.33/0.85      inference(cnf_transformation,[],[f36]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_747,plain,
% 2.33/0.85      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.33/0.85      | r2_hidden(X2,X0) != iProver_top
% 2.33/0.85      | r2_hidden(X2,X1) = iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1639,plain,
% 2.33/0.85      ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
% 2.33/0.85      | r2_hidden(X0,sK2) = iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_1544,c_747]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2148,plain,
% 2.33/0.85      ( k1_funct_1(sK3,sK4(sK0(k2_relat_1(sK3),sK2))) = sK0(k2_relat_1(sK3),sK2)
% 2.33/0.85      | k2_relat_1(sK3) = sK2
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_1244,c_1639]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_16,negated_conjecture,
% 2.33/0.85      ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 2.33/0.85      inference(cnf_transformation,[],[f54]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1266,plain,
% 2.33/0.85      ( k2_relat_1(sK3) != sK2 ),
% 2.33/0.85      inference(demodulation,[status(thm)],[c_1059,c_16]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2202,plain,
% 2.33/0.85      ( k1_funct_1(sK3,sK4(sK0(k2_relat_1(sK3),sK2))) = sK0(k2_relat_1(sK3),sK2)
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top ),
% 2.33/0.85      inference(global_propositional_subsumption,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_2148,c_1266]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2208,plain,
% 2.33/0.85      ( k1_funct_1(sK3,sK4(sK0(k2_relat_1(sK3),sK2))) = sK0(k2_relat_1(sK3),sK2) ),
% 2.33/0.85      inference(forward_subsumption_resolution,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_2202,c_743]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_6,plain,
% 2.33/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.85      | v1_relat_1(X0) ),
% 2.33/0.85      inference(cnf_transformation,[],[f39]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_4,plain,
% 2.33/0.85      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.33/0.85      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.33/0.85      | ~ v1_relat_1(X1)
% 2.33/0.85      | ~ v1_funct_1(X1) ),
% 2.33/0.85      inference(cnf_transformation,[],[f37]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_21,negated_conjecture,
% 2.33/0.85      ( v1_funct_1(sK3) ),
% 2.33/0.85      inference(cnf_transformation,[],[f49]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_255,plain,
% 2.33/0.85      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.33/0.85      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.33/0.85      | ~ v1_relat_1(X1)
% 2.33/0.85      | sK3 != X1 ),
% 2.33/0.85      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_256,plain,
% 2.33/0.85      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.33/0.85      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 2.33/0.85      | ~ v1_relat_1(sK3) ),
% 2.33/0.85      inference(unflattening,[status(thm)],[c_255]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_274,plain,
% 2.33/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.85      | ~ r2_hidden(X3,k1_relat_1(sK3))
% 2.33/0.85      | r2_hidden(k1_funct_1(sK3,X3),k2_relat_1(sK3))
% 2.33/0.85      | sK3 != X0 ),
% 2.33/0.85      inference(resolution_lifted,[status(thm)],[c_6,c_256]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_275,plain,
% 2.33/0.85      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.33/0.85      | ~ r2_hidden(X2,k1_relat_1(sK3))
% 2.33/0.85      | r2_hidden(k1_funct_1(sK3,X2),k2_relat_1(sK3)) ),
% 2.33/0.85      inference(unflattening,[status(thm)],[c_274]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_455,plain,
% 2.33/0.85      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.33/0.85      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 2.33/0.85      | ~ sP0_iProver_split ),
% 2.33/0.85      inference(splitting,
% 2.33/0.85                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.33/0.85                [c_275]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_739,plain,
% 2.33/0.85      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.33/0.85      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.33/0.85      | sP0_iProver_split != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_457,plain,
% 2.33/0.85      ( sP1_iProver_split | sP0_iProver_split ),
% 2.33/0.85      inference(splitting,
% 2.33/0.85                [splitting(split),new_symbols(definition,[])],
% 2.33/0.85                [c_275]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_483,plain,
% 2.33/0.85      ( sP1_iProver_split = iProver_top
% 2.33/0.85      | sP0_iProver_split = iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_487,plain,
% 2.33/0.85      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.33/0.85      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.33/0.85      | sP0_iProver_split != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_456,plain,
% 2.33/0.85      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.33/0.85      | ~ sP1_iProver_split ),
% 2.33/0.85      inference(splitting,
% 2.33/0.85                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.33/0.85                [c_275]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_858,plain,
% 2.33/0.85      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.33/0.85      | ~ sP1_iProver_split ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_456]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_859,plain,
% 2.33/0.85      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.33/0.85      | sP1_iProver_split != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1048,plain,
% 2.33/0.85      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.33/0.85      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.33/0.85      inference(global_propositional_subsumption,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_739,c_24,c_483,c_487,c_859]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1049,plain,
% 2.33/0.85      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.33/0.85      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 2.33/0.85      inference(renaming,[status(thm)],[c_1048]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2209,plain,
% 2.33/0.85      ( r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) = iProver_top
% 2.33/0.85      | r2_hidden(sK4(sK0(k2_relat_1(sK3),sK2)),k1_relat_1(sK3)) != iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_2208,c_1049]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2317,plain,
% 2.33/0.85      ( sK2 = k1_xboole_0
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) = iProver_top
% 2.33/0.85      | r2_hidden(sK4(sK0(k2_relat_1(sK3),sK2)),sK1) != iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_1351,c_2209]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_874,plain,
% 2.33/0.85      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.33/0.85      | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_9]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_460,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_864,plain,
% 2.33/0.85      ( k2_relset_1(sK1,sK2,sK3) != X0
% 2.33/0.85      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.33/0.85      | sK2 != X0 ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_460]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_944,plain,
% 2.33/0.85      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 2.33/0.85      | k2_relset_1(sK1,sK2,sK3) = sK2
% 2.33/0.85      | sK2 != k2_relat_1(sK3) ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_864]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_0,plain,
% 2.33/0.85      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.33/0.85      | ~ r2_hidden(sK0(X0,X1),X0)
% 2.33/0.85      | X1 = X0 ),
% 2.33/0.85      inference(cnf_transformation,[],[f34]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1007,plain,
% 2.33/0.85      ( ~ r2_hidden(sK0(X0,sK2),X0)
% 2.33/0.85      | ~ r2_hidden(sK0(X0,sK2),sK2)
% 2.33/0.85      | sK2 = X0 ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_0]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1506,plain,
% 2.33/0.85      ( ~ r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3))
% 2.33/0.85      | ~ r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2)
% 2.33/0.85      | sK2 = k2_relat_1(sK3) ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_1007]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1507,plain,
% 2.33/0.85      ( sK2 = k2_relat_1(sK3)
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) != iProver_top
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_1506]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2146,plain,
% 2.33/0.85      ( k2_relat_1(sK3) = X0
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),X0),X0) = iProver_top
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),X0),sK2) = iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_748,c_1639]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2388,plain,
% 2.33/0.85      ( k2_relat_1(sK3) = sK2
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top
% 2.33/0.85      | iProver_top != iProver_top ),
% 2.33/0.85      inference(equality_factoring,[status(thm)],[c_2146]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2390,plain,
% 2.33/0.85      ( k2_relat_1(sK3) = sK2
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) = iProver_top ),
% 2.33/0.85      inference(equality_resolution_simp,[status(thm)],[c_2388]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2686,plain,
% 2.33/0.85      ( sK2 = k1_xboole_0
% 2.33/0.85      | r2_hidden(sK4(sK0(k2_relat_1(sK3),sK2)),sK1) != iProver_top ),
% 2.33/0.85      inference(global_propositional_subsumption,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_2317,c_19,c_16,c_874,c_944,c_1266,c_1507,c_2390]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2692,plain,
% 2.33/0.85      ( sK2 = k1_xboole_0
% 2.33/0.85      | r2_hidden(sK0(k2_relat_1(sK3),sK2),sK2) != iProver_top ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_742,c_2686]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2764,plain,
% 2.33/0.85      ( sK2 = k1_xboole_0 ),
% 2.33/0.85      inference(global_propositional_subsumption,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_2692,c_1266,c_2390]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_2773,plain,
% 2.33/0.85      ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
% 2.33/0.85      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.33/0.85      inference(demodulation,[status(thm)],[c_2764,c_1639]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_246,plain,
% 2.33/0.85      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.33/0.85      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_3546,plain,
% 2.33/0.85      ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
% 2.33/0.85      inference(global_propositional_subsumption,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_2773,c_246]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_3556,plain,
% 2.33/0.85      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.33/0.85      inference(superposition,[status(thm)],[c_1611,c_3546]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1013,plain,
% 2.33/0.85      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_460]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1515,plain,
% 2.33/0.85      ( k2_relat_1(sK3) != X0 | sK2 != X0 | sK2 = k2_relat_1(sK3) ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_1013]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(c_1516,plain,
% 2.33/0.85      ( k2_relat_1(sK3) != k1_xboole_0
% 2.33/0.85      | sK2 = k2_relat_1(sK3)
% 2.33/0.85      | sK2 != k1_xboole_0 ),
% 2.33/0.85      inference(instantiation,[status(thm)],[c_1515]) ).
% 2.33/0.85  
% 2.33/0.85  cnf(contradiction,plain,
% 2.33/0.85      ( $false ),
% 2.33/0.85      inference(minisat,
% 2.33/0.85                [status(thm)],
% 2.33/0.85                [c_3556,c_2692,c_2390,c_1516,c_1266,c_944,c_874,c_16,
% 2.33/0.85                 c_19]) ).
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.85  
% 2.33/0.85  ------                               Statistics
% 2.33/0.85  
% 2.33/0.85  ------ General
% 2.33/0.85  
% 2.33/0.85  abstr_ref_over_cycles:                  0
% 2.33/0.85  abstr_ref_under_cycles:                 0
% 2.33/0.85  gc_basic_clause_elim:                   0
% 2.33/0.85  forced_gc_time:                         0
% 2.33/0.85  parsing_time:                           0.007
% 2.33/0.85  unif_index_cands_time:                  0.
% 2.33/0.85  unif_index_add_time:                    0.
% 2.33/0.85  orderings_time:                         0.
% 2.33/0.85  out_proof_time:                         0.013
% 2.33/0.85  total_time:                             0.124
% 2.33/0.85  num_of_symbols:                         52
% 2.33/0.85  num_of_terms:                           3168
% 2.33/0.85  
% 2.33/0.85  ------ Preprocessing
% 2.33/0.85  
% 2.33/0.85  num_of_splits:                          2
% 2.33/0.85  num_of_split_atoms:                     2
% 2.33/0.85  num_of_reused_defs:                     0
% 2.33/0.85  num_eq_ax_congr_red:                    15
% 2.33/0.85  num_of_sem_filtered_clauses:            1
% 2.33/0.85  num_of_subtypes:                        0
% 2.33/0.85  monotx_restored_types:                  0
% 2.33/0.85  sat_num_of_epr_types:                   0
% 2.33/0.85  sat_num_of_non_cyclic_types:            0
% 2.33/0.85  sat_guarded_non_collapsed_types:        0
% 2.33/0.85  num_pure_diseq_elim:                    0
% 2.33/0.85  simp_replaced_by:                       0
% 2.33/0.85  res_preprocessed:                       94
% 2.33/0.85  prep_upred:                             0
% 2.33/0.85  prep_unflattend:                        31
% 2.33/0.85  smt_new_axioms:                         0
% 2.33/0.85  pred_elim_cands:                        2
% 2.33/0.85  pred_elim:                              4
% 2.33/0.85  pred_elim_cl:                           7
% 2.33/0.85  pred_elim_cycles:                       6
% 2.33/0.85  merged_defs:                            0
% 2.33/0.85  merged_defs_ncl:                        0
% 2.33/0.85  bin_hyper_res:                          0
% 2.33/0.85  prep_cycles:                            4
% 2.33/0.85  pred_elim_time:                         0.002
% 2.33/0.85  splitting_time:                         0.
% 2.33/0.85  sem_filter_time:                        0.
% 2.33/0.85  monotx_time:                            0.001
% 2.33/0.85  subtype_inf_time:                       0.
% 2.33/0.85  
% 2.33/0.85  ------ Problem properties
% 2.33/0.85  
% 2.33/0.85  clauses:                                17
% 2.33/0.85  conjectures:                            4
% 2.33/0.85  epr:                                    2
% 2.33/0.85  horn:                                   13
% 2.33/0.85  ground:                                 6
% 2.33/0.85  unary:                                  3
% 2.33/0.85  binary:                                 8
% 2.33/0.85  lits:                                   38
% 2.33/0.85  lits_eq:                                13
% 2.33/0.85  fd_pure:                                0
% 2.33/0.85  fd_pseudo:                              0
% 2.33/0.85  fd_cond:                                0
% 2.33/0.85  fd_pseudo_cond:                         2
% 2.33/0.85  ac_symbols:                             0
% 2.33/0.85  
% 2.33/0.85  ------ Propositional Solver
% 2.33/0.85  
% 2.33/0.85  prop_solver_calls:                      28
% 2.33/0.85  prop_fast_solver_calls:                 608
% 2.33/0.85  smt_solver_calls:                       0
% 2.33/0.85  smt_fast_solver_calls:                  0
% 2.33/0.85  prop_num_of_clauses:                    1227
% 2.33/0.85  prop_preprocess_simplified:             3560
% 2.33/0.85  prop_fo_subsumed:                       10
% 2.33/0.85  prop_solver_time:                       0.
% 2.33/0.85  smt_solver_time:                        0.
% 2.33/0.85  smt_fast_solver_time:                   0.
% 2.33/0.85  prop_fast_solver_time:                  0.
% 2.33/0.85  prop_unsat_core_time:                   0.
% 2.33/0.85  
% 2.33/0.85  ------ QBF
% 2.33/0.85  
% 2.33/0.85  qbf_q_res:                              0
% 2.33/0.85  qbf_num_tautologies:                    0
% 2.33/0.85  qbf_prep_cycles:                        0
% 2.33/0.85  
% 2.33/0.85  ------ BMC1
% 2.33/0.85  
% 2.33/0.85  bmc1_current_bound:                     -1
% 2.33/0.85  bmc1_last_solved_bound:                 -1
% 2.33/0.85  bmc1_unsat_core_size:                   -1
% 2.33/0.85  bmc1_unsat_core_parents_size:           -1
% 2.33/0.85  bmc1_merge_next_fun:                    0
% 2.33/0.85  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.85  
% 2.33/0.85  ------ Instantiation
% 2.33/0.85  
% 2.33/0.85  inst_num_of_clauses:                    405
% 2.33/0.85  inst_num_in_passive:                    20
% 2.33/0.85  inst_num_in_active:                     223
% 2.33/0.85  inst_num_in_unprocessed:                162
% 2.33/0.85  inst_num_of_loops:                      290
% 2.33/0.85  inst_num_of_learning_restarts:          0
% 2.33/0.85  inst_num_moves_active_passive:          64
% 2.33/0.85  inst_lit_activity:                      0
% 2.33/0.85  inst_lit_activity_moves:                0
% 2.33/0.85  inst_num_tautologies:                   0
% 2.33/0.85  inst_num_prop_implied:                  0
% 2.33/0.85  inst_num_existing_simplified:           0
% 2.33/0.85  inst_num_eq_res_simplified:             0
% 2.33/0.85  inst_num_child_elim:                    0
% 2.33/0.85  inst_num_of_dismatching_blockings:      117
% 2.33/0.85  inst_num_of_non_proper_insts:           418
% 2.33/0.85  inst_num_of_duplicates:                 0
% 2.33/0.85  inst_inst_num_from_inst_to_res:         0
% 2.33/0.85  inst_dismatching_checking_time:         0.
% 2.33/0.85  
% 2.33/0.85  ------ Resolution
% 2.33/0.85  
% 2.33/0.85  res_num_of_clauses:                     0
% 2.33/0.85  res_num_in_passive:                     0
% 2.33/0.85  res_num_in_active:                      0
% 2.33/0.85  res_num_of_loops:                       98
% 2.33/0.85  res_forward_subset_subsumed:            61
% 2.33/0.85  res_backward_subset_subsumed:           0
% 2.33/0.85  res_forward_subsumed:                   0
% 2.33/0.85  res_backward_subsumed:                  0
% 2.33/0.85  res_forward_subsumption_resolution:     0
% 2.33/0.85  res_backward_subsumption_resolution:    0
% 2.33/0.85  res_clause_to_clause_subsumption:       175
% 2.33/0.85  res_orphan_elimination:                 0
% 2.33/0.85  res_tautology_del:                      33
% 2.33/0.85  res_num_eq_res_simplified:              0
% 2.33/0.85  res_num_sel_changes:                    0
% 2.33/0.85  res_moves_from_active_to_pass:          0
% 2.33/0.85  
% 2.33/0.85  ------ Superposition
% 2.33/0.85  
% 2.33/0.85  sup_time_total:                         0.
% 2.33/0.85  sup_time_generating:                    0.
% 2.33/0.85  sup_time_sim_full:                      0.
% 2.33/0.85  sup_time_sim_immed:                     0.
% 2.33/0.85  
% 2.33/0.85  sup_num_of_clauses:                     52
% 2.33/0.85  sup_num_in_active:                      30
% 2.33/0.85  sup_num_in_passive:                     22
% 2.33/0.85  sup_num_of_loops:                       56
% 2.33/0.85  sup_fw_superposition:                   48
% 2.33/0.85  sup_bw_superposition:                   48
% 2.33/0.85  sup_immediate_simplified:               13
% 2.33/0.85  sup_given_eliminated:                   1
% 2.33/0.85  comparisons_done:                       0
% 2.33/0.85  comparisons_avoided:                    25
% 2.33/0.85  
% 2.33/0.85  ------ Simplifications
% 2.33/0.85  
% 2.33/0.85  
% 2.33/0.85  sim_fw_subset_subsumed:                 6
% 2.33/0.85  sim_bw_subset_subsumed:                 11
% 2.33/0.85  sim_fw_subsumed:                        5
% 2.33/0.85  sim_bw_subsumed:                        0
% 2.33/0.85  sim_fw_subsumption_res:                 2
% 2.33/0.85  sim_bw_subsumption_res:                 0
% 2.33/0.85  sim_tautology_del:                      2
% 2.33/0.85  sim_eq_tautology_del:                   17
% 2.33/0.85  sim_eq_res_simp:                        3
% 2.33/0.85  sim_fw_demodulated:                     0
% 2.33/0.85  sim_bw_demodulated:                     25
% 2.33/0.85  sim_light_normalised:                   1
% 2.33/0.85  sim_joinable_taut:                      0
% 2.33/0.85  sim_joinable_simp:                      0
% 2.33/0.85  sim_ac_normalised:                      0
% 2.33/0.85  sim_smt_subsumption:                    0
% 2.33/0.85  
%------------------------------------------------------------------------------
