%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:59 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1872)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
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

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
          & r2_hidden(X3,sK2)
          & r2_hidden(X2,sK2) )
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK4 != sK5
    & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK4,sK2)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f31,f30])).

fof(f56,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f42,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_913,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2)
    | k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X0)) = X0
    | sK2 != X3
    | sK2 != X1
    | sK3 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_25,c_23,c_22])).

cnf(c_910,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_1262,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_913,c_910])).

cnf(c_19,negated_conjecture,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1270,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1262,c_19])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_912,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1263,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_912,c_910])).

cnf(c_1501,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_1270,c_1263])).

cnf(c_911,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_915,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_917,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1694,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_917])).

cnf(c_2205,plain,
    ( r1_tarski(k1_relset_1(sK2,sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_1694])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_914,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2370,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_911,c_914])).

cnf(c_2517,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2205,c_2370])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_921,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2964,plain,
    ( k1_relat_1(sK3) = sK2
    | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_921])).

cnf(c_18,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_532,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1136,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_318,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_323,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ r2_hidden(X0,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_22])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_323])).

cnf(c_909,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_325,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1035,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_1073,plain,
    ( r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_28,c_325,c_1035])).

cnf(c_1074,plain,
    ( X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1073])).

cnf(c_1081,plain,
    ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
    | sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1074])).

cnf(c_1149,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1081])).

cnf(c_1156,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | sK5 = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1149])).

cnf(c_1179,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_541,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1060,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,sK2)
    | X1 != sK2
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_1135,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK2)
    | X0 != sK2
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_1583,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK2)
    | k1_relat_1(sK3) != sK2
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_1065,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,sK2)
    | X1 != sK2
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_1178,plain,
    ( r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,sK2)
    | X0 != sK2
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_1604,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,sK2)
    | k1_relat_1(sK3) != sK2
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_1274,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1829,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | k1_relat_1(sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_1830,plain,
    ( k1_relat_1(sK3) = sK2
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1829])).

cnf(c_533,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1040,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_2265,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_3506,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2964,c_21,c_20,c_18,c_1136,c_1156,c_1179,c_1583,c_1604,c_1830,c_2265,c_2517])).

cnf(c_3511,plain,
    ( sK5 = sK4
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_3506])).

cnf(c_3514,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3511,c_21,c_20,c_18,c_1136,c_1156,c_1179,c_1501,c_1583,c_1604,c_1872,c_2265,c_2967])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_919,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3519,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3514,c_919])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.47/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/0.99  
% 2.47/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/0.99  
% 2.47/0.99  ------  iProver source info
% 2.47/0.99  
% 2.47/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.47/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/0.99  git: non_committed_changes: false
% 2.47/0.99  git: last_make_outside_of_git: false
% 2.47/0.99  
% 2.47/0.99  ------ 
% 2.47/0.99  
% 2.47/0.99  ------ Input Options
% 2.47/0.99  
% 2.47/0.99  --out_options                           all
% 2.47/0.99  --tptp_safe_out                         true
% 2.47/0.99  --problem_path                          ""
% 2.47/0.99  --include_path                          ""
% 2.47/0.99  --clausifier                            res/vclausify_rel
% 2.47/0.99  --clausifier_options                    --mode clausify
% 2.47/0.99  --stdin                                 false
% 2.47/0.99  --stats_out                             all
% 2.47/0.99  
% 2.47/0.99  ------ General Options
% 2.47/0.99  
% 2.47/0.99  --fof                                   false
% 2.47/0.99  --time_out_real                         305.
% 2.47/0.99  --time_out_virtual                      -1.
% 2.47/0.99  --symbol_type_check                     false
% 2.47/0.99  --clausify_out                          false
% 2.47/0.99  --sig_cnt_out                           false
% 2.47/0.99  --trig_cnt_out                          false
% 2.47/0.99  --trig_cnt_out_tolerance                1.
% 2.47/0.99  --trig_cnt_out_sk_spl                   false
% 2.47/0.99  --abstr_cl_out                          false
% 2.47/0.99  
% 2.47/0.99  ------ Global Options
% 2.47/0.99  
% 2.47/0.99  --schedule                              default
% 2.47/0.99  --add_important_lit                     false
% 2.47/0.99  --prop_solver_per_cl                    1000
% 2.47/0.99  --min_unsat_core                        false
% 2.47/0.99  --soft_assumptions                      false
% 2.47/0.99  --soft_lemma_size                       3
% 2.47/0.99  --prop_impl_unit_size                   0
% 2.47/0.99  --prop_impl_unit                        []
% 2.47/0.99  --share_sel_clauses                     true
% 2.47/0.99  --reset_solvers                         false
% 2.47/0.99  --bc_imp_inh                            [conj_cone]
% 2.47/0.99  --conj_cone_tolerance                   3.
% 2.47/0.99  --extra_neg_conj                        none
% 2.47/0.99  --large_theory_mode                     true
% 2.47/0.99  --prolific_symb_bound                   200
% 2.47/0.99  --lt_threshold                          2000
% 2.47/0.99  --clause_weak_htbl                      true
% 2.47/0.99  --gc_record_bc_elim                     false
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing Options
% 2.47/0.99  
% 2.47/0.99  --preprocessing_flag                    true
% 2.47/0.99  --time_out_prep_mult                    0.1
% 2.47/0.99  --splitting_mode                        input
% 2.47/0.99  --splitting_grd                         true
% 2.47/0.99  --splitting_cvd                         false
% 2.47/0.99  --splitting_cvd_svl                     false
% 2.47/0.99  --splitting_nvd                         32
% 2.47/0.99  --sub_typing                            true
% 2.47/0.99  --prep_gs_sim                           true
% 2.47/0.99  --prep_unflatten                        true
% 2.47/0.99  --prep_res_sim                          true
% 2.47/0.99  --prep_upred                            true
% 2.47/0.99  --prep_sem_filter                       exhaustive
% 2.47/0.99  --prep_sem_filter_out                   false
% 2.47/0.99  --pred_elim                             true
% 2.47/0.99  --res_sim_input                         true
% 2.47/0.99  --eq_ax_congr_red                       true
% 2.47/0.99  --pure_diseq_elim                       true
% 2.47/0.99  --brand_transform                       false
% 2.47/0.99  --non_eq_to_eq                          false
% 2.47/0.99  --prep_def_merge                        true
% 2.47/0.99  --prep_def_merge_prop_impl              false
% 2.47/0.99  --prep_def_merge_mbd                    true
% 2.47/0.99  --prep_def_merge_tr_red                 false
% 2.47/0.99  --prep_def_merge_tr_cl                  false
% 2.47/0.99  --smt_preprocessing                     true
% 2.47/0.99  --smt_ac_axioms                         fast
% 2.47/0.99  --preprocessed_out                      false
% 2.47/0.99  --preprocessed_stats                    false
% 2.47/0.99  
% 2.47/0.99  ------ Abstraction refinement Options
% 2.47/0.99  
% 2.47/0.99  --abstr_ref                             []
% 2.47/0.99  --abstr_ref_prep                        false
% 2.47/0.99  --abstr_ref_until_sat                   false
% 2.47/0.99  --abstr_ref_sig_restrict                funpre
% 2.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.99  --abstr_ref_under                       []
% 2.47/0.99  
% 2.47/0.99  ------ SAT Options
% 2.47/0.99  
% 2.47/0.99  --sat_mode                              false
% 2.47/0.99  --sat_fm_restart_options                ""
% 2.47/0.99  --sat_gr_def                            false
% 2.47/0.99  --sat_epr_types                         true
% 2.47/0.99  --sat_non_cyclic_types                  false
% 2.47/0.99  --sat_finite_models                     false
% 2.47/0.99  --sat_fm_lemmas                         false
% 2.47/0.99  --sat_fm_prep                           false
% 2.47/0.99  --sat_fm_uc_incr                        true
% 2.47/0.99  --sat_out_model                         small
% 2.47/0.99  --sat_out_clauses                       false
% 2.47/0.99  
% 2.47/0.99  ------ QBF Options
% 2.47/0.99  
% 2.47/0.99  --qbf_mode                              false
% 2.47/0.99  --qbf_elim_univ                         false
% 2.47/0.99  --qbf_dom_inst                          none
% 2.47/0.99  --qbf_dom_pre_inst                      false
% 2.47/0.99  --qbf_sk_in                             false
% 2.47/0.99  --qbf_pred_elim                         true
% 2.47/0.99  --qbf_split                             512
% 2.47/0.99  
% 2.47/0.99  ------ BMC1 Options
% 2.47/0.99  
% 2.47/0.99  --bmc1_incremental                      false
% 2.47/0.99  --bmc1_axioms                           reachable_all
% 2.47/0.99  --bmc1_min_bound                        0
% 2.47/0.99  --bmc1_max_bound                        -1
% 2.47/0.99  --bmc1_max_bound_default                -1
% 2.47/0.99  --bmc1_symbol_reachability              true
% 2.47/0.99  --bmc1_property_lemmas                  false
% 2.47/0.99  --bmc1_k_induction                      false
% 2.47/0.99  --bmc1_non_equiv_states                 false
% 2.47/0.99  --bmc1_deadlock                         false
% 2.47/0.99  --bmc1_ucm                              false
% 2.47/0.99  --bmc1_add_unsat_core                   none
% 2.47/0.99  --bmc1_unsat_core_children              false
% 2.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.99  --bmc1_out_stat                         full
% 2.47/0.99  --bmc1_ground_init                      false
% 2.47/0.99  --bmc1_pre_inst_next_state              false
% 2.47/0.99  --bmc1_pre_inst_state                   false
% 2.47/0.99  --bmc1_pre_inst_reach_state             false
% 2.47/0.99  --bmc1_out_unsat_core                   false
% 2.47/0.99  --bmc1_aig_witness_out                  false
% 2.47/0.99  --bmc1_verbose                          false
% 2.47/0.99  --bmc1_dump_clauses_tptp                false
% 2.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.99  --bmc1_dump_file                        -
% 2.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.99  --bmc1_ucm_extend_mode                  1
% 2.47/0.99  --bmc1_ucm_init_mode                    2
% 2.47/0.99  --bmc1_ucm_cone_mode                    none
% 2.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.99  --bmc1_ucm_relax_model                  4
% 2.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.99  --bmc1_ucm_layered_model                none
% 2.47/0.99  --bmc1_ucm_max_lemma_size               10
% 2.47/0.99  
% 2.47/0.99  ------ AIG Options
% 2.47/0.99  
% 2.47/0.99  --aig_mode                              false
% 2.47/0.99  
% 2.47/0.99  ------ Instantiation Options
% 2.47/0.99  
% 2.47/0.99  --instantiation_flag                    true
% 2.47/0.99  --inst_sos_flag                         false
% 2.47/0.99  --inst_sos_phase                        true
% 2.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel_side                     num_symb
% 2.47/0.99  --inst_solver_per_active                1400
% 2.47/0.99  --inst_solver_calls_frac                1.
% 2.47/0.99  --inst_passive_queue_type               priority_queues
% 2.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.99  --inst_passive_queues_freq              [25;2]
% 2.47/0.99  --inst_dismatching                      true
% 2.47/0.99  --inst_eager_unprocessed_to_passive     true
% 2.47/0.99  --inst_prop_sim_given                   true
% 2.47/0.99  --inst_prop_sim_new                     false
% 2.47/0.99  --inst_subs_new                         false
% 2.47/0.99  --inst_eq_res_simp                      false
% 2.47/0.99  --inst_subs_given                       false
% 2.47/0.99  --inst_orphan_elimination               true
% 2.47/0.99  --inst_learning_loop_flag               true
% 2.47/0.99  --inst_learning_start                   3000
% 2.47/0.99  --inst_learning_factor                  2
% 2.47/0.99  --inst_start_prop_sim_after_learn       3
% 2.47/0.99  --inst_sel_renew                        solver
% 2.47/0.99  --inst_lit_activity_flag                true
% 2.47/0.99  --inst_restr_to_given                   false
% 2.47/0.99  --inst_activity_threshold               500
% 2.47/0.99  --inst_out_proof                        true
% 2.47/0.99  
% 2.47/0.99  ------ Resolution Options
% 2.47/0.99  
% 2.47/0.99  --resolution_flag                       true
% 2.47/0.99  --res_lit_sel                           adaptive
% 2.47/0.99  --res_lit_sel_side                      none
% 2.47/0.99  --res_ordering                          kbo
% 2.47/0.99  --res_to_prop_solver                    active
% 2.47/0.99  --res_prop_simpl_new                    false
% 2.47/0.99  --res_prop_simpl_given                  true
% 2.47/0.99  --res_passive_queue_type                priority_queues
% 2.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.99  --res_passive_queues_freq               [15;5]
% 2.47/0.99  --res_forward_subs                      full
% 2.47/0.99  --res_backward_subs                     full
% 2.47/0.99  --res_forward_subs_resolution           true
% 2.47/0.99  --res_backward_subs_resolution          true
% 2.47/0.99  --res_orphan_elimination                true
% 2.47/0.99  --res_time_limit                        2.
% 2.47/0.99  --res_out_proof                         true
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Options
% 2.47/0.99  
% 2.47/0.99  --superposition_flag                    true
% 2.47/0.99  --sup_passive_queue_type                priority_queues
% 2.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.99  --demod_completeness_check              fast
% 2.47/0.99  --demod_use_ground                      true
% 2.47/0.99  --sup_to_prop_solver                    passive
% 2.47/0.99  --sup_prop_simpl_new                    true
% 2.47/0.99  --sup_prop_simpl_given                  true
% 2.47/0.99  --sup_fun_splitting                     false
% 2.47/0.99  --sup_smt_interval                      50000
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Simplification Setup
% 2.47/0.99  
% 2.47/0.99  --sup_indices_passive                   []
% 2.47/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_full_bw                           [BwDemod]
% 2.47/0.99  --sup_immed_triv                        [TrivRules]
% 2.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_immed_bw_main                     []
% 2.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  
% 2.47/0.99  ------ Combination Options
% 2.47/0.99  
% 2.47/0.99  --comb_res_mult                         3
% 2.47/0.99  --comb_sup_mult                         2
% 2.47/0.99  --comb_inst_mult                        10
% 2.47/0.99  
% 2.47/0.99  ------ Debug Options
% 2.47/0.99  
% 2.47/0.99  --dbg_backtrace                         false
% 2.47/0.99  --dbg_dump_prop_clauses                 false
% 2.47/0.99  --dbg_dump_prop_clauses_file            -
% 2.47/0.99  --dbg_out_stat                          false
% 2.47/0.99  ------ Parsing...
% 2.47/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/0.99  ------ Proving...
% 2.47/0.99  ------ Problem Properties 
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  clauses                                 18
% 2.47/0.99  conjectures                             5
% 2.47/0.99  EPR                                     6
% 2.47/0.99  Horn                                    16
% 2.47/0.99  unary                                   9
% 2.47/0.99  binary                                  5
% 2.47/0.99  lits                                    33
% 2.47/0.99  lits eq                                 13
% 2.47/0.99  fd_pure                                 0
% 2.47/0.99  fd_pseudo                               0
% 2.47/0.99  fd_cond                                 1
% 2.47/0.99  fd_pseudo_cond                          2
% 2.47/0.99  AC symbols                              0
% 2.47/0.99  
% 2.47/0.99  ------ Schedule dynamic 5 is on 
% 2.47/0.99  
% 2.47/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  ------ 
% 2.47/0.99  Current options:
% 2.47/0.99  ------ 
% 2.47/0.99  
% 2.47/0.99  ------ Input Options
% 2.47/0.99  
% 2.47/0.99  --out_options                           all
% 2.47/0.99  --tptp_safe_out                         true
% 2.47/0.99  --problem_path                          ""
% 2.47/0.99  --include_path                          ""
% 2.47/0.99  --clausifier                            res/vclausify_rel
% 2.47/0.99  --clausifier_options                    --mode clausify
% 2.47/0.99  --stdin                                 false
% 2.47/0.99  --stats_out                             all
% 2.47/0.99  
% 2.47/0.99  ------ General Options
% 2.47/0.99  
% 2.47/0.99  --fof                                   false
% 2.47/0.99  --time_out_real                         305.
% 2.47/0.99  --time_out_virtual                      -1.
% 2.47/0.99  --symbol_type_check                     false
% 2.47/0.99  --clausify_out                          false
% 2.47/0.99  --sig_cnt_out                           false
% 2.47/0.99  --trig_cnt_out                          false
% 2.47/0.99  --trig_cnt_out_tolerance                1.
% 2.47/0.99  --trig_cnt_out_sk_spl                   false
% 2.47/0.99  --abstr_cl_out                          false
% 2.47/0.99  
% 2.47/0.99  ------ Global Options
% 2.47/0.99  
% 2.47/0.99  --schedule                              default
% 2.47/0.99  --add_important_lit                     false
% 2.47/0.99  --prop_solver_per_cl                    1000
% 2.47/0.99  --min_unsat_core                        false
% 2.47/0.99  --soft_assumptions                      false
% 2.47/0.99  --soft_lemma_size                       3
% 2.47/0.99  --prop_impl_unit_size                   0
% 2.47/0.99  --prop_impl_unit                        []
% 2.47/0.99  --share_sel_clauses                     true
% 2.47/0.99  --reset_solvers                         false
% 2.47/0.99  --bc_imp_inh                            [conj_cone]
% 2.47/0.99  --conj_cone_tolerance                   3.
% 2.47/0.99  --extra_neg_conj                        none
% 2.47/0.99  --large_theory_mode                     true
% 2.47/0.99  --prolific_symb_bound                   200
% 2.47/0.99  --lt_threshold                          2000
% 2.47/0.99  --clause_weak_htbl                      true
% 2.47/0.99  --gc_record_bc_elim                     false
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing Options
% 2.47/0.99  
% 2.47/0.99  --preprocessing_flag                    true
% 2.47/0.99  --time_out_prep_mult                    0.1
% 2.47/0.99  --splitting_mode                        input
% 2.47/0.99  --splitting_grd                         true
% 2.47/0.99  --splitting_cvd                         false
% 2.47/0.99  --splitting_cvd_svl                     false
% 2.47/0.99  --splitting_nvd                         32
% 2.47/0.99  --sub_typing                            true
% 2.47/0.99  --prep_gs_sim                           true
% 2.47/0.99  --prep_unflatten                        true
% 2.47/0.99  --prep_res_sim                          true
% 2.47/0.99  --prep_upred                            true
% 2.47/0.99  --prep_sem_filter                       exhaustive
% 2.47/0.99  --prep_sem_filter_out                   false
% 2.47/0.99  --pred_elim                             true
% 2.47/0.99  --res_sim_input                         true
% 2.47/0.99  --eq_ax_congr_red                       true
% 2.47/0.99  --pure_diseq_elim                       true
% 2.47/0.99  --brand_transform                       false
% 2.47/0.99  --non_eq_to_eq                          false
% 2.47/0.99  --prep_def_merge                        true
% 2.47/0.99  --prep_def_merge_prop_impl              false
% 2.47/0.99  --prep_def_merge_mbd                    true
% 2.47/0.99  --prep_def_merge_tr_red                 false
% 2.47/0.99  --prep_def_merge_tr_cl                  false
% 2.47/0.99  --smt_preprocessing                     true
% 2.47/0.99  --smt_ac_axioms                         fast
% 2.47/0.99  --preprocessed_out                      false
% 2.47/0.99  --preprocessed_stats                    false
% 2.47/0.99  
% 2.47/0.99  ------ Abstraction refinement Options
% 2.47/0.99  
% 2.47/0.99  --abstr_ref                             []
% 2.47/0.99  --abstr_ref_prep                        false
% 2.47/0.99  --abstr_ref_until_sat                   false
% 2.47/0.99  --abstr_ref_sig_restrict                funpre
% 2.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.99  --abstr_ref_under                       []
% 2.47/0.99  
% 2.47/0.99  ------ SAT Options
% 2.47/0.99  
% 2.47/0.99  --sat_mode                              false
% 2.47/0.99  --sat_fm_restart_options                ""
% 2.47/0.99  --sat_gr_def                            false
% 2.47/0.99  --sat_epr_types                         true
% 2.47/0.99  --sat_non_cyclic_types                  false
% 2.47/0.99  --sat_finite_models                     false
% 2.47/0.99  --sat_fm_lemmas                         false
% 2.47/0.99  --sat_fm_prep                           false
% 2.47/0.99  --sat_fm_uc_incr                        true
% 2.47/0.99  --sat_out_model                         small
% 2.47/0.99  --sat_out_clauses                       false
% 2.47/0.99  
% 2.47/0.99  ------ QBF Options
% 2.47/0.99  
% 2.47/0.99  --qbf_mode                              false
% 2.47/0.99  --qbf_elim_univ                         false
% 2.47/0.99  --qbf_dom_inst                          none
% 2.47/0.99  --qbf_dom_pre_inst                      false
% 2.47/0.99  --qbf_sk_in                             false
% 2.47/0.99  --qbf_pred_elim                         true
% 2.47/0.99  --qbf_split                             512
% 2.47/0.99  
% 2.47/0.99  ------ BMC1 Options
% 2.47/0.99  
% 2.47/0.99  --bmc1_incremental                      false
% 2.47/0.99  --bmc1_axioms                           reachable_all
% 2.47/0.99  --bmc1_min_bound                        0
% 2.47/0.99  --bmc1_max_bound                        -1
% 2.47/0.99  --bmc1_max_bound_default                -1
% 2.47/0.99  --bmc1_symbol_reachability              true
% 2.47/0.99  --bmc1_property_lemmas                  false
% 2.47/0.99  --bmc1_k_induction                      false
% 2.47/0.99  --bmc1_non_equiv_states                 false
% 2.47/0.99  --bmc1_deadlock                         false
% 2.47/0.99  --bmc1_ucm                              false
% 2.47/0.99  --bmc1_add_unsat_core                   none
% 2.47/0.99  --bmc1_unsat_core_children              false
% 2.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.99  --bmc1_out_stat                         full
% 2.47/0.99  --bmc1_ground_init                      false
% 2.47/0.99  --bmc1_pre_inst_next_state              false
% 2.47/0.99  --bmc1_pre_inst_state                   false
% 2.47/0.99  --bmc1_pre_inst_reach_state             false
% 2.47/0.99  --bmc1_out_unsat_core                   false
% 2.47/0.99  --bmc1_aig_witness_out                  false
% 2.47/0.99  --bmc1_verbose                          false
% 2.47/0.99  --bmc1_dump_clauses_tptp                false
% 2.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.99  --bmc1_dump_file                        -
% 2.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.99  --bmc1_ucm_extend_mode                  1
% 2.47/0.99  --bmc1_ucm_init_mode                    2
% 2.47/0.99  --bmc1_ucm_cone_mode                    none
% 2.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.99  --bmc1_ucm_relax_model                  4
% 2.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.99  --bmc1_ucm_layered_model                none
% 2.47/0.99  --bmc1_ucm_max_lemma_size               10
% 2.47/0.99  
% 2.47/0.99  ------ AIG Options
% 2.47/0.99  
% 2.47/0.99  --aig_mode                              false
% 2.47/0.99  
% 2.47/0.99  ------ Instantiation Options
% 2.47/0.99  
% 2.47/0.99  --instantiation_flag                    true
% 2.47/0.99  --inst_sos_flag                         false
% 2.47/0.99  --inst_sos_phase                        true
% 2.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel_side                     none
% 2.47/0.99  --inst_solver_per_active                1400
% 2.47/0.99  --inst_solver_calls_frac                1.
% 2.47/0.99  --inst_passive_queue_type               priority_queues
% 2.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.99  --inst_passive_queues_freq              [25;2]
% 2.47/0.99  --inst_dismatching                      true
% 2.47/0.99  --inst_eager_unprocessed_to_passive     true
% 2.47/0.99  --inst_prop_sim_given                   true
% 2.47/0.99  --inst_prop_sim_new                     false
% 2.47/0.99  --inst_subs_new                         false
% 2.47/0.99  --inst_eq_res_simp                      false
% 2.47/0.99  --inst_subs_given                       false
% 2.47/0.99  --inst_orphan_elimination               true
% 2.47/0.99  --inst_learning_loop_flag               true
% 2.47/0.99  --inst_learning_start                   3000
% 2.47/0.99  --inst_learning_factor                  2
% 2.47/0.99  --inst_start_prop_sim_after_learn       3
% 2.47/0.99  --inst_sel_renew                        solver
% 2.47/0.99  --inst_lit_activity_flag                true
% 2.47/0.99  --inst_restr_to_given                   false
% 2.47/0.99  --inst_activity_threshold               500
% 2.47/0.99  --inst_out_proof                        true
% 2.47/0.99  
% 2.47/0.99  ------ Resolution Options
% 2.47/0.99  
% 2.47/0.99  --resolution_flag                       false
% 2.47/0.99  --res_lit_sel                           adaptive
% 2.47/0.99  --res_lit_sel_side                      none
% 2.47/0.99  --res_ordering                          kbo
% 2.47/0.99  --res_to_prop_solver                    active
% 2.47/0.99  --res_prop_simpl_new                    false
% 2.47/0.99  --res_prop_simpl_given                  true
% 2.47/0.99  --res_passive_queue_type                priority_queues
% 2.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.99  --res_passive_queues_freq               [15;5]
% 2.47/0.99  --res_forward_subs                      full
% 2.47/0.99  --res_backward_subs                     full
% 2.47/0.99  --res_forward_subs_resolution           true
% 2.47/0.99  --res_backward_subs_resolution          true
% 2.47/0.99  --res_orphan_elimination                true
% 2.47/0.99  --res_time_limit                        2.
% 2.47/0.99  --res_out_proof                         true
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Options
% 2.47/0.99  
% 2.47/0.99  --superposition_flag                    true
% 2.47/0.99  --sup_passive_queue_type                priority_queues
% 2.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.99  --demod_completeness_check              fast
% 2.47/0.99  --demod_use_ground                      true
% 2.47/0.99  --sup_to_prop_solver                    passive
% 2.47/0.99  --sup_prop_simpl_new                    true
% 2.47/0.99  --sup_prop_simpl_given                  true
% 2.47/0.99  --sup_fun_splitting                     false
% 2.47/0.99  --sup_smt_interval                      50000
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Simplification Setup
% 2.47/0.99  
% 2.47/0.99  --sup_indices_passive                   []
% 2.47/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_full_bw                           [BwDemod]
% 2.47/0.99  --sup_immed_triv                        [TrivRules]
% 2.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_immed_bw_main                     []
% 2.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  
% 2.47/0.99  ------ Combination Options
% 2.47/0.99  
% 2.47/0.99  --comb_res_mult                         3
% 2.47/0.99  --comb_sup_mult                         2
% 2.47/0.99  --comb_inst_mult                        10
% 2.47/0.99  
% 2.47/0.99  ------ Debug Options
% 2.47/0.99  
% 2.47/0.99  --dbg_backtrace                         false
% 2.47/0.99  --dbg_dump_prop_clauses                 false
% 2.47/0.99  --dbg_dump_prop_clauses_file            -
% 2.47/0.99  --dbg_out_stat                          false
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  ------ Proving...
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  % SZS status Theorem for theBenchmark.p
% 2.47/0.99  
% 2.47/0.99   Resolution empty clause
% 2.47/0.99  
% 2.47/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/0.99  
% 2.47/0.99  fof(f10,conjecture,(
% 2.47/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f11,negated_conjecture,(
% 2.47/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.47/0.99    inference(negated_conjecture,[],[f10])).
% 2.47/0.99  
% 2.47/0.99  fof(f19,plain,(
% 2.47/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.47/0.99    inference(ennf_transformation,[],[f11])).
% 2.47/0.99  
% 2.47/0.99  fof(f20,plain,(
% 2.47/0.99    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.47/0.99    inference(flattening,[],[f19])).
% 2.47/0.99  
% 2.47/0.99  fof(f31,plain,(
% 2.47/0.99    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.47/0.99    introduced(choice_axiom,[])).
% 2.47/0.99  
% 2.47/0.99  fof(f30,plain,(
% 2.47/0.99    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.47/0.99    introduced(choice_axiom,[])).
% 2.47/0.99  
% 2.47/0.99  fof(f32,plain,(
% 2.47/0.99    (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f31,f30])).
% 2.47/0.99  
% 2.47/0.99  fof(f56,plain,(
% 2.47/0.99    r2_hidden(sK5,sK2)),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f9,axiom,(
% 2.47/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f17,plain,(
% 2.47/0.99    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.47/0.99    inference(ennf_transformation,[],[f9])).
% 2.47/0.99  
% 2.47/0.99  fof(f18,plain,(
% 2.47/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.47/0.99    inference(flattening,[],[f17])).
% 2.47/0.99  
% 2.47/0.99  fof(f50,plain,(
% 2.47/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f18])).
% 2.47/0.99  
% 2.47/0.99  fof(f52,plain,(
% 2.47/0.99    v1_funct_2(sK3,sK2,sK2)),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f51,plain,(
% 2.47/0.99    v1_funct_1(sK3)),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f53,plain,(
% 2.47/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f54,plain,(
% 2.47/0.99    v2_funct_1(sK3)),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f57,plain,(
% 2.47/0.99    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f55,plain,(
% 2.47/0.99    r2_hidden(sK4,sK2)),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f7,axiom,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f15,plain,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.99    inference(ennf_transformation,[],[f7])).
% 2.47/0.99  
% 2.47/0.99  fof(f48,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f15])).
% 2.47/0.99  
% 2.47/0.99  fof(f4,axiom,(
% 2.47/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f25,plain,(
% 2.47/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.47/0.99    inference(nnf_transformation,[],[f4])).
% 2.47/0.99  
% 2.47/0.99  fof(f40,plain,(
% 2.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f25])).
% 2.47/0.99  
% 2.47/0.99  fof(f8,axiom,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f16,plain,(
% 2.47/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.99    inference(ennf_transformation,[],[f8])).
% 2.47/0.99  
% 2.47/0.99  fof(f49,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f16])).
% 2.47/0.99  
% 2.47/0.99  fof(f1,axiom,(
% 2.47/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f21,plain,(
% 2.47/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.47/0.99    inference(nnf_transformation,[],[f1])).
% 2.47/0.99  
% 2.47/0.99  fof(f22,plain,(
% 2.47/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.47/0.99    inference(flattening,[],[f21])).
% 2.47/0.99  
% 2.47/0.99  fof(f35,plain,(
% 2.47/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f22])).
% 2.47/0.99  
% 2.47/0.99  fof(f58,plain,(
% 2.47/0.99    sK4 != sK5),
% 2.47/0.99    inference(cnf_transformation,[],[f32])).
% 2.47/0.99  
% 2.47/0.99  fof(f5,axiom,(
% 2.47/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f12,plain,(
% 2.47/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f5])).
% 2.47/0.99  
% 2.47/0.99  fof(f13,plain,(
% 2.47/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.47/0.99    inference(flattening,[],[f12])).
% 2.47/0.99  
% 2.47/0.99  fof(f26,plain,(
% 2.47/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.47/0.99    inference(nnf_transformation,[],[f13])).
% 2.47/0.99  
% 2.47/0.99  fof(f27,plain,(
% 2.47/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.47/0.99    inference(rectify,[],[f26])).
% 2.47/0.99  
% 2.47/0.99  fof(f28,plain,(
% 2.47/0.99    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.47/0.99    introduced(choice_axiom,[])).
% 2.47/0.99  
% 2.47/0.99  fof(f29,plain,(
% 2.47/0.99    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 2.47/0.99  
% 2.47/0.99  fof(f42,plain,(
% 2.47/0.99    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f29])).
% 2.47/0.99  
% 2.47/0.99  fof(f6,axiom,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f14,plain,(
% 2.47/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.99    inference(ennf_transformation,[],[f6])).
% 2.47/0.99  
% 2.47/0.99  fof(f47,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f14])).
% 2.47/0.99  
% 2.47/0.99  fof(f2,axiom,(
% 2.47/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f36,plain,(
% 2.47/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f2])).
% 2.47/0.99  
% 2.47/0.99  cnf(c_20,negated_conjecture,
% 2.47/0.99      ( r2_hidden(sK5,sK2) ),
% 2.47/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_913,plain,
% 2.47/0.99      ( r2_hidden(sK5,sK2) = iProver_top ),
% 2.47/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_17,plain,
% 2.47/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.47/0.99      | ~ r2_hidden(X3,X1)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/0.99      | ~ v1_funct_1(X0)
% 2.47/0.99      | ~ v2_funct_1(X0)
% 2.47/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.47/0.99      | k1_xboole_0 = X2 ),
% 2.47/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_24,negated_conjecture,
% 2.47/0.99      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.47/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_285,plain,
% 2.47/0.99      ( ~ r2_hidden(X0,X1)
% 2.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.47/0.99      | ~ v1_funct_1(X2)
% 2.47/0.99      | ~ v2_funct_1(X2)
% 2.47/0.99      | k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X0)) = X0
% 2.47/0.99      | sK2 != X3
% 2.47/0.99      | sK2 != X1
% 2.47/0.99      | sK3 != X2
% 2.47/0.99      | k1_xboole_0 = X3 ),
% 2.47/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_286,plain,
% 2.47/0.99      ( ~ r2_hidden(X0,sK2)
% 2.47/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.47/0.99      | ~ v1_funct_1(sK3)
% 2.47/0.99      | ~ v2_funct_1(sK3)
% 2.47/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.47/0.99      | k1_xboole_0 = sK2 ),
% 2.47/0.99      inference(unflattening,[status(thm)],[c_285]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_25,negated_conjecture,
% 2.47/0.99      ( v1_funct_1(sK3) ),
% 2.47/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_23,negated_conjecture,
% 2.47/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.47/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_22,negated_conjecture,
% 2.47/0.99      ( v2_funct_1(sK3) ),
% 2.47/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_290,plain,
% 2.47/0.99      ( ~ r2_hidden(X0,sK2)
% 2.47/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.47/0.99      | k1_xboole_0 = sK2 ),
% 2.47/0.99      inference(global_propositional_subsumption,
% 2.47/0.99                [status(thm)],
% 2.47/0.99                [c_286,c_25,c_23,c_22]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_910,plain,
% 2.47/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.47/0.99      | k1_xboole_0 = sK2
% 2.47/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 2.47/0.99      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1262,plain,
% 2.47/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.47/0.99      | sK2 = k1_xboole_0 ),
% 2.47/0.99      inference(superposition,[status(thm)],[c_913,c_910]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_19,negated_conjecture,
% 2.47/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.47/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1270,plain,
% 2.47/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.47/0.99      | sK2 = k1_xboole_0 ),
% 2.47/0.99      inference(light_normalisation,[status(thm)],[c_1262,c_19]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_21,negated_conjecture,
% 2.47/0.99      ( r2_hidden(sK4,sK2) ),
% 2.47/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_912,plain,
% 2.47/0.99      ( r2_hidden(sK4,sK2) = iProver_top ),
% 2.47/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1263,plain,
% 2.47/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.47/0.99      | sK2 = k1_xboole_0 ),
% 2.47/0.99      inference(superposition,[status(thm)],[c_912,c_910]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1501,plain,
% 2.47/0.99      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 2.47/0.99      inference(superposition,[status(thm)],[c_1270,c_1263]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_911,plain,
% 2.47/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.47/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_15,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.47/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_915,plain,
% 2.47/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.47/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.47/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_917,plain,
% 2.47/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.47/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1694,plain,
% 2.47/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.47/1.00      | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_915,c_917]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2205,plain,
% 2.47/1.00      ( r1_tarski(k1_relset_1(sK2,sK2,sK3),sK2) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_911,c_1694]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_16,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_914,plain,
% 2.47/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.47/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2370,plain,
% 2.47/1.00      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_911,c_914]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2517,plain,
% 2.47/1.00      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 2.47/1.00      inference(light_normalisation,[status(thm)],[c_2205,c_2370]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_0,plain,
% 2.47/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.47/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_921,plain,
% 2.47/1.00      ( X0 = X1
% 2.47/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.47/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2964,plain,
% 2.47/1.00      ( k1_relat_1(sK3) = sK2 | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2517,c_921]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_18,negated_conjecture,
% 2.47/1.00      ( sK4 != sK5 ),
% 2.47/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_532,plain,( X0 = X0 ),theory(equality) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1136,plain,
% 2.47/1.00      ( sK5 = sK5 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_532]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_13,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.47/1.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.47/1.00      | ~ v1_relat_1(X1)
% 2.47/1.00      | ~ v1_funct_1(X1)
% 2.47/1.00      | ~ v2_funct_1(X1)
% 2.47/1.00      | X0 = X2
% 2.47/1.00      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.47/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_318,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.47/1.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.47/1.00      | ~ v1_relat_1(X1)
% 2.47/1.00      | ~ v2_funct_1(X1)
% 2.47/1.00      | X2 = X0
% 2.47/1.00      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.47/1.00      | sK3 != X1 ),
% 2.47/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_319,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.47/1.00      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.47/1.00      | ~ v1_relat_1(sK3)
% 2.47/1.00      | ~ v2_funct_1(sK3)
% 2.47/1.00      | X0 = X1
% 2.47/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.47/1.00      inference(unflattening,[status(thm)],[c_318]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_323,plain,
% 2.47/1.00      ( ~ v1_relat_1(sK3)
% 2.47/1.00      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.47/1.00      | ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.47/1.00      | X0 = X1
% 2.47/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.47/1.00      inference(global_propositional_subsumption,[status(thm)],[c_319,c_22]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_324,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.47/1.00      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.47/1.00      | ~ v1_relat_1(sK3)
% 2.47/1.00      | X0 = X1
% 2.47/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_323]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_909,plain,
% 2.47/1.00      ( X0 = X1
% 2.47/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.47/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_28,plain,
% 2.47/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_325,plain,
% 2.47/1.00      ( X0 = X1
% 2.47/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.47/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_14,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1034,plain,
% 2.47/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.47/1.00      | v1_relat_1(sK3) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1035,plain,
% 2.47/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.47/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1073,plain,
% 2.47/1.00      ( r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.47/1.00      | X0 = X1 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_909,c_28,c_325,c_1035]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1074,plain,
% 2.47/1.00      ( X0 = X1
% 2.47/1.00      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
% 2.47/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_1073]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1081,plain,
% 2.47/1.00      ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK4)
% 2.47/1.00      | sK5 = X0
% 2.47/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_19,c_1074]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1149,plain,
% 2.47/1.00      ( sK5 = sK4
% 2.47/1.00      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 2.47/1.00      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(equality_resolution,[status(thm)],[c_1081]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1156,plain,
% 2.47/1.00      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
% 2.47/1.00      | ~ r2_hidden(sK4,k1_relat_1(sK3))
% 2.47/1.00      | sK5 = sK4 ),
% 2.47/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1149]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1179,plain,
% 2.47/1.00      ( sK4 = sK4 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_532]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_541,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.47/1.00      theory(equality) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1060,plain,
% 2.47/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(sK5,sK2) | X1 != sK2 | X0 != sK5 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_541]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1135,plain,
% 2.47/1.00      ( r2_hidden(sK5,X0) | ~ r2_hidden(sK5,sK2) | X0 != sK2 | sK5 != sK5 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1060]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1583,plain,
% 2.47/1.00      ( r2_hidden(sK5,k1_relat_1(sK3))
% 2.47/1.00      | ~ r2_hidden(sK5,sK2)
% 2.47/1.00      | k1_relat_1(sK3) != sK2
% 2.47/1.00      | sK5 != sK5 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1135]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1065,plain,
% 2.47/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(sK4,sK2) | X1 != sK2 | X0 != sK4 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_541]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1178,plain,
% 2.47/1.00      ( r2_hidden(sK4,X0) | ~ r2_hidden(sK4,sK2) | X0 != sK2 | sK4 != sK4 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1065]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1604,plain,
% 2.47/1.00      ( r2_hidden(sK4,k1_relat_1(sK3))
% 2.47/1.00      | ~ r2_hidden(sK4,sK2)
% 2.47/1.00      | k1_relat_1(sK3) != sK2
% 2.47/1.00      | sK4 != sK4 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1178]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1274,plain,
% 2.47/1.00      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1829,plain,
% 2.47/1.00      ( ~ r1_tarski(k1_relat_1(sK3),sK2)
% 2.47/1.00      | ~ r1_tarski(sK2,k1_relat_1(sK3))
% 2.47/1.00      | k1_relat_1(sK3) = sK2 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1274]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1830,plain,
% 2.47/1.00      ( k1_relat_1(sK3) = sK2
% 2.47/1.00      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 2.47/1.00      | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1829]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_533,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1040,plain,
% 2.47/1.00      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_533]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2265,plain,
% 2.47/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1040]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3506,plain,
% 2.47/1.00      ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_2964,c_21,c_20,c_18,c_1136,c_1156,c_1179,c_1583,c_1604,
% 2.47/1.00                 c_1830,c_2265,c_2517]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3511,plain,
% 2.47/1.00      ( sK5 = sK4 | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1501,c_3506]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3514,plain,
% 2.47/1.00      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3511,c_21,c_20,c_18,c_1136,c_1156,c_1179,c_1501,c_1583,
% 2.47/1.00                 c_1604,c_1872,c_2265,c_2967]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3,plain,
% 2.47/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_919,plain,
% 2.47/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3519,plain,
% 2.47/1.00      ( $false ),
% 2.47/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3514,c_919]) ).
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  ------                               Statistics
% 2.47/1.00  
% 2.47/1.00  ------ General
% 2.47/1.00  
% 2.47/1.00  abstr_ref_over_cycles:                  0
% 2.47/1.00  abstr_ref_under_cycles:                 0
% 2.47/1.00  gc_basic_clause_elim:                   0
% 2.47/1.00  forced_gc_time:                         0
% 2.47/1.00  parsing_time:                           0.012
% 2.47/1.00  unif_index_cands_time:                  0.
% 2.47/1.00  unif_index_add_time:                    0.
% 2.47/1.00  orderings_time:                         0.
% 2.47/1.00  out_proof_time:                         0.008
% 2.47/1.00  total_time:                             0.146
% 2.47/1.00  num_of_symbols:                         51
% 2.47/1.00  num_of_terms:                           3003
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing
% 2.47/1.00  
% 2.47/1.00  num_of_splits:                          0
% 2.47/1.00  num_of_split_atoms:                     0
% 2.47/1.00  num_of_reused_defs:                     0
% 2.47/1.00  num_eq_ax_congr_red:                    17
% 2.47/1.00  num_of_sem_filtered_clauses:            1
% 2.47/1.00  num_of_subtypes:                        0
% 2.47/1.00  monotx_restored_types:                  0
% 2.47/1.00  sat_num_of_epr_types:                   0
% 2.47/1.00  sat_num_of_non_cyclic_types:            0
% 2.47/1.00  sat_guarded_non_collapsed_types:        0
% 2.47/1.00  num_pure_diseq_elim:                    0
% 2.47/1.00  simp_replaced_by:                       0
% 2.47/1.00  res_preprocessed:                       102
% 2.47/1.00  prep_upred:                             0
% 2.47/1.00  prep_unflattend:                        10
% 2.47/1.00  smt_new_axioms:                         0
% 2.47/1.00  pred_elim_cands:                        4
% 2.47/1.00  pred_elim:                              3
% 2.47/1.00  pred_elim_cl:                           7
% 2.47/1.00  pred_elim_cycles:                       5
% 2.47/1.00  merged_defs:                            8
% 2.47/1.00  merged_defs_ncl:                        0
% 2.47/1.00  bin_hyper_res:                          8
% 2.47/1.00  prep_cycles:                            4
% 2.47/1.00  pred_elim_time:                         0.001
% 2.47/1.00  splitting_time:                         0.
% 2.47/1.00  sem_filter_time:                        0.
% 2.47/1.00  monotx_time:                            0.
% 2.47/1.00  subtype_inf_time:                       0.
% 2.47/1.00  
% 2.47/1.00  ------ Problem properties
% 2.47/1.00  
% 2.47/1.00  clauses:                                18
% 2.47/1.00  conjectures:                            5
% 2.47/1.00  epr:                                    6
% 2.47/1.00  horn:                                   16
% 2.47/1.00  ground:                                 5
% 2.47/1.00  unary:                                  9
% 2.47/1.00  binary:                                 5
% 2.47/1.00  lits:                                   33
% 2.47/1.00  lits_eq:                                13
% 2.47/1.00  fd_pure:                                0
% 2.47/1.00  fd_pseudo:                              0
% 2.47/1.00  fd_cond:                                1
% 2.47/1.00  fd_pseudo_cond:                         2
% 2.47/1.00  ac_symbols:                             0
% 2.47/1.00  
% 2.47/1.00  ------ Propositional Solver
% 2.47/1.00  
% 2.47/1.00  prop_solver_calls:                      28
% 2.47/1.00  prop_fast_solver_calls:                 579
% 2.47/1.00  smt_solver_calls:                       0
% 2.47/1.00  smt_fast_solver_calls:                  0
% 2.47/1.00  prop_num_of_clauses:                    1301
% 2.47/1.00  prop_preprocess_simplified:             3948
% 2.47/1.00  prop_fo_subsumed:                       12
% 2.47/1.00  prop_solver_time:                       0.
% 2.47/1.00  smt_solver_time:                        0.
% 2.47/1.00  smt_fast_solver_time:                   0.
% 2.47/1.00  prop_fast_solver_time:                  0.
% 2.47/1.00  prop_unsat_core_time:                   0.
% 2.47/1.00  
% 2.47/1.00  ------ QBF
% 2.47/1.00  
% 2.47/1.00  qbf_q_res:                              0
% 2.47/1.00  qbf_num_tautologies:                    0
% 2.47/1.00  qbf_prep_cycles:                        0
% 2.47/1.00  
% 2.47/1.00  ------ BMC1
% 2.47/1.00  
% 2.47/1.00  bmc1_current_bound:                     -1
% 2.47/1.00  bmc1_last_solved_bound:                 -1
% 2.47/1.00  bmc1_unsat_core_size:                   -1
% 2.47/1.00  bmc1_unsat_core_parents_size:           -1
% 2.47/1.00  bmc1_merge_next_fun:                    0
% 2.47/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation
% 2.47/1.00  
% 2.47/1.00  inst_num_of_clauses:                    468
% 2.47/1.00  inst_num_in_passive:                    23
% 2.47/1.00  inst_num_in_active:                     233
% 2.47/1.00  inst_num_in_unprocessed:                212
% 2.47/1.00  inst_num_of_loops:                      270
% 2.47/1.00  inst_num_of_learning_restarts:          0
% 2.47/1.00  inst_num_moves_active_passive:          34
% 2.47/1.00  inst_lit_activity:                      0
% 2.47/1.00  inst_lit_activity_moves:                0
% 2.47/1.00  inst_num_tautologies:                   0
% 2.47/1.00  inst_num_prop_implied:                  0
% 2.47/1.00  inst_num_existing_simplified:           0
% 2.47/1.00  inst_num_eq_res_simplified:             0
% 2.47/1.00  inst_num_child_elim:                    0
% 2.47/1.00  inst_num_of_dismatching_blockings:      99
% 2.47/1.00  inst_num_of_non_proper_insts:           374
% 2.47/1.00  inst_num_of_duplicates:                 0
% 2.47/1.00  inst_inst_num_from_inst_to_res:         0
% 2.47/1.00  inst_dismatching_checking_time:         0.
% 2.47/1.00  
% 2.47/1.00  ------ Resolution
% 2.47/1.00  
% 2.47/1.00  res_num_of_clauses:                     0
% 2.47/1.00  res_num_in_passive:                     0
% 2.47/1.00  res_num_in_active:                      0
% 2.47/1.00  res_num_of_loops:                       106
% 2.47/1.00  res_forward_subset_subsumed:            43
% 2.47/1.00  res_backward_subset_subsumed:           0
% 2.47/1.00  res_forward_subsumed:                   0
% 2.47/1.00  res_backward_subsumed:                  0
% 2.47/1.00  res_forward_subsumption_resolution:     0
% 2.47/1.00  res_backward_subsumption_resolution:    0
% 2.47/1.00  res_clause_to_clause_subsumption:       193
% 2.47/1.00  res_orphan_elimination:                 0
% 2.47/1.00  res_tautology_del:                      42
% 2.47/1.00  res_num_eq_res_simplified:              0
% 2.47/1.00  res_num_sel_changes:                    0
% 2.47/1.00  res_moves_from_active_to_pass:          0
% 2.47/1.00  
% 2.47/1.00  ------ Superposition
% 2.47/1.00  
% 2.47/1.00  sup_time_total:                         0.
% 2.47/1.00  sup_time_generating:                    0.
% 2.47/1.00  sup_time_sim_full:                      0.
% 2.47/1.00  sup_time_sim_immed:                     0.
% 2.47/1.00  
% 2.47/1.00  sup_num_of_clauses:                     81
% 2.47/1.00  sup_num_in_active:                      53
% 2.47/1.00  sup_num_in_passive:                     28
% 2.47/1.00  sup_num_of_loops:                       53
% 2.47/1.00  sup_fw_superposition:                   72
% 2.47/1.00  sup_bw_superposition:                   28
% 2.47/1.00  sup_immediate_simplified:               19
% 2.47/1.00  sup_given_eliminated:                   0
% 2.47/1.00  comparisons_done:                       0
% 2.47/1.00  comparisons_avoided:                    10
% 2.47/1.00  
% 2.47/1.00  ------ Simplifications
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  sim_fw_subset_subsumed:                 4
% 2.47/1.00  sim_bw_subset_subsumed:                 1
% 2.47/1.00  sim_fw_subsumed:                        2
% 2.47/1.00  sim_bw_subsumed:                        0
% 2.47/1.00  sim_fw_subsumption_res:                 1
% 2.47/1.00  sim_bw_subsumption_res:                 0
% 2.47/1.00  sim_tautology_del:                      1
% 2.47/1.00  sim_eq_tautology_del:                   4
% 2.47/1.00  sim_eq_res_simp:                        0
% 2.47/1.00  sim_fw_demodulated:                     10
% 2.47/1.00  sim_bw_demodulated:                     0
% 2.47/1.00  sim_light_normalised:                   4
% 2.47/1.00  sim_joinable_taut:                      0
% 2.47/1.00  sim_joinable_simp:                      0
% 2.47/1.00  sim_ac_normalised:                      0
% 2.47/1.00  sim_smt_subsumption:                    0
% 2.47/1.00  
%------------------------------------------------------------------------------
