%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:33 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1796)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f48])).

fof(f83,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f92])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_554,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_556,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_35])).

cnf(c_1454,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1459,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3474,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1454,c_1459])).

cnf(c_3656,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_556,c_3474])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1468,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_1451,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_1795,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1451])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1467,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4079,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1467])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2322,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1463])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_321,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_259])).

cnf(c_1453,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_2337,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1453])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1462,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2402,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2337,c_1462])).

cnf(c_4371,plain,
    ( r2_hidden(X0,sK1) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_2402])).

cnf(c_4372,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_4371])).

cnf(c_4379,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r2_hidden(sK0(k1_relat_1(sK4),X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_4372])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1469,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5937,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4379,c_1469])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1458,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3219,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1454,c_1458])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1455,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3615,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3219,c_1455])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1457,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3472,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1457,c_1459])).

cnf(c_11579,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3615,c_3472])).

cnf(c_12387,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11579,c_2402])).

cnf(c_12388,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12387])).

cnf(c_12397,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5937,c_12388])).

cnf(c_29,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_185,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_37])).

cnf(c_186,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_186])).

cnf(c_541,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_1446,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_12740,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12397,c_1446])).

cnf(c_2647,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2649,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_12953,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12740,c_1796,c_2403,c_2647,c_3623,c_12741])).

cnf(c_12954,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_12953])).

cnf(c_12957,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3656,c_12954])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1466,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3949,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK4
    | r1_tarski(k2_zfmisc_1(sK1,sK2),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1466])).

cnf(c_13775,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK4
    | sK3 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12957,c_3949])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_13809,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK4
    | sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13775,c_8])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_100,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_103,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_186])).

cnf(c_512,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_513,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_564,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK2 != sK3
    | sK1 != sK1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_186,c_36])).

cnf(c_565,plain,
    ( sK2 != sK3
    | sK1 != sK1
    | sK4 != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_843,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1707,plain,
    ( sK2 != X0
    | sK2 = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1708,plain,
    ( sK2 = sK3
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_842,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1789,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2024,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2025,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_2403,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2402])).

cnf(c_2799,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2800,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2799])).

cnf(c_2802,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2800])).

cnf(c_2805,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_4239,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4241,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4239])).

cnf(c_4240,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4239])).

cnf(c_4242,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4240])).

cnf(c_2678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1457])).

cnf(c_4553,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_2678])).

cnf(c_4850,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4553,c_2402])).

cnf(c_4851,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4850])).

cnf(c_4852,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4851])).

cnf(c_4163,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != X0
    | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_7367,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_relat_1(sK4)
    | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4163])).

cnf(c_1464,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2663,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1451])).

cnf(c_5535,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2663])).

cnf(c_20,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1457])).

cnf(c_4600,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2679])).

cnf(c_19,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4617,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4600,c_19])).

cnf(c_25,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1456,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2321,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1463])).

cnf(c_2594,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1453])).

cnf(c_2962,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2594,c_1462])).

cnf(c_4806,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4617,c_2962])).

cnf(c_4807,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4806])).

cnf(c_4816,plain,
    ( m1_subset_1(k6_relat_1(k1_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_4807])).

cnf(c_5230,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(k6_relat_1(k1_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4816,c_2402])).

cnf(c_5231,plain,
    ( m1_subset_1(k6_relat_1(k1_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5230])).

cnf(c_5236,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3656,c_5231])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_542,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_1706,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1788,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_2220,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2221,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2220])).

cnf(c_1929,plain,
    ( k1_relset_1(sK1,sK3,sK4) != X0
    | k1_relset_1(sK1,sK3,sK4) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_2223,plain,
    ( k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
    | k1_relset_1(sK1,sK3,sK4) = sK1
    | sK1 != k1_relset_1(sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_2224,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relset_1(sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2422,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_2423,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_1785,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2755,plain,
    ( ~ r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1)
    | ~ r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4))
    | sK1 = k1_relset_1(sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_2756,plain,
    ( sK1 = k1_relset_1(sK1,sK3,sK4)
    | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1) != iProver_top
    | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2755])).

cnf(c_2759,plain,
    ( r1_tarski(X0,k1_relset_1(sK1,sK3,sK4))
    | r2_hidden(sK0(X0,k1_relset_1(sK1,sK3,sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2765,plain,
    ( r1_tarski(X0,k1_relset_1(sK1,sK3,sK4)) = iProver_top
    | r2_hidden(sK0(X0,k1_relset_1(sK1,sK3,sK4)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2759])).

cnf(c_2767,plain,
    ( r1_tarski(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_2896,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2587,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_3864,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2587])).

cnf(c_845,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2149,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1)
    | k1_relset_1(sK1,sK3,sK4) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_4176,plain,
    ( r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1)
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_4178,plain,
    ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
    | sK1 != X0
    | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4176])).

cnf(c_4180,plain,
    ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
    | sK1 != k1_xboole_0
    | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4178])).

cnf(c_2522,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4))
    | k1_relset_1(sK1,sK3,sK4) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_4209,plain,
    ( ~ r1_tarski(X0,k1_relset_1(sK1,sK3,sK4))
    | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4))
    | k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2522])).

cnf(c_4210,plain,
    ( k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
    | sK1 != X0
    | r1_tarski(X0,k1_relset_1(sK1,sK3,sK4)) != iProver_top
    | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4209])).

cnf(c_4212,plain,
    ( k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
    | sK1 != k1_xboole_0
    | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4210])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_430,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_431,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_4693,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_4696,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4693])).

cnf(c_5292,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5236,c_33,c_100,c_101,c_542,c_636,c_1708,c_1788,c_1789,c_1795,c_2221,c_2223,c_2224,c_2402,c_2423,c_2649,c_2756,c_2767,c_2896,c_3615,c_3864,c_4180,c_4212,c_4696])).

cnf(c_1798,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1451])).

cnf(c_5299,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK1)),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5292,c_1798])).

cnf(c_5327,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top
    | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5299,c_20])).

cnf(c_7688,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5327,c_2962])).

cnf(c_7852,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5535,c_7688])).

cnf(c_7965,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7852])).

cnf(c_5238,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(sK4))),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5231,c_1798])).

cnf(c_5266,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5238,c_20])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1465,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4602,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3656,c_2679])).

cnf(c_5407,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4602,c_2402])).

cnf(c_5408,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5407])).

cnf(c_5417,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_5408])).

cnf(c_6062,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5417,c_1798])).

cnf(c_7690,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7688])).

cnf(c_8081,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5266,c_33,c_100,c_101,c_542,c_636,c_1708,c_1788,c_1789,c_1795,c_2221,c_2223,c_2224,c_2402,c_2423,c_2649,c_2756,c_2767,c_2896,c_3615,c_3864,c_4180,c_4212,c_4696,c_6062,c_7690])).

cnf(c_8082,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8081])).

cnf(c_8087,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5535,c_8082])).

cnf(c_8102,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8087])).

cnf(c_8101,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | ~ r1_tarski(sK4,k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8087])).

cnf(c_8103,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0)
    | ~ r1_tarski(sK4,k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8101])).

cnf(c_1452,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_2793,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1452])).

cnf(c_8088,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3656,c_8082])).

cnf(c_8199,plain,
    ( k1_relat_1(sK4) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8088,c_1466])).

cnf(c_9280,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_8199])).

cnf(c_9682,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(sK4))
    | X2 != X0
    | k1_relat_1(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_9684,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK4))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9682])).

cnf(c_12398,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5535,c_12388])).

cnf(c_13783,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12957,c_33])).

cnf(c_13778,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12957,c_2322])).

cnf(c_13795,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13778,c_8])).

cnf(c_13856,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13783,c_33,c_100,c_101,c_542,c_636,c_1708,c_1788,c_1789,c_1795,c_2221,c_2223,c_2224,c_2402,c_2423,c_2649,c_2756,c_2767,c_2896,c_3615,c_3864,c_4180,c_4212,c_4696,c_8102,c_12957,c_13795])).

cnf(c_13886,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13856,c_3615])).

cnf(c_14053,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13886])).

cnf(c_26,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_468,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK1 != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_186])).

cnf(c_469,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_1450,plain,
    ( sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_1607,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1450,c_8])).

cnf(c_97,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_99,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_102,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_104,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_1983,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | sK4 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_99,c_104])).

cnf(c_1984,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1983])).

cnf(c_13887,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13856,c_1984])).

cnf(c_13903,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13887])).

cnf(c_13907,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13903,c_8])).

cnf(c_14937,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK4))
    | k1_xboole_0 = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_16253,plain,
    ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13809,c_33,c_99,c_100,c_101,c_103,c_104,c_513,c_542,c_636,c_1607,c_1708,c_1788,c_1789,c_1795,c_2025,c_2221,c_2223,c_2224,c_2402,c_2403,c_2423,c_2649,c_2756,c_2767,c_2802,c_2896,c_3615,c_3864,c_4180,c_4212,c_4241,c_4242,c_4553,c_4696,c_4852,c_7367,c_7965,c_8102,c_8103,c_9280,c_9684,c_12398,c_12957,c_13795,c_13886,c_14053,c_14937])).

cnf(c_16258,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16253,c_2793])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.30  % Computer   : n007.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 17:58:36 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.31  % Running in FOF mode
% 3.71/0.91  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/0.91  
% 3.71/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/0.91  
% 3.71/0.91  ------  iProver source info
% 3.71/0.91  
% 3.71/0.91  git: date: 2020-06-30 10:37:57 +0100
% 3.71/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/0.91  git: non_committed_changes: false
% 3.71/0.91  git: last_make_outside_of_git: false
% 3.71/0.91  
% 3.71/0.91  ------ 
% 3.71/0.91  
% 3.71/0.91  ------ Input Options
% 3.71/0.91  
% 3.71/0.91  --out_options                           all
% 3.71/0.91  --tptp_safe_out                         true
% 3.71/0.91  --problem_path                          ""
% 3.71/0.91  --include_path                          ""
% 3.71/0.91  --clausifier                            res/vclausify_rel
% 3.71/0.91  --clausifier_options                    --mode clausify
% 3.71/0.91  --stdin                                 false
% 3.71/0.91  --stats_out                             all
% 3.71/0.91  
% 3.71/0.91  ------ General Options
% 3.71/0.91  
% 3.71/0.91  --fof                                   false
% 3.71/0.91  --time_out_real                         305.
% 3.71/0.91  --time_out_virtual                      -1.
% 3.71/0.91  --symbol_type_check                     false
% 3.71/0.91  --clausify_out                          false
% 3.71/0.91  --sig_cnt_out                           false
% 3.71/0.91  --trig_cnt_out                          false
% 3.71/0.91  --trig_cnt_out_tolerance                1.
% 3.71/0.91  --trig_cnt_out_sk_spl                   false
% 3.71/0.91  --abstr_cl_out                          false
% 3.71/0.91  
% 3.71/0.91  ------ Global Options
% 3.71/0.91  
% 3.71/0.91  --schedule                              default
% 3.71/0.91  --add_important_lit                     false
% 3.71/0.91  --prop_solver_per_cl                    1000
% 3.71/0.91  --min_unsat_core                        false
% 3.71/0.91  --soft_assumptions                      false
% 3.71/0.91  --soft_lemma_size                       3
% 3.71/0.91  --prop_impl_unit_size                   0
% 3.71/0.91  --prop_impl_unit                        []
% 3.71/0.91  --share_sel_clauses                     true
% 3.71/0.91  --reset_solvers                         false
% 3.71/0.91  --bc_imp_inh                            [conj_cone]
% 3.71/0.91  --conj_cone_tolerance                   3.
% 3.71/0.91  --extra_neg_conj                        none
% 3.71/0.91  --large_theory_mode                     true
% 3.71/0.91  --prolific_symb_bound                   200
% 3.71/0.91  --lt_threshold                          2000
% 3.71/0.91  --clause_weak_htbl                      true
% 3.71/0.91  --gc_record_bc_elim                     false
% 3.71/0.91  
% 3.71/0.91  ------ Preprocessing Options
% 3.71/0.91  
% 3.71/0.91  --preprocessing_flag                    true
% 3.71/0.91  --time_out_prep_mult                    0.1
% 3.71/0.91  --splitting_mode                        input
% 3.71/0.91  --splitting_grd                         true
% 3.71/0.91  --splitting_cvd                         false
% 3.71/0.91  --splitting_cvd_svl                     false
% 3.71/0.91  --splitting_nvd                         32
% 3.71/0.91  --sub_typing                            true
% 3.71/0.91  --prep_gs_sim                           true
% 3.71/0.91  --prep_unflatten                        true
% 3.71/0.91  --prep_res_sim                          true
% 3.71/0.91  --prep_upred                            true
% 3.71/0.91  --prep_sem_filter                       exhaustive
% 3.71/0.91  --prep_sem_filter_out                   false
% 3.71/0.91  --pred_elim                             true
% 3.71/0.91  --res_sim_input                         true
% 3.71/0.91  --eq_ax_congr_red                       true
% 3.71/0.91  --pure_diseq_elim                       true
% 3.71/0.91  --brand_transform                       false
% 3.71/0.91  --non_eq_to_eq                          false
% 3.71/0.91  --prep_def_merge                        true
% 3.71/0.91  --prep_def_merge_prop_impl              false
% 3.71/0.91  --prep_def_merge_mbd                    true
% 3.71/0.91  --prep_def_merge_tr_red                 false
% 3.71/0.91  --prep_def_merge_tr_cl                  false
% 3.71/0.91  --smt_preprocessing                     true
% 3.71/0.91  --smt_ac_axioms                         fast
% 3.71/0.91  --preprocessed_out                      false
% 3.71/0.91  --preprocessed_stats                    false
% 3.71/0.91  
% 3.71/0.91  ------ Abstraction refinement Options
% 3.71/0.91  
% 3.71/0.91  --abstr_ref                             []
% 3.71/0.91  --abstr_ref_prep                        false
% 3.71/0.91  --abstr_ref_until_sat                   false
% 3.71/0.91  --abstr_ref_sig_restrict                funpre
% 3.71/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.91  --abstr_ref_under                       []
% 3.71/0.91  
% 3.71/0.91  ------ SAT Options
% 3.71/0.91  
% 3.71/0.91  --sat_mode                              false
% 3.71/0.91  --sat_fm_restart_options                ""
% 3.71/0.91  --sat_gr_def                            false
% 3.71/0.91  --sat_epr_types                         true
% 3.71/0.91  --sat_non_cyclic_types                  false
% 3.71/0.91  --sat_finite_models                     false
% 3.71/0.91  --sat_fm_lemmas                         false
% 3.71/0.91  --sat_fm_prep                           false
% 3.71/0.91  --sat_fm_uc_incr                        true
% 3.71/0.91  --sat_out_model                         small
% 3.71/0.91  --sat_out_clauses                       false
% 3.71/0.91  
% 3.71/0.91  ------ QBF Options
% 3.71/0.91  
% 3.71/0.91  --qbf_mode                              false
% 3.71/0.91  --qbf_elim_univ                         false
% 3.71/0.91  --qbf_dom_inst                          none
% 3.71/0.91  --qbf_dom_pre_inst                      false
% 3.71/0.91  --qbf_sk_in                             false
% 3.71/0.91  --qbf_pred_elim                         true
% 3.71/0.91  --qbf_split                             512
% 3.71/0.91  
% 3.71/0.91  ------ BMC1 Options
% 3.71/0.91  
% 3.71/0.91  --bmc1_incremental                      false
% 3.71/0.91  --bmc1_axioms                           reachable_all
% 3.71/0.91  --bmc1_min_bound                        0
% 3.71/0.91  --bmc1_max_bound                        -1
% 3.71/0.91  --bmc1_max_bound_default                -1
% 3.71/0.91  --bmc1_symbol_reachability              true
% 3.71/0.91  --bmc1_property_lemmas                  false
% 3.71/0.91  --bmc1_k_induction                      false
% 3.71/0.91  --bmc1_non_equiv_states                 false
% 3.71/0.91  --bmc1_deadlock                         false
% 3.71/0.91  --bmc1_ucm                              false
% 3.71/0.91  --bmc1_add_unsat_core                   none
% 3.71/0.91  --bmc1_unsat_core_children              false
% 3.71/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.91  --bmc1_out_stat                         full
% 3.71/0.91  --bmc1_ground_init                      false
% 3.71/0.91  --bmc1_pre_inst_next_state              false
% 3.71/0.91  --bmc1_pre_inst_state                   false
% 3.71/0.91  --bmc1_pre_inst_reach_state             false
% 3.71/0.91  --bmc1_out_unsat_core                   false
% 3.71/0.91  --bmc1_aig_witness_out                  false
% 3.71/0.91  --bmc1_verbose                          false
% 3.71/0.91  --bmc1_dump_clauses_tptp                false
% 3.71/0.91  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.91  --bmc1_dump_file                        -
% 3.71/0.91  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.91  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.91  --bmc1_ucm_extend_mode                  1
% 3.71/0.91  --bmc1_ucm_init_mode                    2
% 3.71/0.91  --bmc1_ucm_cone_mode                    none
% 3.71/0.91  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.91  --bmc1_ucm_relax_model                  4
% 3.71/0.91  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.91  --bmc1_ucm_layered_model                none
% 3.71/0.91  --bmc1_ucm_max_lemma_size               10
% 3.71/0.91  
% 3.71/0.91  ------ AIG Options
% 3.71/0.91  
% 3.71/0.91  --aig_mode                              false
% 3.71/0.91  
% 3.71/0.91  ------ Instantiation Options
% 3.71/0.91  
% 3.71/0.91  --instantiation_flag                    true
% 3.71/0.91  --inst_sos_flag                         false
% 3.71/0.91  --inst_sos_phase                        true
% 3.71/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.91  --inst_lit_sel_side                     num_symb
% 3.71/0.91  --inst_solver_per_active                1400
% 3.71/0.91  --inst_solver_calls_frac                1.
% 3.71/0.91  --inst_passive_queue_type               priority_queues
% 3.71/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.91  --inst_passive_queues_freq              [25;2]
% 3.71/0.91  --inst_dismatching                      true
% 3.71/0.91  --inst_eager_unprocessed_to_passive     true
% 3.71/0.91  --inst_prop_sim_given                   true
% 3.71/0.91  --inst_prop_sim_new                     false
% 3.71/0.91  --inst_subs_new                         false
% 3.71/0.91  --inst_eq_res_simp                      false
% 3.71/0.91  --inst_subs_given                       false
% 3.71/0.91  --inst_orphan_elimination               true
% 3.71/0.91  --inst_learning_loop_flag               true
% 3.71/0.91  --inst_learning_start                   3000
% 3.71/0.91  --inst_learning_factor                  2
% 3.71/0.91  --inst_start_prop_sim_after_learn       3
% 3.71/0.91  --inst_sel_renew                        solver
% 3.71/0.91  --inst_lit_activity_flag                true
% 3.71/0.91  --inst_restr_to_given                   false
% 3.71/0.91  --inst_activity_threshold               500
% 3.71/0.91  --inst_out_proof                        true
% 3.71/0.91  
% 3.71/0.91  ------ Resolution Options
% 3.71/0.91  
% 3.71/0.91  --resolution_flag                       true
% 3.71/0.91  --res_lit_sel                           adaptive
% 3.71/0.91  --res_lit_sel_side                      none
% 3.71/0.91  --res_ordering                          kbo
% 3.71/0.91  --res_to_prop_solver                    active
% 3.71/0.91  --res_prop_simpl_new                    false
% 3.71/0.91  --res_prop_simpl_given                  true
% 3.71/0.91  --res_passive_queue_type                priority_queues
% 3.71/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.91  --res_passive_queues_freq               [15;5]
% 3.71/0.91  --res_forward_subs                      full
% 3.71/0.91  --res_backward_subs                     full
% 3.71/0.91  --res_forward_subs_resolution           true
% 3.71/0.91  --res_backward_subs_resolution          true
% 3.71/0.91  --res_orphan_elimination                true
% 3.71/0.91  --res_time_limit                        2.
% 3.71/0.91  --res_out_proof                         true
% 3.71/0.91  
% 3.71/0.91  ------ Superposition Options
% 3.71/0.91  
% 3.71/0.91  --superposition_flag                    true
% 3.71/0.91  --sup_passive_queue_type                priority_queues
% 3.71/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.91  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.91  --demod_completeness_check              fast
% 3.71/0.91  --demod_use_ground                      true
% 3.71/0.91  --sup_to_prop_solver                    passive
% 3.71/0.91  --sup_prop_simpl_new                    true
% 3.71/0.91  --sup_prop_simpl_given                  true
% 3.71/0.91  --sup_fun_splitting                     false
% 3.71/0.91  --sup_smt_interval                      50000
% 3.71/0.91  
% 3.71/0.91  ------ Superposition Simplification Setup
% 3.71/0.91  
% 3.71/0.91  --sup_indices_passive                   []
% 3.71/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.91  --sup_full_bw                           [BwDemod]
% 3.71/0.91  --sup_immed_triv                        [TrivRules]
% 3.71/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.91  --sup_immed_bw_main                     []
% 3.71/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.91  
% 3.71/0.91  ------ Combination Options
% 3.71/0.91  
% 3.71/0.91  --comb_res_mult                         3
% 3.71/0.91  --comb_sup_mult                         2
% 3.71/0.91  --comb_inst_mult                        10
% 3.71/0.91  
% 3.71/0.91  ------ Debug Options
% 3.71/0.91  
% 3.71/0.91  --dbg_backtrace                         false
% 3.71/0.91  --dbg_dump_prop_clauses                 false
% 3.71/0.91  --dbg_dump_prop_clauses_file            -
% 3.71/0.91  --dbg_out_stat                          false
% 3.71/0.91  ------ Parsing...
% 3.71/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/0.91  
% 3.71/0.91  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.71/0.91  
% 3.71/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.91  
% 3.71/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/0.91  ------ Proving...
% 3.71/0.91  ------ Problem Properties 
% 3.71/0.91  
% 3.71/0.91  
% 3.71/0.91  clauses                                 32
% 3.71/0.91  conjectures                             3
% 3.71/0.91  EPR                                     6
% 3.71/0.91  Horn                                    28
% 3.71/0.91  unary                                   10
% 3.71/0.91  binary                                  9
% 3.71/0.91  lits                                    72
% 3.71/0.91  lits eq                                 31
% 3.71/0.91  fd_pure                                 0
% 3.71/0.91  fd_pseudo                               0
% 3.71/0.91  fd_cond                                 3
% 3.71/0.91  fd_pseudo_cond                          1
% 3.71/0.91  AC symbols                              0
% 3.71/0.91  
% 3.71/0.91  ------ Schedule dynamic 5 is on 
% 3.71/0.91  
% 3.71/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/0.91  
% 3.71/0.91  
% 3.71/0.91  ------ 
% 3.71/0.91  Current options:
% 3.71/0.91  ------ 
% 3.71/0.91  
% 3.71/0.91  ------ Input Options
% 3.71/0.91  
% 3.71/0.91  --out_options                           all
% 3.71/0.91  --tptp_safe_out                         true
% 3.71/0.91  --problem_path                          ""
% 3.71/0.91  --include_path                          ""
% 3.71/0.91  --clausifier                            res/vclausify_rel
% 3.71/0.91  --clausifier_options                    --mode clausify
% 3.71/0.91  --stdin                                 false
% 3.71/0.91  --stats_out                             all
% 3.71/0.91  
% 3.71/0.91  ------ General Options
% 3.71/0.91  
% 3.71/0.91  --fof                                   false
% 3.71/0.91  --time_out_real                         305.
% 3.71/0.91  --time_out_virtual                      -1.
% 3.71/0.91  --symbol_type_check                     false
% 3.71/0.91  --clausify_out                          false
% 3.71/0.91  --sig_cnt_out                           false
% 3.71/0.91  --trig_cnt_out                          false
% 3.71/0.91  --trig_cnt_out_tolerance                1.
% 3.71/0.91  --trig_cnt_out_sk_spl                   false
% 3.71/0.91  --abstr_cl_out                          false
% 3.71/0.91  
% 3.71/0.91  ------ Global Options
% 3.71/0.91  
% 3.71/0.91  --schedule                              default
% 3.71/0.91  --add_important_lit                     false
% 3.71/0.91  --prop_solver_per_cl                    1000
% 3.71/0.91  --min_unsat_core                        false
% 3.71/0.91  --soft_assumptions                      false
% 3.71/0.91  --soft_lemma_size                       3
% 3.71/0.91  --prop_impl_unit_size                   0
% 3.71/0.91  --prop_impl_unit                        []
% 3.71/0.91  --share_sel_clauses                     true
% 3.71/0.91  --reset_solvers                         false
% 3.71/0.91  --bc_imp_inh                            [conj_cone]
% 3.71/0.91  --conj_cone_tolerance                   3.
% 3.71/0.91  --extra_neg_conj                        none
% 3.71/0.91  --large_theory_mode                     true
% 3.71/0.91  --prolific_symb_bound                   200
% 3.71/0.91  --lt_threshold                          2000
% 3.71/0.91  --clause_weak_htbl                      true
% 3.71/0.91  --gc_record_bc_elim                     false
% 3.71/0.91  
% 3.71/0.91  ------ Preprocessing Options
% 3.71/0.91  
% 3.71/0.91  --preprocessing_flag                    true
% 3.71/0.91  --time_out_prep_mult                    0.1
% 3.71/0.91  --splitting_mode                        input
% 3.71/0.91  --splitting_grd                         true
% 3.71/0.91  --splitting_cvd                         false
% 3.71/0.91  --splitting_cvd_svl                     false
% 3.71/0.91  --splitting_nvd                         32
% 3.71/0.91  --sub_typing                            true
% 3.71/0.91  --prep_gs_sim                           true
% 3.71/0.91  --prep_unflatten                        true
% 3.71/0.91  --prep_res_sim                          true
% 3.71/0.91  --prep_upred                            true
% 3.71/0.91  --prep_sem_filter                       exhaustive
% 3.71/0.91  --prep_sem_filter_out                   false
% 3.71/0.91  --pred_elim                             true
% 3.71/0.91  --res_sim_input                         true
% 3.71/0.91  --eq_ax_congr_red                       true
% 3.71/0.91  --pure_diseq_elim                       true
% 3.71/0.91  --brand_transform                       false
% 3.71/0.91  --non_eq_to_eq                          false
% 3.71/0.91  --prep_def_merge                        true
% 3.71/0.91  --prep_def_merge_prop_impl              false
% 3.71/0.91  --prep_def_merge_mbd                    true
% 3.71/0.91  --prep_def_merge_tr_red                 false
% 3.71/0.91  --prep_def_merge_tr_cl                  false
% 3.71/0.91  --smt_preprocessing                     true
% 3.71/0.91  --smt_ac_axioms                         fast
% 3.71/0.91  --preprocessed_out                      false
% 3.71/0.91  --preprocessed_stats                    false
% 3.71/0.91  
% 3.71/0.91  ------ Abstraction refinement Options
% 3.71/0.91  
% 3.71/0.91  --abstr_ref                             []
% 3.71/0.91  --abstr_ref_prep                        false
% 3.71/0.91  --abstr_ref_until_sat                   false
% 3.71/0.91  --abstr_ref_sig_restrict                funpre
% 3.71/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.91  --abstr_ref_under                       []
% 3.71/0.91  
% 3.71/0.91  ------ SAT Options
% 3.71/0.91  
% 3.71/0.91  --sat_mode                              false
% 3.71/0.91  --sat_fm_restart_options                ""
% 3.71/0.91  --sat_gr_def                            false
% 3.71/0.91  --sat_epr_types                         true
% 3.71/0.91  --sat_non_cyclic_types                  false
% 3.71/0.91  --sat_finite_models                     false
% 3.71/0.91  --sat_fm_lemmas                         false
% 3.71/0.91  --sat_fm_prep                           false
% 3.71/0.91  --sat_fm_uc_incr                        true
% 3.71/0.91  --sat_out_model                         small
% 3.71/0.91  --sat_out_clauses                       false
% 3.71/0.91  
% 3.71/0.91  ------ QBF Options
% 3.71/0.91  
% 3.71/0.91  --qbf_mode                              false
% 3.71/0.91  --qbf_elim_univ                         false
% 3.71/0.91  --qbf_dom_inst                          none
% 3.71/0.91  --qbf_dom_pre_inst                      false
% 3.71/0.91  --qbf_sk_in                             false
% 3.71/0.91  --qbf_pred_elim                         true
% 3.71/0.91  --qbf_split                             512
% 3.71/0.91  
% 3.71/0.91  ------ BMC1 Options
% 3.71/0.91  
% 3.71/0.91  --bmc1_incremental                      false
% 3.71/0.91  --bmc1_axioms                           reachable_all
% 3.71/0.91  --bmc1_min_bound                        0
% 3.71/0.91  --bmc1_max_bound                        -1
% 3.71/0.91  --bmc1_max_bound_default                -1
% 3.71/0.91  --bmc1_symbol_reachability              true
% 3.71/0.91  --bmc1_property_lemmas                  false
% 3.71/0.91  --bmc1_k_induction                      false
% 3.71/0.91  --bmc1_non_equiv_states                 false
% 3.71/0.91  --bmc1_deadlock                         false
% 3.71/0.91  --bmc1_ucm                              false
% 3.71/0.91  --bmc1_add_unsat_core                   none
% 3.71/0.91  --bmc1_unsat_core_children              false
% 3.71/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.91  --bmc1_out_stat                         full
% 3.71/0.91  --bmc1_ground_init                      false
% 3.71/0.91  --bmc1_pre_inst_next_state              false
% 3.71/0.91  --bmc1_pre_inst_state                   false
% 3.71/0.91  --bmc1_pre_inst_reach_state             false
% 3.71/0.91  --bmc1_out_unsat_core                   false
% 3.71/0.91  --bmc1_aig_witness_out                  false
% 3.71/0.91  --bmc1_verbose                          false
% 3.71/0.91  --bmc1_dump_clauses_tptp                false
% 3.71/0.91  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.91  --bmc1_dump_file                        -
% 3.71/0.91  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.91  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.91  --bmc1_ucm_extend_mode                  1
% 3.71/0.91  --bmc1_ucm_init_mode                    2
% 3.71/0.91  --bmc1_ucm_cone_mode                    none
% 3.71/0.91  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.91  --bmc1_ucm_relax_model                  4
% 3.71/0.91  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.91  --bmc1_ucm_layered_model                none
% 3.71/0.91  --bmc1_ucm_max_lemma_size               10
% 3.71/0.91  
% 3.71/0.91  ------ AIG Options
% 3.71/0.91  
% 3.71/0.91  --aig_mode                              false
% 3.71/0.91  
% 3.71/0.91  ------ Instantiation Options
% 3.71/0.91  
% 3.71/0.91  --instantiation_flag                    true
% 3.71/0.91  --inst_sos_flag                         false
% 3.71/0.91  --inst_sos_phase                        true
% 3.71/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.91  --inst_lit_sel_side                     none
% 3.71/0.91  --inst_solver_per_active                1400
% 3.71/0.91  --inst_solver_calls_frac                1.
% 3.71/0.91  --inst_passive_queue_type               priority_queues
% 3.71/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.91  --inst_passive_queues_freq              [25;2]
% 3.71/0.91  --inst_dismatching                      true
% 3.71/0.91  --inst_eager_unprocessed_to_passive     true
% 3.71/0.91  --inst_prop_sim_given                   true
% 3.71/0.91  --inst_prop_sim_new                     false
% 3.71/0.91  --inst_subs_new                         false
% 3.71/0.91  --inst_eq_res_simp                      false
% 3.71/0.91  --inst_subs_given                       false
% 3.71/0.91  --inst_orphan_elimination               true
% 3.71/0.91  --inst_learning_loop_flag               true
% 3.71/0.91  --inst_learning_start                   3000
% 3.71/0.91  --inst_learning_factor                  2
% 3.71/0.91  --inst_start_prop_sim_after_learn       3
% 3.71/0.91  --inst_sel_renew                        solver
% 3.71/0.91  --inst_lit_activity_flag                true
% 3.71/0.91  --inst_restr_to_given                   false
% 3.71/0.91  --inst_activity_threshold               500
% 3.71/0.91  --inst_out_proof                        true
% 3.71/0.91  
% 3.71/0.91  ------ Resolution Options
% 3.71/0.91  
% 3.71/0.91  --resolution_flag                       false
% 3.71/0.91  --res_lit_sel                           adaptive
% 3.71/0.91  --res_lit_sel_side                      none
% 3.71/0.91  --res_ordering                          kbo
% 3.71/0.91  --res_to_prop_solver                    active
% 3.71/0.91  --res_prop_simpl_new                    false
% 3.71/0.91  --res_prop_simpl_given                  true
% 3.71/0.91  --res_passive_queue_type                priority_queues
% 3.71/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.91  --res_passive_queues_freq               [15;5]
% 3.71/0.91  --res_forward_subs                      full
% 3.71/0.91  --res_backward_subs                     full
% 3.71/0.91  --res_forward_subs_resolution           true
% 3.71/0.91  --res_backward_subs_resolution          true
% 3.71/0.91  --res_orphan_elimination                true
% 3.71/0.91  --res_time_limit                        2.
% 3.71/0.91  --res_out_proof                         true
% 3.71/0.91  
% 3.71/0.91  ------ Superposition Options
% 3.71/0.91  
% 3.71/0.91  --superposition_flag                    true
% 3.71/0.91  --sup_passive_queue_type                priority_queues
% 3.71/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.91  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.91  --demod_completeness_check              fast
% 3.71/0.92  --demod_use_ground                      true
% 3.71/0.92  --sup_to_prop_solver                    passive
% 3.71/0.92  --sup_prop_simpl_new                    true
% 3.71/0.92  --sup_prop_simpl_given                  true
% 3.71/0.92  --sup_fun_splitting                     false
% 3.71/0.92  --sup_smt_interval                      50000
% 3.71/0.92  
% 3.71/0.92  ------ Superposition Simplification Setup
% 3.71/0.92  
% 3.71/0.92  --sup_indices_passive                   []
% 3.71/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.92  --sup_full_bw                           [BwDemod]
% 3.71/0.92  --sup_immed_triv                        [TrivRules]
% 3.71/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.92  --sup_immed_bw_main                     []
% 3.71/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.92  
% 3.71/0.92  ------ Combination Options
% 3.71/0.92  
% 3.71/0.92  --comb_res_mult                         3
% 3.71/0.92  --comb_sup_mult                         2
% 3.71/0.92  --comb_inst_mult                        10
% 3.71/0.92  
% 3.71/0.92  ------ Debug Options
% 3.71/0.92  
% 3.71/0.92  --dbg_backtrace                         false
% 3.71/0.92  --dbg_dump_prop_clauses                 false
% 3.71/0.92  --dbg_dump_prop_clauses_file            -
% 3.71/0.92  --dbg_out_stat                          false
% 3.71/0.92  
% 3.71/0.92  
% 3.71/0.92  
% 3.71/0.92  
% 3.71/0.92  ------ Proving...
% 3.71/0.92  
% 3.71/0.92  
% 3.71/0.92  % SZS status Theorem for theBenchmark.p
% 3.71/0.92  
% 3.71/0.92   Resolution empty clause
% 3.71/0.92  
% 3.71/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/0.92  
% 3.71/0.92  fof(f17,axiom,(
% 3.71/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f33,plain,(
% 3.71/0.92    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.92    inference(ennf_transformation,[],[f17])).
% 3.71/0.92  
% 3.71/0.92  fof(f34,plain,(
% 3.71/0.92    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.92    inference(flattening,[],[f33])).
% 3.71/0.92  
% 3.71/0.92  fof(f47,plain,(
% 3.71/0.92    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.92    inference(nnf_transformation,[],[f34])).
% 3.71/0.92  
% 3.71/0.92  fof(f76,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f47])).
% 3.71/0.92  
% 3.71/0.92  fof(f18,conjecture,(
% 3.71/0.92    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f19,negated_conjecture,(
% 3.71/0.92    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.71/0.92    inference(negated_conjecture,[],[f18])).
% 3.71/0.92  
% 3.71/0.92  fof(f35,plain,(
% 3.71/0.92    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.71/0.92    inference(ennf_transformation,[],[f19])).
% 3.71/0.92  
% 3.71/0.92  fof(f36,plain,(
% 3.71/0.92    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.71/0.92    inference(flattening,[],[f35])).
% 3.71/0.92  
% 3.71/0.92  fof(f48,plain,(
% 3.71/0.92    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.71/0.92    introduced(choice_axiom,[])).
% 3.71/0.92  
% 3.71/0.92  fof(f49,plain,(
% 3.71/0.92    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.71/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f36,f48])).
% 3.71/0.92  
% 3.71/0.92  fof(f83,plain,(
% 3.71/0.92    v1_funct_2(sK4,sK1,sK2)),
% 3.71/0.92    inference(cnf_transformation,[],[f49])).
% 3.71/0.92  
% 3.71/0.92  fof(f84,plain,(
% 3.71/0.92    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.71/0.92    inference(cnf_transformation,[],[f49])).
% 3.71/0.92  
% 3.71/0.92  fof(f13,axiom,(
% 3.71/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f29,plain,(
% 3.71/0.92    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.92    inference(ennf_transformation,[],[f13])).
% 3.71/0.92  
% 3.71/0.92  fof(f72,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f29])).
% 3.71/0.92  
% 3.71/0.92  fof(f2,axiom,(
% 3.71/0.92    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f23,plain,(
% 3.71/0.92    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.71/0.92    inference(ennf_transformation,[],[f2])).
% 3.71/0.92  
% 3.71/0.92  fof(f37,plain,(
% 3.71/0.92    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/0.92    inference(nnf_transformation,[],[f23])).
% 3.71/0.92  
% 3.71/0.92  fof(f38,plain,(
% 3.71/0.92    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/0.92    inference(rectify,[],[f37])).
% 3.71/0.92  
% 3.71/0.92  fof(f39,plain,(
% 3.71/0.92    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.71/0.92    introduced(choice_axiom,[])).
% 3.71/0.92  
% 3.71/0.92  fof(f40,plain,(
% 3.71/0.92    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 3.71/0.92  
% 3.71/0.92  fof(f52,plain,(
% 3.71/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f40])).
% 3.71/0.92  
% 3.71/0.92  fof(f12,axiom,(
% 3.71/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f21,plain,(
% 3.71/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.71/0.92    inference(pure_predicate_removal,[],[f12])).
% 3.71/0.92  
% 3.71/0.92  fof(f28,plain,(
% 3.71/0.92    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.92    inference(ennf_transformation,[],[f21])).
% 3.71/0.92  
% 3.71/0.92  fof(f71,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f28])).
% 3.71/0.92  
% 3.71/0.92  fof(f8,axiom,(
% 3.71/0.92    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f25,plain,(
% 3.71/0.92    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.71/0.92    inference(ennf_transformation,[],[f8])).
% 3.71/0.92  
% 3.71/0.92  fof(f46,plain,(
% 3.71/0.92    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.71/0.92    inference(nnf_transformation,[],[f25])).
% 3.71/0.92  
% 3.71/0.92  fof(f64,plain,(
% 3.71/0.92    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f46])).
% 3.71/0.92  
% 3.71/0.92  fof(f51,plain,(
% 3.71/0.92    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f40])).
% 3.71/0.92  
% 3.71/0.92  fof(f6,axiom,(
% 3.71/0.92    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f45,plain,(
% 3.71/0.92    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.71/0.92    inference(nnf_transformation,[],[f6])).
% 3.71/0.92  
% 3.71/0.92  fof(f61,plain,(
% 3.71/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f45])).
% 3.71/0.92  
% 3.71/0.92  fof(f7,axiom,(
% 3.71/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f24,plain,(
% 3.71/0.92    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.71/0.92    inference(ennf_transformation,[],[f7])).
% 3.71/0.92  
% 3.71/0.92  fof(f63,plain,(
% 3.71/0.92    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f24])).
% 3.71/0.92  
% 3.71/0.92  fof(f62,plain,(
% 3.71/0.92    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f45])).
% 3.71/0.92  
% 3.71/0.92  fof(f9,axiom,(
% 3.71/0.92    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f66,plain,(
% 3.71/0.92    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f9])).
% 3.71/0.92  
% 3.71/0.92  fof(f53,plain,(
% 3.71/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f40])).
% 3.71/0.92  
% 3.71/0.92  fof(f14,axiom,(
% 3.71/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f30,plain,(
% 3.71/0.92    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.92    inference(ennf_transformation,[],[f14])).
% 3.71/0.92  
% 3.71/0.92  fof(f73,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f30])).
% 3.71/0.92  
% 3.71/0.92  fof(f85,plain,(
% 3.71/0.92    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 3.71/0.92    inference(cnf_transformation,[],[f49])).
% 3.71/0.92  
% 3.71/0.92  fof(f15,axiom,(
% 3.71/0.92    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f31,plain,(
% 3.71/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.71/0.92    inference(ennf_transformation,[],[f15])).
% 3.71/0.92  
% 3.71/0.92  fof(f32,plain,(
% 3.71/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.71/0.92    inference(flattening,[],[f31])).
% 3.71/0.92  
% 3.71/0.92  fof(f74,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f32])).
% 3.71/0.92  
% 3.71/0.92  fof(f78,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f47])).
% 3.71/0.92  
% 3.71/0.92  fof(f87,plain,(
% 3.71/0.92    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 3.71/0.92    inference(cnf_transformation,[],[f49])).
% 3.71/0.92  
% 3.71/0.92  fof(f82,plain,(
% 3.71/0.92    v1_funct_1(sK4)),
% 3.71/0.92    inference(cnf_transformation,[],[f49])).
% 3.71/0.92  
% 3.71/0.92  fof(f4,axiom,(
% 3.71/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f41,plain,(
% 3.71/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/0.92    inference(nnf_transformation,[],[f4])).
% 3.71/0.92  
% 3.71/0.92  fof(f42,plain,(
% 3.71/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/0.92    inference(flattening,[],[f41])).
% 3.71/0.92  
% 3.71/0.92  fof(f57,plain,(
% 3.71/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f42])).
% 3.71/0.92  
% 3.71/0.92  fof(f5,axiom,(
% 3.71/0.92    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f43,plain,(
% 3.71/0.92    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.71/0.92    inference(nnf_transformation,[],[f5])).
% 3.71/0.92  
% 3.71/0.92  fof(f44,plain,(
% 3.71/0.92    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.71/0.92    inference(flattening,[],[f43])).
% 3.71/0.92  
% 3.71/0.92  fof(f60,plain,(
% 3.71/0.92    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.71/0.92    inference(cnf_transformation,[],[f44])).
% 3.71/0.92  
% 3.71/0.92  fof(f90,plain,(
% 3.71/0.92    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.71/0.92    inference(equality_resolution,[],[f60])).
% 3.71/0.92  
% 3.71/0.92  fof(f58,plain,(
% 3.71/0.92    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f44])).
% 3.71/0.92  
% 3.71/0.92  fof(f59,plain,(
% 3.71/0.92    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.71/0.92    inference(cnf_transformation,[],[f44])).
% 3.71/0.92  
% 3.71/0.92  fof(f91,plain,(
% 3.71/0.92    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.71/0.92    inference(equality_resolution,[],[f59])).
% 3.71/0.92  
% 3.71/0.92  fof(f55,plain,(
% 3.71/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.71/0.92    inference(cnf_transformation,[],[f42])).
% 3.71/0.92  
% 3.71/0.92  fof(f89,plain,(
% 3.71/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/0.92    inference(equality_resolution,[],[f55])).
% 3.71/0.92  
% 3.71/0.92  fof(f79,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f47])).
% 3.71/0.92  
% 3.71/0.92  fof(f95,plain,(
% 3.71/0.92    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.71/0.92    inference(equality_resolution,[],[f79])).
% 3.71/0.92  
% 3.71/0.92  fof(f11,axiom,(
% 3.71/0.92    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f69,plain,(
% 3.71/0.92    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.71/0.92    inference(cnf_transformation,[],[f11])).
% 3.71/0.92  
% 3.71/0.92  fof(f70,plain,(
% 3.71/0.92    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.71/0.92    inference(cnf_transformation,[],[f11])).
% 3.71/0.92  
% 3.71/0.92  fof(f16,axiom,(
% 3.71/0.92    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f75,plain,(
% 3.71/0.92    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f16])).
% 3.71/0.92  
% 3.71/0.92  fof(f86,plain,(
% 3.71/0.92    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.71/0.92    inference(cnf_transformation,[],[f49])).
% 3.71/0.92  
% 3.71/0.92  fof(f1,axiom,(
% 3.71/0.92    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f20,plain,(
% 3.71/0.92    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.71/0.92    inference(unused_predicate_definition_removal,[],[f1])).
% 3.71/0.92  
% 3.71/0.92  fof(f22,plain,(
% 3.71/0.92    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.71/0.92    inference(ennf_transformation,[],[f20])).
% 3.71/0.92  
% 3.71/0.92  fof(f50,plain,(
% 3.71/0.92    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.71/0.92    inference(cnf_transformation,[],[f22])).
% 3.71/0.92  
% 3.71/0.92  fof(f3,axiom,(
% 3.71/0.92    v1_xboole_0(k1_xboole_0)),
% 3.71/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.92  
% 3.71/0.92  fof(f54,plain,(
% 3.71/0.92    v1_xboole_0(k1_xboole_0)),
% 3.71/0.92    inference(cnf_transformation,[],[f3])).
% 3.71/0.92  
% 3.71/0.92  fof(f56,plain,(
% 3.71/0.92    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.71/0.92    inference(cnf_transformation,[],[f42])).
% 3.71/0.92  
% 3.71/0.92  fof(f88,plain,(
% 3.71/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/0.92    inference(equality_resolution,[],[f56])).
% 3.71/0.92  
% 3.71/0.92  fof(f81,plain,(
% 3.71/0.92    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(cnf_transformation,[],[f47])).
% 3.71/0.92  
% 3.71/0.92  fof(f92,plain,(
% 3.71/0.92    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.92    inference(equality_resolution,[],[f81])).
% 3.71/0.92  
% 3.71/0.92  fof(f93,plain,(
% 3.71/0.92    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.71/0.92    inference(equality_resolution,[],[f92])).
% 3.71/0.92  
% 3.71/0.92  cnf(c_31,plain,
% 3.71/0.92      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | k1_relset_1(X1,X2,X0) = X1
% 3.71/0.92      | k1_xboole_0 = X2 ),
% 3.71/0.92      inference(cnf_transformation,[],[f76]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_36,negated_conjecture,
% 3.71/0.92      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.71/0.92      inference(cnf_transformation,[],[f83]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_553,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | k1_relset_1(X1,X2,X0) = X1
% 3.71/0.92      | sK2 != X2
% 3.71/0.92      | sK1 != X1
% 3.71/0.92      | sK4 != X0
% 3.71/0.92      | k1_xboole_0 = X2 ),
% 3.71/0.92      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_554,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.71/0.92      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.71/0.92      | k1_xboole_0 = sK2 ),
% 3.71/0.92      inference(unflattening,[status(thm)],[c_553]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_35,negated_conjecture,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.71/0.92      inference(cnf_transformation,[],[f84]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_556,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.71/0.92      inference(global_propositional_subsumption,[status(thm)],[c_554,c_35]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1454,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_22,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.71/0.92      inference(cnf_transformation,[],[f72]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1459,plain,
% 3.71/0.92      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.71/0.92      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3474,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1454,c_1459]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3656,plain,
% 3.71/0.92      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_556,c_3474]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2,plain,
% 3.71/0.92      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 3.71/0.92      inference(cnf_transformation,[],[f52]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1468,plain,
% 3.71/0.92      ( r1_tarski(X0,X1) = iProver_top
% 3.71/0.92      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_21,plain,
% 3.71/0.92      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/0.92      inference(cnf_transformation,[],[f71]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_15,plain,
% 3.71/0.92      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.71/0.92      inference(cnf_transformation,[],[f64]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_441,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),X1)
% 3.71/0.92      | ~ v1_relat_1(X0) ),
% 3.71/0.92      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1451,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.71/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1795,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1454,c_1451]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.71/0.92      inference(cnf_transformation,[],[f51]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1467,plain,
% 3.71/0.92      ( r1_tarski(X0,X1) != iProver_top
% 3.71/0.92      | r2_hidden(X2,X0) != iProver_top
% 3.71/0.92      | r2_hidden(X2,X1) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4079,plain,
% 3.71/0.92      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.71/0.92      | r2_hidden(X0,sK1) = iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1795,c_1467]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.71/0.92      inference(cnf_transformation,[],[f61]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1463,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.71/0.92      | r1_tarski(X0,X1) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2322,plain,
% 3.71/0.92      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1454,c_1463]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.71/0.92      inference(cnf_transformation,[],[f63]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_11,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.71/0.92      inference(cnf_transformation,[],[f62]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_258,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.71/0.92      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_259,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_258]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_321,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.71/0.92      inference(bin_hyper_res,[status(thm)],[c_13,c_259]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1453,plain,
% 3.71/0.92      ( r1_tarski(X0,X1) != iProver_top
% 3.71/0.92      | v1_relat_1(X1) != iProver_top
% 3.71/0.92      | v1_relat_1(X0) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2337,plain,
% 3.71/0.92      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_2322,c_1453]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_16,plain,
% 3.71/0.92      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.71/0.92      inference(cnf_transformation,[],[f66]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1462,plain,
% 3.71/0.92      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2402,plain,
% 3.71/0.92      ( v1_relat_1(sK4) = iProver_top ),
% 3.71/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_2337,c_1462]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4371,plain,
% 3.71/0.92      ( r2_hidden(X0,sK1) = iProver_top
% 3.71/0.92      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.71/0.92      inference(global_propositional_subsumption,[status(thm)],[c_4079,c_2402]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4372,plain,
% 3.71/0.92      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.71/0.92      | r2_hidden(X0,sK1) = iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_4371]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4379,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.71/0.92      | r2_hidden(sK0(k1_relat_1(sK4),X0),sK1) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1468,c_4372]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1,plain,
% 3.71/0.92      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 3.71/0.92      inference(cnf_transformation,[],[f53]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1469,plain,
% 3.71/0.92      ( r1_tarski(X0,X1) = iProver_top
% 3.71/0.92      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5937,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_4379,c_1469]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_23,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.71/0.92      inference(cnf_transformation,[],[f73]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1458,plain,
% 3.71/0.92      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.71/0.92      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3219,plain,
% 3.71/0.92      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1454,c_1458]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_34,negated_conjecture,
% 3.71/0.92      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 3.71/0.92      inference(cnf_transformation,[],[f85]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1455,plain,
% 3.71/0.92      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3615,plain,
% 3.71/0.92      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_3219,c_1455]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_24,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.71/0.92      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.71/0.92      | ~ v1_relat_1(X0) ),
% 3.71/0.92      inference(cnf_transformation,[],[f74]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1457,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.71/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3472,plain,
% 3.71/0.92      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.71/0.92      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.71/0.92      | v1_relat_1(X2) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1457,c_1459]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_11579,plain,
% 3.71/0.92      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_3615,c_3472]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12387,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.71/0.92      | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
% 3.71/0.92      inference(global_propositional_subsumption,
% 3.71/0.92                [status(thm)],
% 3.71/0.92                [c_11579,c_2402]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12388,plain,
% 3.71/0.92      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_12387]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12397,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_5937,c_12388]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_29,plain,
% 3.71/0.92      ( v1_funct_2(X0,X1,X2)
% 3.71/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | k1_relset_1(X1,X2,X0) != X1
% 3.71/0.92      | k1_xboole_0 = X2 ),
% 3.71/0.92      inference(cnf_transformation,[],[f78]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_32,negated_conjecture,
% 3.71/0.92      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.71/0.92      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | ~ v1_funct_1(sK4) ),
% 3.71/0.92      inference(cnf_transformation,[],[f87]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_37,negated_conjecture,
% 3.71/0.92      ( v1_funct_1(sK4) ),
% 3.71/0.92      inference(cnf_transformation,[],[f82]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_185,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 3.71/0.92      inference(global_propositional_subsumption,[status(thm)],[c_32,c_37]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_186,negated_conjecture,
% 3.71/0.92      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.71/0.92      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_185]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_540,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.92      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | k1_relset_1(X1,X2,X0) != X1
% 3.71/0.92      | sK3 != X2
% 3.71/0.92      | sK1 != X1
% 3.71/0.92      | sK4 != X0
% 3.71/0.92      | k1_xboole_0 = X2 ),
% 3.71/0.92      inference(resolution_lifted,[status(thm)],[c_29,c_186]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_541,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) != sK1
% 3.71/0.92      | k1_xboole_0 = sK3 ),
% 3.71/0.92      inference(unflattening,[status(thm)],[c_540]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1446,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.71/0.92      | k1_xboole_0 = sK3
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12740,plain,
% 3.71/0.92      ( k1_relat_1(sK4) != sK1
% 3.71/0.92      | sK3 = k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_12397,c_1446]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2647,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.71/0.92      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 3.71/0.92      | ~ v1_relat_1(sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_24]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2649,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12953,plain,
% 3.71/0.92      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) != sK1 ),
% 3.71/0.92      inference(global_propositional_subsumption,
% 3.71/0.92                [status(thm)],
% 3.71/0.92                [c_12740,c_1796,c_2403,c_2647,c_3623,c_12741]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12954,plain,
% 3.71/0.92      ( k1_relat_1(sK4) != sK1 | sK3 = k1_xboole_0 ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_12953]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12957,plain,
% 3.71/0.92      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_3656,c_12954]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.71/0.92      inference(cnf_transformation,[],[f57]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1466,plain,
% 3.71/0.92      ( X0 = X1
% 3.71/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.71/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3949,plain,
% 3.71/0.92      ( k2_zfmisc_1(sK1,sK2) = sK4
% 3.71/0.92      | r1_tarski(k2_zfmisc_1(sK1,sK2),sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_2322,c_1466]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13775,plain,
% 3.71/0.92      ( k2_zfmisc_1(sK1,sK2) = sK4
% 3.71/0.92      | sK3 = k1_xboole_0
% 3.71/0.92      | r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_12957,c_3949]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8,plain,
% 3.71/0.92      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.71/0.92      inference(cnf_transformation,[],[f90]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13809,plain,
% 3.71/0.92      ( k2_zfmisc_1(sK1,sK2) = sK4
% 3.71/0.92      | sK3 = k1_xboole_0
% 3.71/0.92      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_13775,c_8]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_10,plain,
% 3.71/0.92      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.71/0.92      | k1_xboole_0 = X1
% 3.71/0.92      | k1_xboole_0 = X0 ),
% 3.71/0.92      inference(cnf_transformation,[],[f58]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_100,plain,
% 3.71/0.92      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.71/0.92      | k1_xboole_0 = k1_xboole_0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_10]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_9,plain,
% 3.71/0.92      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.71/0.92      inference(cnf_transformation,[],[f91]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_101,plain,
% 3.71/0.92      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_9]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f89]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_103,plain,
% 3.71/0.92      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_7]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_28,plain,
% 3.71/0.92      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.71/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.71/0.92      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.71/0.92      inference(cnf_transformation,[],[f95]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_511,plain,
% 3.71/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.71/0.92      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.71/0.92      | sK3 != X1
% 3.71/0.92      | sK1 != k1_xboole_0
% 3.71/0.92      | sK4 != X0 ),
% 3.71/0.92      inference(resolution_lifted,[status(thm)],[c_28,c_186]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_512,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.71/0.92      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.71/0.92      | sK1 != k1_xboole_0 ),
% 3.71/0.92      inference(unflattening,[status(thm)],[c_511]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_513,plain,
% 3.71/0.92      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.71/0.92      | sK1 != k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_564,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | sK2 != sK3
% 3.71/0.92      | sK1 != sK1
% 3.71/0.92      | sK4 != sK4 ),
% 3.71/0.92      inference(resolution_lifted,[status(thm)],[c_186,c_36]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_565,plain,
% 3.71/0.92      ( sK2 != sK3
% 3.71/0.92      | sK1 != sK1
% 3.71/0.92      | sK4 != sK4
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_843,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1707,plain,
% 3.71/0.92      ( sK2 != X0 | sK2 = sK3 | sK3 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_843]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1708,plain,
% 3.71/0.92      ( sK2 = sK3 | sK2 != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_1707]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_842,plain,( X0 = X0 ),theory(equality) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1789,plain,
% 3.71/0.92      ( sK1 = sK1 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_842]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2024,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.71/0.92      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.71/0.92      | ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0)
% 3.71/0.92      | ~ v1_relat_1(sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_24]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2025,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2403,plain,
% 3.71/0.92      ( v1_relat_1(sK4) ),
% 3.71/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_2402]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2799,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_5]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2800,plain,
% 3.71/0.92      ( sK4 = X0
% 3.71/0.92      | r1_tarski(X0,sK4) != iProver_top
% 3.71/0.92      | r1_tarski(sK4,X0) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_2799]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2802,plain,
% 3.71/0.92      ( sK4 = k1_xboole_0
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_2800]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2805,plain,
% 3.71/0.92      ( sK4 = sK4 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_842]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4239,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_12]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4241,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_4239]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4240,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.71/0.92      | r1_tarski(sK4,X0) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_4239]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4242,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_4240]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2678,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.71/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_8,c_1457]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4553,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1795,c_2678]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4850,plain,
% 3.71/0.92      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.71/0.92      inference(global_propositional_subsumption,[status(thm)],[c_4553,c_2402]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4851,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_4850]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4852,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
% 3.71/0.92      | ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
% 3.71/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_4851]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4163,plain,
% 3.71/0.92      ( k1_relset_1(k1_xboole_0,sK3,sK4) != X0
% 3.71/0.92      | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 3.71/0.92      | k1_xboole_0 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_843]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_7367,plain,
% 3.71/0.92      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_relat_1(sK4)
% 3.71/0.92      | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 3.71/0.92      | k1_xboole_0 != k1_relat_1(sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_4163]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1464,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.71/0.92      | r1_tarski(X0,X1) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2663,plain,
% 3.71/0.92      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.71/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1464,c_1451]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5535,plain,
% 3.71/0.92      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 3.71/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_9,c_2663]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_20,plain,
% 3.71/0.92      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.71/0.92      inference(cnf_transformation,[],[f69]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2679,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_9,c_1457]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4600,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) != iProver_top
% 3.71/0.92      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_20,c_2679]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_19,plain,
% 3.71/0.92      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.71/0.92      inference(cnf_transformation,[],[f70]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4617,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.71/0.92      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.71/0.92      inference(light_normalisation,[status(thm)],[c_4600,c_19]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_25,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.71/0.92      inference(cnf_transformation,[],[f75]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1456,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2321,plain,
% 3.71/0.92      ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1456,c_1463]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2594,plain,
% 3.71/0.92      ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
% 3.71/0.92      | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_2321,c_1453]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2962,plain,
% 3.71/0.92      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.71/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_2594,c_1462]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4806,plain,
% 3.71/0.92      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.71/0.92      | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.71/0.92      inference(global_propositional_subsumption,[status(thm)],[c_4617,c_2962]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4807,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.71/0.92      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_4806]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4816,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(k1_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1795,c_4807]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5230,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | m1_subset_1(k6_relat_1(k1_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.71/0.92      inference(global_propositional_subsumption,[status(thm)],[c_4816,c_2402]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5231,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(k1_relat_1(sK4)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_5230]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5236,plain,
% 3.71/0.92      ( sK2 = k1_xboole_0
% 3.71/0.92      | m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_3656,c_5231]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_33,negated_conjecture,
% 3.71/0.92      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.71/0.92      inference(cnf_transformation,[],[f86]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_542,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.71/0.92      | k1_xboole_0 = sK3
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1706,plain,
% 3.71/0.92      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_843]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1788,plain,
% 3.71/0.92      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_1706]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2220,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_22]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2221,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_2220]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1929,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != X0
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) = sK1
% 3.71/0.92      | sK1 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_843]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2223,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) = sK1
% 3.71/0.92      | sK1 != k1_relset_1(sK1,sK3,sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_1929]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2224,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) = k1_relset_1(sK1,sK3,sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_842]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2422,plain,
% 3.71/0.92      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_843]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2423,plain,
% 3.71/0.92      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1785,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_5]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2755,plain,
% 3.71/0.92      ( ~ r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1)
% 3.71/0.92      | ~ r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4))
% 3.71/0.92      | sK1 = k1_relset_1(sK1,sK3,sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_1785]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2756,plain,
% 3.71/0.92      ( sK1 = k1_relset_1(sK1,sK3,sK4)
% 3.71/0.92      | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4)) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_2755]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2759,plain,
% 3.71/0.92      ( r1_tarski(X0,k1_relset_1(sK1,sK3,sK4))
% 3.71/0.92      | r2_hidden(sK0(X0,k1_relset_1(sK1,sK3,sK4)),X0) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_2]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2765,plain,
% 3.71/0.92      ( r1_tarski(X0,k1_relset_1(sK1,sK3,sK4)) = iProver_top
% 3.71/0.92      | r2_hidden(sK0(X0,k1_relset_1(sK1,sK3,sK4)),X0) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_2759]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2767,plain,
% 3.71/0.92      ( r1_tarski(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)) = iProver_top
% 3.71/0.92      | r2_hidden(sK0(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)),k1_xboole_0) = iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_2765]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2896,plain,
% 3.71/0.92      ( sK3 = sK3 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_842]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2587,plain,
% 3.71/0.92      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_843]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_3864,plain,
% 3.71/0.92      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_2587]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_845,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.71/0.92      theory(equality) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2149,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1)
% 3.71/0.92      | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1)
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) != X0
% 3.71/0.92      | sK1 != X1 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_845]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4176,plain,
% 3.71/0.92      ( r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1)
% 3.71/0.92      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
% 3.71/0.92      | sK1 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_2149]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4178,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
% 3.71/0.92      | sK1 != X0
% 3.71/0.92      | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_4176]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4180,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != k1_relat_1(sK4)
% 3.71/0.92      | sK1 != k1_xboole_0
% 3.71/0.92      | r1_tarski(k1_relset_1(sK1,sK3,sK4),sK1) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_4178]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2522,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1)
% 3.71/0.92      | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4))
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) != X1
% 3.71/0.92      | sK1 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_845]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4209,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,k1_relset_1(sK1,sK3,sK4))
% 3.71/0.92      | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4))
% 3.71/0.92      | k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
% 3.71/0.92      | sK1 != X0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_2522]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4210,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
% 3.71/0.92      | sK1 != X0
% 3.71/0.92      | r1_tarski(X0,k1_relset_1(sK1,sK3,sK4)) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4)) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_4209]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4212,plain,
% 3.71/0.92      ( k1_relset_1(sK1,sK3,sK4) != k1_relset_1(sK1,sK3,sK4)
% 3.71/0.92      | sK1 != k1_xboole_0
% 3.71/0.92      | r1_tarski(sK1,k1_relset_1(sK1,sK3,sK4)) = iProver_top
% 3.71/0.92      | r1_tarski(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)) != iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_4210]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_0,plain,
% 3.71/0.92      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.71/0.92      inference(cnf_transformation,[],[f50]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4,plain,
% 3.71/0.92      ( v1_xboole_0(k1_xboole_0) ),
% 3.71/0.92      inference(cnf_transformation,[],[f54]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_430,plain,
% 3.71/0.92      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.71/0.92      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_431,plain,
% 3.71/0.92      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.71/0.92      inference(unflattening,[status(thm)],[c_430]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4693,plain,
% 3.71/0.92      ( ~ r2_hidden(sK0(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)),k1_xboole_0) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_431]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4696,plain,
% 3.71/0.92      ( r2_hidden(sK0(k1_xboole_0,k1_relset_1(sK1,sK3,sK4)),k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_4693]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5292,plain,
% 3.71/0.92      ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(global_propositional_subsumption,
% 3.71/0.92                [status(thm)],
% 3.71/0.92                [c_5236,c_33,c_100,c_101,c_542,c_636,c_1708,c_1788,c_1789,
% 3.71/0.92                 c_1795,c_2221,c_2223,c_2224,c_2402,c_2423,c_2649,c_2756,
% 3.71/0.92                 c_2767,c_2896,c_3615,c_3864,c_4180,c_4212,c_4696]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1798,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.71/0.92      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_8,c_1451]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5299,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(k6_relat_1(sK1)),X0) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_5292,c_1798]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5327,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,X0) = iProver_top
% 3.71/0.92      | v1_relat_1(k6_relat_1(sK1)) != iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_5299,c_20]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_7688,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,X0) = iProver_top ),
% 3.71/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_5327,c_2962]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_7852,plain,
% 3.71/0.92      ( r1_tarski(sK1,X0) = iProver_top
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_5535,c_7688]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_7965,plain,
% 3.71/0.92      ( r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_7852]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5238,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(sK4))),X0) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(k6_relat_1(k1_relat_1(sK4))) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_5231,c_1798]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5266,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(k6_relat_1(k1_relat_1(sK4))) != iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_5238,c_20]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f88]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1465,plain,
% 3.71/0.92      ( r1_tarski(X0,X0) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_4602,plain,
% 3.71/0.92      ( sK2 = k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_3656,c_2679]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5407,plain,
% 3.71/0.92      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | sK2 = k1_xboole_0 ),
% 3.71/0.92      inference(global_propositional_subsumption,[status(thm)],[c_4602,c_2402]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5408,plain,
% 3.71/0.92      ( sK2 = k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_5407]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_5417,plain,
% 3.71/0.92      ( sK2 = k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1465,c_5408]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_6062,plain,
% 3.71/0.92      ( sK2 = k1_xboole_0
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_5417,c_1798]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_7690,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_7688]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8081,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 3.71/0.92      inference(global_propositional_subsumption,
% 3.71/0.92                [status(thm)],
% 3.71/0.92                [c_5266,c_33,c_100,c_101,c_542,c_636,c_1708,c_1788,c_1789,
% 3.71/0.92                 c_1795,c_2221,c_2223,c_2224,c_2402,c_2423,c_2649,c_2756,
% 3.71/0.92                 c_2767,c_2896,c_3615,c_3864,c_4180,c_4212,c_4696,c_6062,
% 3.71/0.92                 c_7690]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8082,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_8081]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8087,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_5535,c_8082]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8102,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) = iProver_top
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_8087]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8101,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),X0)
% 3.71/0.92      | ~ r1_tarski(sK4,k1_xboole_0)
% 3.71/0.92      | ~ v1_relat_1(sK4) ),
% 3.71/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_8087]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8103,plain,
% 3.71/0.92      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0)
% 3.71/0.92      | ~ r1_tarski(sK4,k1_xboole_0)
% 3.71/0.92      | ~ v1_relat_1(sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_8101]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1452,plain,
% 3.71/0.92      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_2793,plain,
% 3.71/0.92      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_1468,c_1452]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8088,plain,
% 3.71/0.92      ( sK2 = k1_xboole_0
% 3.71/0.92      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_3656,c_8082]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_8199,plain,
% 3.71/0.92      ( k1_relat_1(sK4) = X0
% 3.71/0.92      | sK2 = k1_xboole_0
% 3.71/0.92      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_8088,c_1466]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_9280,plain,
% 3.71/0.92      ( k1_relat_1(sK4) = k1_xboole_0
% 3.71/0.92      | sK2 = k1_xboole_0
% 3.71/0.92      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_2793,c_8199]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_9682,plain,
% 3.71/0.92      ( ~ r1_tarski(X0,X1)
% 3.71/0.92      | r1_tarski(X2,k1_relat_1(sK4))
% 3.71/0.92      | X2 != X0
% 3.71/0.92      | k1_relat_1(sK4) != X1 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_845]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_9684,plain,
% 3.71/0.92      ( r1_tarski(k1_xboole_0,k1_relat_1(sK4))
% 3.71/0.92      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.71/0.92      | k1_relat_1(sK4) != k1_xboole_0
% 3.71/0.92      | k1_xboole_0 != k1_xboole_0 ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_9682]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_12398,plain,
% 3.71/0.92      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4)
% 3.71/0.92      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.71/0.92      | v1_relat_1(sK4) != iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_5535,c_12388]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13783,plain,
% 3.71/0.92      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_12957,c_33]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13778,plain,
% 3.71/0.92      ( sK3 = k1_xboole_0
% 3.71/0.92      | r1_tarski(sK4,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 3.71/0.92      inference(superposition,[status(thm)],[c_12957,c_2322]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13795,plain,
% 3.71/0.92      ( sK3 = k1_xboole_0 | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_13778,c_8]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13856,plain,
% 3.71/0.92      ( sK3 = k1_xboole_0 ),
% 3.71/0.92      inference(global_propositional_subsumption,
% 3.71/0.92                [status(thm)],
% 3.71/0.92                [c_13783,c_33,c_100,c_101,c_542,c_636,c_1708,c_1788,c_1789,
% 3.71/0.92                 c_1795,c_2221,c_2223,c_2224,c_2402,c_2423,c_2649,c_2756,
% 3.71/0.92                 c_2767,c_2896,c_3615,c_3864,c_4180,c_4212,c_4696,c_8102,
% 3.71/0.92                 c_12957,c_13795]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13886,plain,
% 3.71/0.92      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_13856,c_3615]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_14053,plain,
% 3.71/0.92      ( r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
% 3.71/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_13886]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_26,plain,
% 3.71/0.92      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.71/0.92      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.71/0.92      | k1_xboole_0 = X0 ),
% 3.71/0.92      inference(cnf_transformation,[],[f93]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_468,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.71/0.92      | sK3 != k1_xboole_0
% 3.71/0.92      | sK1 != X0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | k1_xboole_0 = X0 ),
% 3.71/0.92      inference(resolution_lifted,[status(thm)],[c_26,c_186]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_469,plain,
% 3.71/0.92      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.71/0.92      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.71/0.92      | sK3 != k1_xboole_0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | k1_xboole_0 = sK1 ),
% 3.71/0.92      inference(unflattening,[status(thm)],[c_468]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1450,plain,
% 3.71/0.92      ( sK3 != k1_xboole_0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | k1_xboole_0 = sK1
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.71/0.92      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1607,plain,
% 3.71/0.92      ( sK3 != k1_xboole_0
% 3.71/0.92      | sK1 = k1_xboole_0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.71/0.92      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_1450,c_8]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_97,plain,
% 3.71/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.71/0.92      | r1_tarski(X0,X1) != iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_99,plain,
% 3.71/0.92      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.71/0.92      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_97]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_102,plain,
% 3.71/0.92      ( r1_tarski(X0,X0) = iProver_top ),
% 3.71/0.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_104,plain,
% 3.71/0.92      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_102]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1983,plain,
% 3.71/0.92      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | sK1 = k1_xboole_0
% 3.71/0.92      | sK3 != k1_xboole_0 ),
% 3.71/0.92      inference(global_propositional_subsumption,
% 3.71/0.92                [status(thm)],
% 3.71/0.92                [c_1607,c_99,c_104]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_1984,plain,
% 3.71/0.92      ( sK3 != k1_xboole_0
% 3.71/0.92      | sK1 = k1_xboole_0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.71/0.92      inference(renaming,[status(thm)],[c_1983]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13887,plain,
% 3.71/0.92      ( sK1 = k1_xboole_0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | k1_xboole_0 != k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_13856,c_1984]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13903,plain,
% 3.71/0.92      ( sK1 = k1_xboole_0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.71/0.92      inference(equality_resolution_simp,[status(thm)],[c_13887]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_13907,plain,
% 3.71/0.92      ( sK1 = k1_xboole_0
% 3.71/0.92      | sK4 != k1_xboole_0
% 3.71/0.92      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.71/0.92      inference(demodulation,[status(thm)],[c_13903,c_8]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_14937,plain,
% 3.71/0.92      ( ~ r1_tarski(k1_relat_1(sK4),k1_xboole_0)
% 3.71/0.92      | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK4))
% 3.71/0.92      | k1_xboole_0 = k1_relat_1(sK4) ),
% 3.71/0.92      inference(instantiation,[status(thm)],[c_5]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_16253,plain,
% 3.71/0.92      ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.71/0.92      inference(global_propositional_subsumption,
% 3.71/0.92                [status(thm)],
% 3.71/0.92                [c_13809,c_33,c_99,c_100,c_101,c_103,c_104,c_513,c_542,
% 3.71/0.92                 c_636,c_1607,c_1708,c_1788,c_1789,c_1795,c_2025,c_2221,
% 3.71/0.92                 c_2223,c_2224,c_2402,c_2403,c_2423,c_2649,c_2756,c_2767,
% 3.71/0.92                 c_2802,c_2896,c_3615,c_3864,c_4180,c_4212,c_4241,c_4242,
% 3.71/0.92                 c_4553,c_4696,c_4852,c_7367,c_7965,c_8102,c_8103,c_9280,
% 3.71/0.92                 c_9684,c_12398,c_12957,c_13795,c_13886,c_14053,c_14937]) ).
% 3.71/0.92  
% 3.71/0.92  cnf(c_16258,plain,
% 3.71/0.92      ( $false ),
% 3.71/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_16253,c_2793]) ).
% 3.71/0.92  
% 3.71/0.92  
% 3.71/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/0.92  
% 3.71/0.92  ------                               Statistics
% 3.71/0.92  
% 3.71/0.92  ------ General
% 3.71/0.92  
% 3.71/0.92  abstr_ref_over_cycles:                  0
% 3.71/0.92  abstr_ref_under_cycles:                 0
% 3.71/0.92  gc_basic_clause_elim:                   0
% 3.71/0.92  forced_gc_time:                         0
% 3.71/0.92  parsing_time:                           0.012
% 3.71/0.92  unif_index_cands_time:                  0.
% 3.71/0.92  unif_index_add_time:                    0.
% 3.71/0.92  orderings_time:                         0.
% 3.71/0.92  out_proof_time:                         0.02
% 3.71/0.92  total_time:                             0.451
% 3.71/0.92  num_of_symbols:                         52
% 3.71/0.92  num_of_terms:                           13144
% 3.71/0.92  
% 3.71/0.92  ------ Preprocessing
% 3.71/0.92  
% 3.71/0.92  num_of_splits:                          0
% 3.71/0.92  num_of_split_atoms:                     0
% 3.71/0.92  num_of_reused_defs:                     0
% 3.71/0.92  num_eq_ax_congr_red:                    14
% 3.71/0.92  num_of_sem_filtered_clauses:            2
% 3.71/0.92  num_of_subtypes:                        0
% 3.71/0.92  monotx_restored_types:                  0
% 3.71/0.92  sat_num_of_epr_types:                   0
% 3.71/0.92  sat_num_of_non_cyclic_types:            0
% 3.71/0.92  sat_guarded_non_collapsed_types:        0
% 3.71/0.92  num_pure_diseq_elim:                    0
% 3.71/0.92  simp_replaced_by:                       0
% 3.71/0.92  res_preprocessed:                       158
% 3.71/0.92  prep_upred:                             0
% 3.71/0.92  prep_unflattend:                        34
% 3.71/0.92  smt_new_axioms:                         0
% 3.71/0.92  pred_elim_cands:                        4
% 3.71/0.92  pred_elim:                              3
% 3.71/0.92  pred_elim_cl:                           4
% 3.71/0.92  pred_elim_cycles:                       5
% 3.71/0.92  merged_defs:                            8
% 3.71/0.92  merged_defs_ncl:                        0
% 3.71/0.92  bin_hyper_res:                          9
% 3.71/0.92  prep_cycles:                            4
% 3.71/0.92  pred_elim_time:                         0.004
% 3.71/0.92  splitting_time:                         0.
% 3.71/0.92  sem_filter_time:                        0.
% 3.71/0.92  monotx_time:                            0.
% 3.71/0.92  subtype_inf_time:                       0.
% 3.71/0.92  
% 3.71/0.92  ------ Problem properties
% 3.71/0.92  
% 3.71/0.92  clauses:                                32
% 3.71/0.92  conjectures:                            3
% 3.71/0.92  epr:                                    6
% 3.71/0.92  horn:                                   28
% 3.71/0.92  ground:                                 10
% 3.71/0.92  unary:                                  10
% 3.71/0.92  binary:                                 9
% 3.71/0.92  lits:                                   72
% 3.71/0.92  lits_eq:                                31
% 3.71/0.92  fd_pure:                                0
% 3.71/0.92  fd_pseudo:                              0
% 3.71/0.92  fd_cond:                                3
% 3.71/0.92  fd_pseudo_cond:                         1
% 3.71/0.92  ac_symbols:                             0
% 3.71/0.92  
% 3.71/0.92  ------ Propositional Solver
% 3.71/0.92  
% 3.71/0.92  prop_solver_calls:                      30
% 3.71/0.92  prop_fast_solver_calls:                 1394
% 3.71/0.92  smt_solver_calls:                       0
% 3.71/0.92  smt_fast_solver_calls:                  0
% 3.71/0.92  prop_num_of_clauses:                    6185
% 3.71/0.92  prop_preprocess_simplified:             14194
% 3.71/0.92  prop_fo_subsumed:                       48
% 3.71/0.92  prop_solver_time:                       0.
% 3.71/0.92  smt_solver_time:                        0.
% 3.71/0.92  smt_fast_solver_time:                   0.
% 3.71/0.92  prop_fast_solver_time:                  0.
% 3.71/0.92  prop_unsat_core_time:                   0.
% 3.71/0.92  
% 3.71/0.92  ------ QBF
% 3.71/0.92  
% 3.71/0.92  qbf_q_res:                              0
% 3.71/0.92  qbf_num_tautologies:                    0
% 3.71/0.92  qbf_prep_cycles:                        0
% 3.71/0.92  
% 3.71/0.92  ------ BMC1
% 3.71/0.92  
% 3.71/0.92  bmc1_current_bound:                     -1
% 3.71/0.92  bmc1_last_solved_bound:                 -1
% 3.71/0.92  bmc1_unsat_core_size:                   -1
% 3.71/0.92  bmc1_unsat_core_parents_size:           -1
% 3.71/0.92  bmc1_merge_next_fun:                    0
% 3.71/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.71/0.92  
% 3.71/0.92  ------ Instantiation
% 3.71/0.92  
% 3.71/0.92  inst_num_of_clauses:                    1833
% 3.71/0.92  inst_num_in_passive:                    823
% 3.71/0.92  inst_num_in_active:                     769
% 3.71/0.92  inst_num_in_unprocessed:                243
% 3.71/0.92  inst_num_of_loops:                      1070
% 3.71/0.92  inst_num_of_learning_restarts:          0
% 3.71/0.92  inst_num_moves_active_passive:          296
% 3.71/0.92  inst_lit_activity:                      0
% 3.71/0.92  inst_lit_activity_moves:                0
% 3.71/0.92  inst_num_tautologies:                   0
% 3.71/0.92  inst_num_prop_implied:                  0
% 3.71/0.92  inst_num_existing_simplified:           0
% 3.71/0.92  inst_num_eq_res_simplified:             0
% 3.71/0.92  inst_num_child_elim:                    0
% 3.71/0.92  inst_num_of_dismatching_blockings:      691
% 3.71/0.92  inst_num_of_non_proper_insts:           1760
% 3.71/0.92  inst_num_of_duplicates:                 0
% 3.71/0.92  inst_inst_num_from_inst_to_res:         0
% 3.71/0.92  inst_dismatching_checking_time:         0.
% 3.71/0.92  
% 3.71/0.92  ------ Resolution
% 3.71/0.92  
% 3.71/0.92  res_num_of_clauses:                     0
% 3.71/0.92  res_num_in_passive:                     0
% 3.71/0.92  res_num_in_active:                      0
% 3.71/0.92  res_num_of_loops:                       162
% 3.71/0.92  res_forward_subset_subsumed:            76
% 3.71/0.92  res_backward_subset_subsumed:           8
% 3.71/0.92  res_forward_subsumed:                   0
% 3.71/0.92  res_backward_subsumed:                  0
% 3.71/0.92  res_forward_subsumption_resolution:     0
% 3.71/0.92  res_backward_subsumption_resolution:    0
% 3.71/0.92  res_clause_to_clause_subsumption:       2027
% 3.71/0.92  res_orphan_elimination:                 0
% 3.71/0.92  res_tautology_del:                      97
% 3.71/0.92  res_num_eq_res_simplified:              1
% 3.71/0.92  res_num_sel_changes:                    0
% 3.71/0.92  res_moves_from_active_to_pass:          0
% 3.71/0.92  
% 3.71/0.92  ------ Superposition
% 3.71/0.92  
% 3.71/0.92  sup_time_total:                         0.
% 3.71/0.92  sup_time_generating:                    0.
% 3.71/0.92  sup_time_sim_full:                      0.
% 3.71/0.92  sup_time_sim_immed:                     0.
% 3.71/0.92  
% 3.71/0.92  sup_num_of_clauses:                     282
% 3.71/0.92  sup_num_in_active:                      169
% 3.71/0.92  sup_num_in_passive:                     113
% 3.71/0.92  sup_num_of_loops:                       213
% 3.71/0.92  sup_fw_superposition:                   334
% 3.71/0.92  sup_bw_superposition:                   186
% 3.71/0.92  sup_immediate_simplified:               149
% 3.71/0.92  sup_given_eliminated:                   3
% 3.71/0.92  comparisons_done:                       0
% 3.71/0.92  comparisons_avoided:                    63
% 3.71/0.92  
% 3.71/0.92  ------ Simplifications
% 3.71/0.92  
% 3.71/0.92  
% 3.71/0.92  sim_fw_subset_subsumed:                 28
% 3.71/0.92  sim_bw_subset_subsumed:                 20
% 3.71/0.92  sim_fw_subsumed:                        22
% 3.71/0.92  sim_bw_subsumed:                        32
% 3.71/0.92  sim_fw_subsumption_res:                 12
% 3.71/0.92  sim_bw_subsumption_res:                 0
% 3.71/0.92  sim_tautology_del:                      21
% 3.71/0.92  sim_eq_tautology_del:                   21
% 3.71/0.92  sim_eq_res_simp:                        1
% 3.71/0.92  sim_fw_demodulated:                     53
% 3.71/0.92  sim_bw_demodulated:                     44
% 3.71/0.92  sim_light_normalised:                   32
% 3.71/0.92  sim_joinable_taut:                      0
% 3.71/0.92  sim_joinable_simp:                      0
% 3.71/0.92  sim_ac_normalised:                      0
% 3.71/0.92  sim_smt_subsumption:                    0
% 3.71/0.92  
%------------------------------------------------------------------------------
