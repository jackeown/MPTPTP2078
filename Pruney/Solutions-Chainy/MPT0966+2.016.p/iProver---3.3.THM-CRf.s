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
% DateTime   : Thu Dec  3 12:00:33 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1849)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f51,plain,
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
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
        | ~ v1_funct_2(sK5,sK2,sK4)
        | ~ v1_funct_1(sK5) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
      | ~ v1_funct_2(sK5,sK2,sK4)
      | ~ v1_funct_1(sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f51])).

fof(f87,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f42])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f97,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_574,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_576,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_36])).

cnf(c_1504,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1509,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3935,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1504,c_1509])).

cnf(c_4223,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_576,c_3935])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_16])).

cnf(c_1501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1848,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1501])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1508,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3442,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1504,c_1508])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1505,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3696,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3442,c_1505])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1507,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3933,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_1509])).

cnf(c_10550,plain,
    ( k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5)
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3696,c_3933])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1513,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2363,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1513])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_266,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_267])).

cnf(c_1503,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2664,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2363,c_1503])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1512,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2992,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2664,c_1512])).

cnf(c_11529,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10550,c_2992])).

cnf(c_11530,plain,
    ( k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5)
    | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11529])).

cnf(c_11539,plain,
    ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_11530])).

cnf(c_2280,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2281,plain,
    ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2280])).

cnf(c_2599,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),sK2)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2601,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2599])).

cnf(c_12065,plain,
    ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11539,c_1848,c_2281,c_2601,c_2992,c_3696])).

cnf(c_30,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_191,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_38])).

cnf(c_192,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK4 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_192])).

cnf(c_561,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(sK2,sK4,sK5) != sK2
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_1496,plain,
    ( k1_relset_1(sK2,sK4,sK5) != sK2
    | k1_xboole_0 = sK4
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_12068,plain,
    ( k1_relat_1(sK5) != sK2
    | sK4 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12065,c_1496])).

cnf(c_12099,plain,
    ( sK4 = k1_xboole_0
    | k1_relat_1(sK5) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12068,c_1849,c_2599,c_2993,c_3704,c_12069])).

cnf(c_12100,plain,
    ( k1_relat_1(sK5) != sK2
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_12099])).

cnf(c_12103,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4223,c_12100])).

cnf(c_12414,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12103,c_1504])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_12422,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12414,c_8])).

cnf(c_584,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | sK3 != sK4
    | sK2 != sK2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_192,c_37])).

cnf(c_585,plain,
    ( sK3 != sK4
    | sK2 != sK2
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_873,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1771,plain,
    ( sK3 != X0
    | sK3 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_1772,plain,
    ( sK3 = sK4
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_872,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1859,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_2758,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1515,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3404,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1507])).

cnf(c_4712,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4223,c_3404])).

cnf(c_4786,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4712,c_2992])).

cnf(c_4787,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4786])).

cnf(c_4796,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_4787])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2832,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1501])).

cnf(c_5194,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2832])).

cnf(c_5215,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4223,c_5194])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_106,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_108,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_874,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1839,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_1840,plain,
    ( sK2 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1839])).

cnf(c_1842,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_1770,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_1858,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_2473,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_2474,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2473])).

cnf(c_5712,plain,
    ( r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5215,c_34,c_104,c_105,c_108,c_1842,c_1858,c_1859,c_2474,c_2992])).

cnf(c_5713,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5712])).

cnf(c_12410,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12103,c_2363])).

cnf(c_12427,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12410,c_8])).

cnf(c_2692,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2693,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2692])).

cnf(c_2695,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2693])).

cnf(c_3403,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1507])).

cnf(c_4663,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_3403])).

cnf(c_12415,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12103,c_34])).

cnf(c_12717,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12415,c_3696])).

cnf(c_12785,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12427,c_104,c_105,c_108,c_657,c_1772,c_1842,c_1848,c_2601,c_2695,c_2992,c_3696,c_4663,c_4796,c_12422,c_12717])).

cnf(c_12860,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12422,c_104,c_105,c_108,c_657,c_1772,c_1842,c_1848,c_2601,c_2992,c_3696,c_4663,c_4796,c_12717])).

cnf(c_1851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1501])).

cnf(c_12866,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_12860,c_1851])).

cnf(c_12918,plain,
    ( r1_tarski(k1_relat_1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12866])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1517,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_267])).

cnf(c_446,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_331])).

cnf(c_447,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_1502,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_2272,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1502])).

cnf(c_12807,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12785,c_2272])).

cnf(c_27,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_488,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | sK2 != X0
    | sK5 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_192])).

cnf(c_489,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1500,plain,
    ( sK4 != k1_xboole_0
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_1664,plain,
    ( sK4 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1500,c_8])).

cnf(c_101,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_103,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_2043,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | sK5 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_103,c_108])).

cnf(c_2044,plain,
    ( sK4 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2043])).

cnf(c_12718,plain,
    ( sK2 = k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12415,c_2044])).

cnf(c_8698,plain,
    ( ~ r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5))
    | ~ r1_tarski(k1_relset_1(sK2,sK4,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_8699,plain,
    ( r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5)) != iProver_top
    | r1_tarski(k1_relset_1(sK2,sK4,sK5),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8698])).

cnf(c_3724,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relset_1(sK2,sK4,sK5),X2)
    | X2 != X1
    | k1_relset_1(sK2,sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_8549,plain,
    ( r1_tarski(k1_relset_1(sK2,sK4,sK5),X0)
    | ~ r1_tarski(k1_relat_1(sK5),X1)
    | X0 != X1
    | k1_relset_1(sK2,sK4,sK5) != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3724])).

cnf(c_8550,plain,
    ( X0 != X1
    | k1_relset_1(sK2,sK4,sK5) != k1_relat_1(sK5)
    | r1_tarski(k1_relset_1(sK2,sK4,sK5),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK5),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8549])).

cnf(c_8552,plain,
    ( k1_relset_1(sK2,sK4,sK5) != k1_relat_1(sK5)
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relset_1(sK2,sK4,sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8550])).

cnf(c_7848,plain,
    ( k1_relset_1(X0,X1,X2) != X3
    | k1_xboole_0 != X3
    | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_7849,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7848])).

cnf(c_2875,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_4569,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2875])).

cnf(c_4570,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_4569])).

cnf(c_882,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_4129,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_relset_1(X0,X1,X2)
    | sK4 != X1
    | sK5 != X2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_4131,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0
    | sK5 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4129])).

cnf(c_3760,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) != X0
    | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_4128,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_relset_1(X0,X1,X2)
    | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_3760])).

cnf(c_4130,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4128])).

cnf(c_26,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1506,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2090,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1506])).

cnf(c_2364,plain,
    ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2090,c_1513])).

cnf(c_2576,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2364,c_2272])).

cnf(c_3934,plain,
    ( k1_relset_1(X0,X0,k6_relat_1(X0)) = k1_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1506,c_1509])).

cnf(c_21,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3949,plain,
    ( k1_relset_1(X0,X0,k6_relat_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3934,c_21])).

cnf(c_4102,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2576,c_3949])).

cnf(c_4019,plain,
    ( r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5))
    | k1_xboole_0 = k1_relset_1(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4020,plain,
    ( k1_xboole_0 = k1_relset_1(sK2,sK4,sK5)
    | r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4019])).

cnf(c_2873,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_2285,plain,
    ( X0 != X1
    | k1_relset_1(sK2,sK4,sK5) != X1
    | k1_relset_1(sK2,sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_2826,plain,
    ( X0 != k1_relset_1(sK2,sK4,sK5)
    | k1_relset_1(sK2,sK4,sK5) = X0
    | k1_relset_1(sK2,sK4,sK5) != k1_relset_1(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_2827,plain,
    ( k1_relset_1(sK2,sK4,sK5) != k1_relset_1(sK2,sK4,sK5)
    | k1_relset_1(sK2,sK4,sK5) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2826])).

cnf(c_2284,plain,
    ( k1_relset_1(sK2,sK4,sK5) = k1_relset_1(sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_1989,plain,
    ( k1_relset_1(sK2,sK4,sK5) != X0
    | k1_relset_1(sK2,sK4,sK5) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_1990,plain,
    ( k1_relset_1(sK2,sK4,sK5) = sK2
    | k1_relset_1(sK2,sK4,sK5) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK4 != X1
    | sK2 != k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_192])).

cnf(c_532,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_1498,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_1655,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1498,c_9])).

cnf(c_562,plain,
    ( k1_relset_1(sK2,sK4,sK5) != sK2
    | k1_xboole_0 = sK4
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12918,c_12860,c_12807,c_12718,c_8699,c_8552,c_7849,c_4570,c_4131,c_4130,c_4102,c_4020,c_3696,c_2992,c_2873,c_2827,c_2601,c_2284,c_2281,c_1990,c_1848,c_1655,c_562,c_105,c_104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:38:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.59/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/0.98  
% 3.59/0.98  ------  iProver source info
% 3.59/0.98  
% 3.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/0.98  git: non_committed_changes: false
% 3.59/0.98  git: last_make_outside_of_git: false
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    --mode clausify
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         false
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     num_symb
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       true
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     false
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   []
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_full_bw                           [BwDemod]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  ------ Parsing...
% 3.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/0.98  ------ Proving...
% 3.59/0.98  ------ Problem Properties 
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  clauses                                 33
% 3.59/0.98  conjectures                             3
% 3.59/0.98  EPR                                     6
% 3.59/0.98  Horn                                    28
% 3.59/0.98  unary                                   9
% 3.59/0.98  binary                                  11
% 3.59/0.98  lits                                    75
% 3.59/0.98  lits eq                                 32
% 3.59/0.98  fd_pure                                 0
% 3.59/0.98  fd_pseudo                               0
% 3.59/0.98  fd_cond                                 4
% 3.59/0.98  fd_pseudo_cond                          1
% 3.59/0.98  AC symbols                              0
% 3.59/0.98  
% 3.59/0.98  ------ Schedule dynamic 5 is on 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  Current options:
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    --mode clausify
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         false
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     none
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       false
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     false
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   []
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_full_bw                           [BwDemod]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ Proving...
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS status Theorem for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  fof(f18,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f34,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f18])).
% 3.59/0.98  
% 3.59/0.98  fof(f35,plain,(
% 3.59/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(flattening,[],[f34])).
% 3.59/0.98  
% 3.59/0.98  fof(f50,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(nnf_transformation,[],[f35])).
% 3.59/0.98  
% 3.59/0.98  fof(f80,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f50])).
% 3.59/0.98  
% 3.59/0.98  fof(f19,conjecture,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f20,negated_conjecture,(
% 3.59/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.59/0.98    inference(negated_conjecture,[],[f19])).
% 3.59/0.98  
% 3.59/0.98  fof(f36,plain,(
% 3.59/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.59/0.98    inference(ennf_transformation,[],[f20])).
% 3.59/0.98  
% 3.59/0.98  fof(f37,plain,(
% 3.59/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.59/0.98    inference(flattening,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f51,plain,(
% 3.59/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f52,plain,(
% 3.59/0.98    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f51])).
% 3.59/0.98  
% 3.59/0.98  fof(f87,plain,(
% 3.59/0.98    v1_funct_2(sK5,sK2,sK3)),
% 3.59/0.98    inference(cnf_transformation,[],[f52])).
% 3.59/0.98  
% 3.59/0.98  fof(f88,plain,(
% 3.59/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.59/0.98    inference(cnf_transformation,[],[f52])).
% 3.59/0.98  
% 3.59/0.98  fof(f14,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f30,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f14])).
% 3.59/0.98  
% 3.59/0.98  fof(f76,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f30])).
% 3.59/0.98  
% 3.59/0.98  fof(f13,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f21,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.59/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.59/0.98  
% 3.59/0.98  fof(f29,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f21])).
% 3.59/0.98  
% 3.59/0.98  fof(f75,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f29])).
% 3.59/0.98  
% 3.59/0.98  fof(f9,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f26,plain,(
% 3.59/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f9])).
% 3.59/0.98  
% 3.59/0.98  fof(f49,plain,(
% 3.59/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f26])).
% 3.59/0.98  
% 3.59/0.98  fof(f68,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f15,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f31,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f15])).
% 3.59/0.98  
% 3.59/0.98  fof(f77,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f31])).
% 3.59/0.98  
% 3.59/0.98  fof(f89,plain,(
% 3.59/0.98    r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4)),
% 3.59/0.98    inference(cnf_transformation,[],[f52])).
% 3.59/0.98  
% 3.59/0.98  fof(f16,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f32,plain,(
% 3.59/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.59/0.98    inference(ennf_transformation,[],[f16])).
% 3.59/0.98  
% 3.59/0.98  fof(f33,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.59/0.98    inference(flattening,[],[f32])).
% 3.59/0.98  
% 3.59/0.98  fof(f78,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f33])).
% 3.59/0.98  
% 3.59/0.98  fof(f6,axiom,(
% 3.59/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f48,plain,(
% 3.59/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.59/0.98    inference(nnf_transformation,[],[f6])).
% 3.59/0.98  
% 3.59/0.98  fof(f64,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f48])).
% 3.59/0.98  
% 3.59/0.98  fof(f8,axiom,(
% 3.59/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f25,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f8])).
% 3.59/0.98  
% 3.59/0.98  fof(f67,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f25])).
% 3.59/0.98  
% 3.59/0.98  fof(f65,plain,(
% 3.59/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f48])).
% 3.59/0.98  
% 3.59/0.98  fof(f10,axiom,(
% 3.59/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f70,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f10])).
% 3.59/0.98  
% 3.59/0.98  fof(f82,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f50])).
% 3.59/0.98  
% 3.59/0.98  fof(f91,plain,(
% 3.59/0.98    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)),
% 3.59/0.98    inference(cnf_transformation,[],[f52])).
% 3.59/0.98  
% 3.59/0.98  fof(f86,plain,(
% 3.59/0.98    v1_funct_1(sK5)),
% 3.59/0.98    inference(cnf_transformation,[],[f52])).
% 3.59/0.98  
% 3.59/0.98  fof(f5,axiom,(
% 3.59/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f46,plain,(
% 3.59/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.59/0.98    inference(nnf_transformation,[],[f5])).
% 3.59/0.98  
% 3.59/0.98  fof(f47,plain,(
% 3.59/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.59/0.98    inference(flattening,[],[f46])).
% 3.59/0.98  
% 3.59/0.98  fof(f63,plain,(
% 3.59/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f94,plain,(
% 3.59/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.59/0.98    inference(equality_resolution,[],[f63])).
% 3.59/0.98  
% 3.59/0.98  fof(f4,axiom,(
% 3.59/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f44,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f4])).
% 3.59/0.98  
% 3.59/0.98  fof(f45,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(flattening,[],[f44])).
% 3.59/0.98  
% 3.59/0.98  fof(f59,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f45])).
% 3.59/0.98  
% 3.59/0.98  fof(f92,plain,(
% 3.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f59])).
% 3.59/0.98  
% 3.59/0.98  fof(f62,plain,(
% 3.59/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f95,plain,(
% 3.59/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f62])).
% 3.59/0.98  
% 3.59/0.98  fof(f90,plain,(
% 3.59/0.98    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 3.59/0.98    inference(cnf_transformation,[],[f52])).
% 3.59/0.98  
% 3.59/0.98  fof(f61,plain,(
% 3.59/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f58,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f45])).
% 3.59/0.98  
% 3.59/0.98  fof(f93,plain,(
% 3.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f58])).
% 3.59/0.98  
% 3.59/0.98  fof(f3,axiom,(
% 3.59/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f23,plain,(
% 3.59/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.59/0.98    inference(ennf_transformation,[],[f3])).
% 3.59/0.98  
% 3.59/0.98  fof(f42,plain,(
% 3.59/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f43,plain,(
% 3.59/0.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f42])).
% 3.59/0.98  
% 3.59/0.98  fof(f57,plain,(
% 3.59/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.59/0.98    inference(cnf_transformation,[],[f43])).
% 3.59/0.98  
% 3.59/0.98  fof(f2,axiom,(
% 3.59/0.98    v1_xboole_0(k1_xboole_0)),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f56,plain,(
% 3.59/0.98    v1_xboole_0(k1_xboole_0)),
% 3.59/0.98    inference(cnf_transformation,[],[f2])).
% 3.59/0.98  
% 3.59/0.98  fof(f7,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f24,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f7])).
% 3.59/0.98  
% 3.59/0.98  fof(f66,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f24])).
% 3.59/0.98  
% 3.59/0.98  fof(f85,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f50])).
% 3.59/0.98  
% 3.59/0.98  fof(f96,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(equality_resolution,[],[f85])).
% 3.59/0.98  
% 3.59/0.98  fof(f97,plain,(
% 3.59/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.59/0.98    inference(equality_resolution,[],[f96])).
% 3.59/0.98  
% 3.59/0.98  fof(f17,axiom,(
% 3.59/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f79,plain,(
% 3.59/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f17])).
% 3.59/0.98  
% 3.59/0.98  fof(f12,axiom,(
% 3.59/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.59/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f73,plain,(
% 3.59/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.59/0.98    inference(cnf_transformation,[],[f12])).
% 3.59/0.98  
% 3.59/0.98  fof(f83,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f50])).
% 3.59/0.98  
% 3.59/0.98  fof(f99,plain,(
% 3.59/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.59/0.98    inference(equality_resolution,[],[f83])).
% 3.59/0.98  
% 3.59/0.98  cnf(c_32,plain,
% 3.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_37,negated_conjecture,
% 3.59/0.98      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_573,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.98      | sK3 != X2
% 3.59/0.98      | sK2 != X1
% 3.59/0.98      | sK5 != X0
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_37]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_574,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.98      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.59/0.98      | k1_xboole_0 = sK3 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_573]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_36,negated_conjecture,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_576,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_574,c_36]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1504,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_23,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1509,plain,
% 3.59/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3935,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1504,c_1509]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4223,plain,
% 3.59/0.98      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_576,c_3935]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_22,plain,
% 3.59/0.98      ( v4_relat_1(X0,X1)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_16,plain,
% 3.59/0.98      ( ~ v4_relat_1(X0,X1)
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_461,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_22,c_16]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1501,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1848,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1504,c_1501]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_24,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1508,plain,
% 3.59/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3442,plain,
% 3.59/0.98      ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1504,c_1508]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_35,negated_conjecture,
% 3.59/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) ),
% 3.59/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1505,plain,
% 3.59/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3696,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_3442,c_1505]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_25,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.59/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1507,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3933,plain,
% 3.59/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.59/0.98      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.59/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1507,c_1509]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10550,plain,
% 3.59/0.98      ( k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5)
% 3.59/0.98      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_3696,c_3933]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1513,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2363,plain,
% 3.59/0.98      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1504,c_1513]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_14,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/0.98      | ~ v1_relat_1(X1)
% 3.59/0.98      | v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_266,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.59/0.98      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_267,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_266]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_332,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.59/0.98      inference(bin_hyper_res,[status(thm)],[c_14,c_267]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1503,plain,
% 3.59/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.59/0.98      | v1_relat_1(X1) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2664,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2363,c_1503]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_17,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1512,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2992,plain,
% 3.59/0.98      ( v1_relat_1(sK5) = iProver_top ),
% 3.59/0.98      inference(forward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2664,c_1512]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11529,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 3.59/0.98      | k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_10550,c_2992]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11530,plain,
% 3.59/0.98      ( k1_relset_1(X0,sK4,sK5) = k1_relat_1(sK5)
% 3.59/0.98      | r1_tarski(k1_relat_1(sK5),X0) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_11529]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11539,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5)
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1848,c_11530]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2280,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2281,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5)
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2280]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2599,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | ~ r1_tarski(k2_relat_1(sK5),sK4)
% 3.59/0.98      | ~ r1_tarski(k1_relat_1(sK5),sK2)
% 3.59/0.98      | ~ v1_relat_1(sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2601,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2599]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12065,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_11539,c_1848,c_2281,c_2601,c_2992,c_3696]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_30,plain,
% 3.59/0.98      ( v1_funct_2(X0,X1,X2)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) != X1
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_33,negated_conjecture,
% 3.59/0.98      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | ~ v1_funct_1(sK5) ),
% 3.59/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_38,negated_conjecture,
% 3.59/0.98      ( v1_funct_1(sK5) ),
% 3.59/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_191,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | ~ v1_funct_2(sK5,sK2,sK4) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_33,c_38]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_192,negated_conjecture,
% 3.59/0.98      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_191]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_560,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) != X1
% 3.59/0.98      | sK4 != X2
% 3.59/0.98      | sK2 != X1
% 3.59/0.98      | sK5 != X0
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_192]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_561,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) != sK2
% 3.59/0.98      | k1_xboole_0 = sK4 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_560]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1496,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) != sK2
% 3.59/0.98      | k1_xboole_0 = sK4
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12068,plain,
% 3.59/0.98      ( k1_relat_1(sK5) != sK2
% 3.59/0.98      | sK4 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_12065,c_1496]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12099,plain,
% 3.59/0.98      ( sK4 = k1_xboole_0 | k1_relat_1(sK5) != sK2 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_12068,c_1849,c_2599,c_2993,c_3704,c_12069]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12100,plain,
% 3.59/0.98      ( k1_relat_1(sK5) != sK2 | sK4 = k1_xboole_0 ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_12099]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12103,plain,
% 3.59/0.98      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_4223,c_12100]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12414,plain,
% 3.59/0.98      ( sK4 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_12103,c_1504]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8,plain,
% 3.59/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12422,plain,
% 3.59/0.98      ( sK4 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_12414,c_8]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_584,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | sK3 != sK4
% 3.59/0.98      | sK2 != sK2
% 3.59/0.98      | sK5 != sK5 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_192,c_37]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_585,plain,
% 3.59/0.98      ( sK3 != sK4
% 3.59/0.98      | sK2 != sK2
% 3.59/0.98      | sK5 != sK5
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_873,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1771,plain,
% 3.59/0.98      ( sK3 != X0 | sK3 = sK4 | sK4 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1772,plain,
% 3.59/0.98      ( sK3 = sK4 | sK3 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1771]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_872,plain,( X0 = X0 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1859,plain,
% 3.59/0.98      ( sK2 = sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_872]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2758,plain,
% 3.59/0.98      ( sK5 = sK5 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_872]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1515,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9,plain,
% 3.59/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3404,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_9,c_1507]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4712,plain,
% 3.59/0.98      ( sK3 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_4223,c_3404]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4786,plain,
% 3.59/0.98      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | sK3 = k1_xboole_0 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_4712,c_2992]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4787,plain,
% 3.59/0.98      ( sK3 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_4786]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4796,plain,
% 3.59/0.98      ( sK3 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1515,c_4787]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1514,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2832,plain,
% 3.59/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1514,c_1501]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5194,plain,
% 3.59/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_9,c_2832]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5215,plain,
% 3.59/0.98      ( sK3 = k1_xboole_0
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top
% 3.59/0.98      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_4223,c_5194]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_34,negated_conjecture,
% 3.59/0.98      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10,plain,
% 3.59/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = X0
% 3.59/0.98      | k1_xboole_0 = X1 ),
% 3.59/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_104,plain,
% 3.59/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_105,plain,
% 3.59/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_106,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_108,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_106]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_874,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1839,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1)
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0)
% 3.59/0.98      | sK2 != X0
% 3.59/0.98      | k1_xboole_0 != X1 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_874]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1840,plain,
% 3.59/0.98      ( sK2 != X0
% 3.59/0.98      | k1_xboole_0 != X1
% 3.59/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1839]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1842,plain,
% 3.59/0.98      ( sK2 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top
% 3.59/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1840]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1770,plain,
% 3.59/0.98      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1858,plain,
% 3.59/0.98      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1770]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2473,plain,
% 3.59/0.98      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2474,plain,
% 3.59/0.98      ( sK3 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = sK3
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2473]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5712,plain,
% 3.59/0.98      ( r1_tarski(sK5,k1_xboole_0) != iProver_top
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_5215,c_34,c_104,c_105,c_108,c_1842,c_1858,c_1859,
% 3.59/0.98                 c_2474,c_2992]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5713,plain,
% 3.59/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top
% 3.59/0.98      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_5712]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12410,plain,
% 3.59/0.98      ( sK4 = k1_xboole_0
% 3.59/0.98      | r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_12103,c_2363]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12427,plain,
% 3.59/0.98      ( sK4 = k1_xboole_0 | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_12410,c_8]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2692,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2693,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.59/0.98      | r1_tarski(sK5,X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2692]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2695,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.59/0.98      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2693]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3403,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_8,c_1507]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4663,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1848,c_3403]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12415,plain,
% 3.59/0.98      ( sK4 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_12103,c_34]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12717,plain,
% 3.59/0.98      ( sK2 = k1_xboole_0
% 3.59/0.98      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_12415,c_3696]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12785,plain,
% 3.59/0.98      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_12427,c_104,c_105,c_108,c_657,c_1772,c_1842,c_1848,
% 3.59/0.98                 c_2601,c_2695,c_2992,c_3696,c_4663,c_4796,c_12422,
% 3.59/0.98                 c_12717]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12860,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_12422,c_104,c_105,c_108,c_657,c_1772,c_1842,c_1848,
% 3.59/0.98                 c_2601,c_2992,c_3696,c_4663,c_4796,c_12717]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1851,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_8,c_1501]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12866,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(sK5),X0) = iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_12860,c_1851]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12918,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(sK5),k1_xboole_0) = iProver_top
% 3.59/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_12866]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4,plain,
% 3.59/0.98      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1517,plain,
% 3.59/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3,plain,
% 3.59/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_13,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/0.98      | ~ r2_hidden(X2,X0)
% 3.59/0.98      | ~ v1_xboole_0(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_331,plain,
% 3.59/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.59/0.98      inference(bin_hyper_res,[status(thm)],[c_13,c_267]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_446,plain,
% 3.59/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_331]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_447,plain,
% 3.59/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_446]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1502,plain,
% 3.59/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.59/0.98      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2272,plain,
% 3.59/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1517,c_1502]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12807,plain,
% 3.59/0.98      ( sK5 = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_12785,c_2272]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_27,plain,
% 3.59/0.98      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.59/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.59/0.98      | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_488,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.59/0.98      | sK4 != k1_xboole_0
% 3.59/0.98      | sK2 != X0
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_192]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_489,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.59/0.98      | sK4 != k1_xboole_0
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = sK2 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_488]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1500,plain,
% 3.59/0.98      ( sK4 != k1_xboole_0
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = sK2
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.59/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1664,plain,
% 3.59/0.98      ( sK4 != k1_xboole_0
% 3.59/0.98      | sK2 = k1_xboole_0
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.59/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_1500,c_8]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_101,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_103,plain,
% 3.59/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_101]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2043,plain,
% 3.59/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | sK2 = k1_xboole_0
% 3.59/0.98      | sK4 != k1_xboole_0 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_1664,c_103,c_108]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2044,plain,
% 3.59/0.98      ( sK4 != k1_xboole_0
% 3.59/0.98      | sK2 = k1_xboole_0
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_2043]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12718,plain,
% 3.59/0.98      ( sK2 = k1_xboole_0
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_12415,c_2044]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8698,plain,
% 3.59/0.98      ( ~ r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5))
% 3.59/0.98      | ~ r1_tarski(k1_relset_1(sK2,sK4,sK5),k1_xboole_0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_447]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8699,plain,
% 3.59/0.98      ( r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5)) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relset_1(sK2,sK4,sK5),k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_8698]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3724,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1)
% 3.59/0.98      | r1_tarski(k1_relset_1(sK2,sK4,sK5),X2)
% 3.59/0.98      | X2 != X1
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_874]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8549,plain,
% 3.59/0.98      ( r1_tarski(k1_relset_1(sK2,sK4,sK5),X0)
% 3.59/0.98      | ~ r1_tarski(k1_relat_1(sK5),X1)
% 3.59/0.98      | X0 != X1
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) != k1_relat_1(sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_3724]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8550,plain,
% 3.59/0.98      ( X0 != X1
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) != k1_relat_1(sK5)
% 3.59/0.98      | r1_tarski(k1_relset_1(sK2,sK4,sK5),X0) = iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(sK5),X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_8549]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8552,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) != k1_relat_1(sK5)
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0
% 3.59/0.98      | r1_tarski(k1_relset_1(sK2,sK4,sK5),k1_xboole_0) = iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_8550]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7848,plain,
% 3.59/0.98      ( k1_relset_1(X0,X1,X2) != X3
% 3.59/0.98      | k1_xboole_0 != X3
% 3.59/0.98      | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7849,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_7848]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2875,plain,
% 3.59/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4569,plain,
% 3.59/0.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2875]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4570,plain,
% 3.59/0.98      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4569]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_882,plain,
% 3.59/0.98      ( X0 != X1
% 3.59/0.98      | X2 != X3
% 3.59/0.98      | X4 != X5
% 3.59/0.98      | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4129,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_relset_1(X0,X1,X2)
% 3.59/0.98      | sK4 != X1
% 3.59/0.98      | sK5 != X2
% 3.59/0.98      | k1_xboole_0 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_882]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4131,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.59/0.98      | sK4 != k1_xboole_0
% 3.59/0.98      | sK5 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4129]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3760,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK4,sK5) != X0
% 3.59/0.98      | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 3.59/0.98      | k1_xboole_0 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4128,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_relset_1(X0,X1,X2)
% 3.59/0.98      | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 3.59/0.98      | k1_xboole_0 != k1_relset_1(X0,X1,X2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_3760]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4130,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.59/0.98      | k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 3.59/0.98      | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4128]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_26,plain,
% 3.59/0.98      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1506,plain,
% 3.59/0.98      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2090,plain,
% 3.59/0.98      ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_8,c_1506]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2364,plain,
% 3.59/0.98      ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2090,c_1513]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2576,plain,
% 3.59/0.98      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2364,c_2272]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3934,plain,
% 3.59/0.98      ( k1_relset_1(X0,X0,k6_relat_1(X0)) = k1_relat_1(k6_relat_1(X0)) ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1506,c_1509]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_21,plain,
% 3.59/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3949,plain,
% 3.59/0.98      ( k1_relset_1(X0,X0,k6_relat_1(X0)) = X0 ),
% 3.59/0.98      inference(light_normalisation,[status(thm)],[c_3934,c_21]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4102,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2576,c_3949]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4019,plain,
% 3.59/0.98      ( r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5))
% 3.59/0.98      | k1_xboole_0 = k1_relset_1(sK2,sK4,sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4020,plain,
% 3.59/0.98      ( k1_xboole_0 = k1_relset_1(sK2,sK4,sK5)
% 3.59/0.98      | r2_hidden(sK1(k1_relset_1(sK2,sK4,sK5)),k1_relset_1(sK2,sK4,sK5)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_4019]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2873,plain,
% 3.59/0.98      ( sK4 = sK4 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_872]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2285,plain,
% 3.59/0.98      ( X0 != X1
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) != X1
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) = X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2826,plain,
% 3.59/0.98      ( X0 != k1_relset_1(sK2,sK4,sK5)
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) = X0
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) != k1_relset_1(sK2,sK4,sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2285]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2827,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) != k1_relset_1(sK2,sK4,sK5)
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) = k1_xboole_0
% 3.59/0.98      | k1_xboole_0 != k1_relset_1(sK2,sK4,sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2826]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2284,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) = k1_relset_1(sK2,sK4,sK5) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_872]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1989,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) != X0
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) = sK2
% 3.59/0.98      | sK2 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_873]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1990,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) = sK2
% 3.59/0.98      | k1_relset_1(sK2,sK4,sK5) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1989]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_29,plain,
% 3.59/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.59/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_531,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.59/0.98      | sK4 != X1
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | sK5 != X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_192]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_532,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.59/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 3.59/0.98      | k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_531]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1498,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1655,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_1498,c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_562,plain,
% 3.59/0.98      ( k1_relset_1(sK2,sK4,sK5) != sK2
% 3.59/0.98      | k1_xboole_0 = sK4
% 3.59/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(contradiction,plain,
% 3.59/0.98      ( $false ),
% 3.59/0.98      inference(minisat,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_12918,c_12860,c_12807,c_12718,c_8699,c_8552,c_7849,
% 3.59/0.98                 c_4570,c_4131,c_4130,c_4102,c_4020,c_3696,c_2992,c_2873,
% 3.59/0.98                 c_2827,c_2601,c_2284,c_2281,c_1990,c_1848,c_1655,c_562,
% 3.59/0.98                 c_105,c_104]) ).
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  ------                               Statistics
% 3.59/0.98  
% 3.59/0.98  ------ General
% 3.59/0.98  
% 3.59/0.98  abstr_ref_over_cycles:                  0
% 3.59/0.98  abstr_ref_under_cycles:                 0
% 3.59/0.98  gc_basic_clause_elim:                   0
% 3.59/0.98  forced_gc_time:                         0
% 3.59/0.98  parsing_time:                           0.01
% 3.59/0.98  unif_index_cands_time:                  0.
% 3.59/0.98  unif_index_add_time:                    0.
% 3.59/0.98  orderings_time:                         0.
% 3.59/0.98  out_proof_time:                         0.014
% 3.59/0.98  total_time:                             0.344
% 3.59/0.98  num_of_symbols:                         53
% 3.59/0.98  num_of_terms:                           9725
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing
% 3.59/0.98  
% 3.59/0.98  num_of_splits:                          0
% 3.59/0.98  num_of_split_atoms:                     0
% 3.59/0.98  num_of_reused_defs:                     0
% 3.59/0.98  num_eq_ax_congr_red:                    19
% 3.59/0.98  num_of_sem_filtered_clauses:            2
% 3.59/0.98  num_of_subtypes:                        0
% 3.59/0.98  monotx_restored_types:                  0
% 3.59/0.98  sat_num_of_epr_types:                   0
% 3.59/0.98  sat_num_of_non_cyclic_types:            0
% 3.59/0.98  sat_guarded_non_collapsed_types:        0
% 3.59/0.98  num_pure_diseq_elim:                    0
% 3.59/0.98  simp_replaced_by:                       0
% 3.59/0.98  res_preprocessed:                       162
% 3.59/0.98  prep_upred:                             0
% 3.59/0.98  prep_unflattend:                        34
% 3.59/0.98  smt_new_axioms:                         0
% 3.59/0.98  pred_elim_cands:                        4
% 3.59/0.98  pred_elim:                              3
% 3.59/0.98  pred_elim_cl:                           4
% 3.59/0.98  pred_elim_cycles:                       5
% 3.59/0.98  merged_defs:                            8
% 3.59/0.98  merged_defs_ncl:                        0
% 3.59/0.98  bin_hyper_res:                          10
% 3.59/0.98  prep_cycles:                            4
% 3.59/0.98  pred_elim_time:                         0.005
% 3.59/0.98  splitting_time:                         0.
% 3.59/0.98  sem_filter_time:                        0.
% 3.59/0.98  monotx_time:                            0.
% 3.59/0.98  subtype_inf_time:                       0.
% 3.59/0.98  
% 3.59/0.98  ------ Problem properties
% 3.59/0.98  
% 3.59/0.98  clauses:                                33
% 3.59/0.98  conjectures:                            3
% 3.59/0.98  epr:                                    6
% 3.59/0.98  horn:                                   28
% 3.59/0.98  ground:                                 10
% 3.59/0.98  unary:                                  9
% 3.59/0.98  binary:                                 11
% 3.59/0.98  lits:                                   75
% 3.59/0.98  lits_eq:                                32
% 3.59/0.98  fd_pure:                                0
% 3.59/0.98  fd_pseudo:                              0
% 3.59/0.98  fd_cond:                                4
% 3.59/0.98  fd_pseudo_cond:                         1
% 3.59/0.98  ac_symbols:                             0
% 3.59/0.98  
% 3.59/0.98  ------ Propositional Solver
% 3.59/0.98  
% 3.59/0.98  prop_solver_calls:                      29
% 3.59/0.98  prop_fast_solver_calls:                 1282
% 3.59/0.98  smt_solver_calls:                       0
% 3.59/0.98  smt_fast_solver_calls:                  0
% 3.59/0.98  prop_num_of_clauses:                    4765
% 3.59/0.98  prop_preprocess_simplified:             10258
% 3.59/0.98  prop_fo_subsumed:                       35
% 3.59/0.98  prop_solver_time:                       0.
% 3.59/0.98  smt_solver_time:                        0.
% 3.59/0.98  smt_fast_solver_time:                   0.
% 3.59/0.98  prop_fast_solver_time:                  0.
% 3.59/0.98  prop_unsat_core_time:                   0.
% 3.59/0.98  
% 3.59/0.98  ------ QBF
% 3.59/0.98  
% 3.59/0.98  qbf_q_res:                              0
% 3.59/0.98  qbf_num_tautologies:                    0
% 3.59/0.98  qbf_prep_cycles:                        0
% 3.59/0.98  
% 3.59/0.98  ------ BMC1
% 3.59/0.98  
% 3.59/0.98  bmc1_current_bound:                     -1
% 3.59/0.98  bmc1_last_solved_bound:                 -1
% 3.59/0.98  bmc1_unsat_core_size:                   -1
% 3.59/0.98  bmc1_unsat_core_parents_size:           -1
% 3.59/0.98  bmc1_merge_next_fun:                    0
% 3.59/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation
% 3.59/0.98  
% 3.59/0.98  inst_num_of_clauses:                    1519
% 3.59/0.98  inst_num_in_passive:                    152
% 3.59/0.98  inst_num_in_active:                     676
% 3.59/0.98  inst_num_in_unprocessed:                691
% 3.59/0.98  inst_num_of_loops:                      900
% 3.59/0.98  inst_num_of_learning_restarts:          0
% 3.59/0.98  inst_num_moves_active_passive:          221
% 3.59/0.98  inst_lit_activity:                      0
% 3.59/0.98  inst_lit_activity_moves:                0
% 3.59/0.98  inst_num_tautologies:                   0
% 3.59/0.98  inst_num_prop_implied:                  0
% 3.59/0.98  inst_num_existing_simplified:           0
% 3.59/0.98  inst_num_eq_res_simplified:             0
% 3.59/0.98  inst_num_child_elim:                    0
% 3.59/0.98  inst_num_of_dismatching_blockings:      509
% 3.59/0.98  inst_num_of_non_proper_insts:           1425
% 3.59/0.98  inst_num_of_duplicates:                 0
% 3.59/0.98  inst_inst_num_from_inst_to_res:         0
% 3.59/0.98  inst_dismatching_checking_time:         0.
% 3.59/0.98  
% 3.59/0.98  ------ Resolution
% 3.59/0.98  
% 3.59/0.98  res_num_of_clauses:                     0
% 3.59/0.98  res_num_in_passive:                     0
% 3.59/0.98  res_num_in_active:                      0
% 3.59/0.98  res_num_of_loops:                       166
% 3.59/0.98  res_forward_subset_subsumed:            81
% 3.59/0.98  res_backward_subset_subsumed:           2
% 3.59/0.98  res_forward_subsumed:                   0
% 3.59/0.98  res_backward_subsumed:                  0
% 3.59/0.98  res_forward_subsumption_resolution:     0
% 3.59/0.98  res_backward_subsumption_resolution:    0
% 3.59/0.98  res_clause_to_clause_subsumption:       1989
% 3.59/0.98  res_orphan_elimination:                 0
% 3.59/0.98  res_tautology_del:                      131
% 3.59/0.98  res_num_eq_res_simplified:              1
% 3.59/0.98  res_num_sel_changes:                    0
% 3.59/0.98  res_moves_from_active_to_pass:          0
% 3.59/0.98  
% 3.59/0.98  ------ Superposition
% 3.59/0.98  
% 3.59/0.98  sup_time_total:                         0.
% 3.59/0.98  sup_time_generating:                    0.
% 3.59/0.98  sup_time_sim_full:                      0.
% 3.59/0.98  sup_time_sim_immed:                     0.
% 3.59/0.98  
% 3.59/0.98  sup_num_of_clauses:                     304
% 3.59/0.98  sup_num_in_active:                      164
% 3.59/0.98  sup_num_in_passive:                     140
% 3.59/0.98  sup_num_of_loops:                       178
% 3.59/0.98  sup_fw_superposition:                   276
% 3.59/0.98  sup_bw_superposition:                   157
% 3.59/0.98  sup_immediate_simplified:               85
% 3.59/0.98  sup_given_eliminated:                   3
% 3.59/0.98  comparisons_done:                       0
% 3.59/0.98  comparisons_avoided:                    69
% 3.59/0.98  
% 3.59/0.98  ------ Simplifications
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  sim_fw_subset_subsumed:                 16
% 3.59/0.98  sim_bw_subset_subsumed:                 9
% 3.59/0.98  sim_fw_subsumed:                        19
% 3.59/0.98  sim_bw_subsumed:                        7
% 3.59/0.98  sim_fw_subsumption_res:                 4
% 3.59/0.98  sim_bw_subsumption_res:                 3
% 3.59/0.98  sim_tautology_del:                      16
% 3.59/0.98  sim_eq_tautology_del:                   21
% 3.59/0.98  sim_eq_res_simp:                        0
% 3.59/0.98  sim_fw_demodulated:                     28
% 3.59/0.98  sim_bw_demodulated:                     8
% 3.59/0.98  sim_light_normalised:                   29
% 3.59/0.98  sim_joinable_taut:                      0
% 3.59/0.98  sim_joinable_simp:                      0
% 3.59/0.98  sim_ac_normalised:                      0
% 3.59/0.98  sim_smt_subsumption:                    0
% 3.59/0.98  
%------------------------------------------------------------------------------
