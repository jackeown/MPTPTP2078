%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:35 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1509)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f36,plain,
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
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f36])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f65,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1210,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_11])).

cnf(c_1208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1563,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1208])).

cnf(c_13,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1213,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1217,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2709,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1217])).

cnf(c_5506,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_2709])).

cnf(c_1565,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1208])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1220,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2707,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1213])).

cnf(c_4494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_2707])).

cnf(c_8722,plain,
    ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5506,c_1565,c_4494])).

cnf(c_8723,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8722])).

cnf(c_8726,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_8723])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1216,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_19,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1212,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2340,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1217])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_268,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_214])).

cnf(c_1209,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_2638,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_1209])).

cnf(c_3237,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_2638])).

cnf(c_8804,plain,
    ( r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8726,c_3237])).

cnf(c_8805,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8804])).

cnf(c_14,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3943,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1565])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1221,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9301,plain,
    ( k1_relat_1(X0) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3943,c_1221])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2822,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1208])).

cnf(c_6762,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2822])).

cnf(c_8554,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6762,c_1209])).

cnf(c_72,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_74,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_90,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_92,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_1389,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_1390,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_1392,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_721,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1599,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1600,plain,
    ( X0 != X1
    | k2_zfmisc_1(X2,X3) != X4
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1599])).

cnf(c_1602,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1600])).

cnf(c_15027,plain,
    ( v1_relat_1(k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8554,c_74,c_88,c_89,c_92,c_1392,c_1602])).

cnf(c_15028,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_15027])).

cnf(c_15038,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k1_relat_1(k6_relat_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8805,c_15028])).

cnf(c_15044,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15038,c_14])).

cnf(c_15118,plain,
    ( v1_relat_1(X0) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15044,c_3237])).

cnf(c_15119,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_15118])).

cnf(c_19239,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9301,c_3237,c_15044])).

cnf(c_19240,plain,
    ( k1_relat_1(X0) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19239])).

cnf(c_19253,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k6_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_19240])).

cnf(c_19257,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_relat_1(X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19253,c_14])).

cnf(c_19383,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8805,c_19257])).

cnf(c_19700,plain,
    ( k1_relat_1(sK3) = sK0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_19383])).

cnf(c_1280,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1281,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_1283,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_408,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1206,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_1223,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1206,c_4])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_720,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1257,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1312,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_719,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1379,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1470,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1471,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_1790,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1223,c_27,c_88,c_89,c_1312,c_1379,c_1471])).

cnf(c_2341,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1217])).

cnf(c_2349,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_1209])).

cnf(c_2452,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_2349])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_470,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_472,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_29])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1215,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3651,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1210,c_1215])).

cnf(c_3695,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_472,c_3651])).

cnf(c_20066,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19700,c_88,c_89,c_92,c_1283,c_1790,c_2452,c_3695])).

cnf(c_2708,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1213])).

cnf(c_4602,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_2708])).

cnf(c_4605,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4602,c_13])).

cnf(c_4613,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4605,c_3237])).

cnf(c_4614,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4613])).

cnf(c_4622,plain,
    ( m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_4614])).

cnf(c_4941,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4622,c_2452])).

cnf(c_4942,plain,
    ( m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4941])).

cnf(c_4946,plain,
    ( r1_tarski(k6_relat_1(k1_relat_1(sK3)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4942,c_1217])).

cnf(c_1219,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3506,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1221])).

cnf(c_6016,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4946,c_3506])).

cnf(c_8566,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6762,c_6016])).

cnf(c_9064,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top
    | k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8566,c_2452])).

cnf(c_9065,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9064])).

cnf(c_20094,plain,
    ( k6_relat_1(sK0) = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20066,c_9065])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_155,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_31])).

cnf(c_156,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_156])).

cnf(c_457,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_480,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_156,c_30])).

cnf(c_481,plain,
    ( sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1263,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1264,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1263])).

cnf(c_1274,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1275,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_1382,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1564,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1563])).

cnf(c_1475,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1688,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_2352,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_2453,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2452])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1214,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2830,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1210,c_1214])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1211,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3018,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2830,c_1211])).

cnf(c_3020,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3018])).

cnf(c_1661,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_2446,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_4425,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_1313,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1438,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_7045,plain,
    ( k1_relat_1(sK3) != sK0
    | sK0 = k1_relat_1(sK3)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_4945,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3695,c_4942])).

cnf(c_5062,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4945,c_1217])).

cnf(c_8567,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6762,c_5062])).

cnf(c_4947,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(sK3))),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4942,c_1565])).

cnf(c_4956,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4947,c_14])).

cnf(c_2977,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k6_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_2978,plain,
    ( r1_tarski(k6_relat_1(sK0),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2977])).

cnf(c_2980,plain,
    ( r1_tarski(k6_relat_1(sK0),k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(sK0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_5063,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k6_relat_1(sK0)),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(k6_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4945,c_1565])).

cnf(c_5072,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5063,c_14])).

cnf(c_5083,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5072])).

cnf(c_4604,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3695,c_2708])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1254,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1255,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_1623,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1624,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1623])).

cnf(c_1754,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1755,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1754])).

cnf(c_1757,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_1506,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1834,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_2409,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2410,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_1514,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1958,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_2804,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | X0 != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_2805,plain,
    ( X0 != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_2807,plain,
    ( sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2805])).

cnf(c_3746,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_1623])).

cnf(c_3747,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3746])).

cnf(c_2282,plain,
    ( k2_zfmisc_1(sK0,sK1) != X0
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_3888,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(c_3890,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3888])).

cnf(c_722,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_4666,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_4667,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4666])).

cnf(c_5086,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4604,c_34,c_88,c_89,c_1255,c_1382,c_1624,c_1757,c_1834,c_2410,c_2452,c_2807,c_3747,c_3890,c_4667])).

cnf(c_5087,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5086])).

cnf(c_5092,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_5087])).

cnf(c_5381,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5092,c_1565])).

cnf(c_7854,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4956,c_74,c_88,c_89,c_92,c_1283,c_1392,c_1602,c_1790,c_2452,c_2980,c_5062,c_5083,c_5381])).

cnf(c_7855,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7854])).

cnf(c_8561,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6762,c_7855])).

cnf(c_8588,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8561])).

cnf(c_8929,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8567,c_2452,c_5062,c_8588])).

cnf(c_8930,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8929])).

cnf(c_8935,plain,
    ( k6_relat_1(sK0) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8930,c_3506])).

cnf(c_8943,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k6_relat_1(sK0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8935])).

cnf(c_9564,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14851,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1729,plain,
    ( X0 != X1
    | X0 = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_5275,plain,
    ( k1_relset_1(sK0,sK2,sK3) != X0
    | k1_relset_1(sK0,sK2,sK3) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_14967,plain,
    ( k1_relset_1(sK0,sK2,sK3) != k1_relat_1(sK3)
    | k1_relset_1(sK0,sK2,sK3) = sK0
    | sK0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5275])).

cnf(c_19699,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3018,c_19383])).

cnf(c_19716,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k2_relat_1(sK3) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19699])).

cnf(c_19825,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19699,c_88,c_89,c_92,c_457,c_1263,c_1283,c_1379,c_1564,c_1790,c_2352,c_2452,c_2453,c_3020,c_3695,c_4425,c_7045,c_9564,c_14851,c_14967,c_19716,c_19700])).

cnf(c_19842,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19825,c_8723])).

cnf(c_19844,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19842])).

cnf(c_20331,plain,
    ( k6_relat_1(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20094,c_88,c_89,c_92,c_457,c_481,c_1263,c_1264,c_1275,c_1283,c_1379,c_1382,c_1509,c_1563,c_1564,c_1688,c_1790,c_2352,c_2452,c_2453,c_3018,c_3020,c_3695,c_4426,c_7045,c_8935,c_9565,c_14851,c_14967,c_19700,c_19830])).

cnf(c_20377,plain,
    ( k2_relat_1(k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_20331,c_13])).

cnf(c_2003,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1212])).

cnf(c_2342,plain,
    ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_1217])).

cnf(c_3866,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2342,c_3506])).

cnf(c_3879,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3866,c_13])).

cnf(c_20379,plain,
    ( sK0 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20377,c_3879])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_156])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_1205,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1224,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1205,c_5])).

cnf(c_20471,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20379,c_1224])).

cnf(c_20481,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_20471])).

cnf(c_20482,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20481,c_5])).

cnf(c_4426,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK2
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4425])).

cnf(c_9565,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9564])).

cnf(c_19382,plain,
    ( sK1 = k1_xboole_0
    | sK0 = X0
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8930,c_19257])).

cnf(c_19386,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19382])).

cnf(c_4495,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_2707])).

cnf(c_4936,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4495,c_2452])).

cnf(c_4937,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4936])).

cnf(c_19830,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19825,c_4937])).

cnf(c_21065,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20482,c_88,c_89,c_92,c_457,c_1224,c_1263,c_1264,c_1283,c_1379,c_1509,c_1563,c_1564,c_1790,c_2352,c_2452,c_2453,c_3018,c_3020,c_3695,c_4426,c_7045,c_9565,c_14692,c_14851,c_14967,c_19700,c_19830])).

cnf(c_20468,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20379,c_2341])).

cnf(c_20483,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20468,c_5])).

cnf(c_20820,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20483,c_3506])).

cnf(c_19833,plain,
    ( k2_relset_1(sK0,sK1,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_19825,c_2830])).

cnf(c_20407,plain,
    ( k2_relset_1(k1_xboole_0,sK1,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_20379,c_19833])).

cnf(c_20875,plain,
    ( k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_20407,c_20407,c_20820])).

cnf(c_2827,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1214])).

cnf(c_7282,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1219,c_2827])).

cnf(c_7288,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7282,c_3879])).

cnf(c_20876,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20875,c_7288])).

cnf(c_21067,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21065,c_20820,c_20876])).

cnf(c_3648,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1215])).

cnf(c_8539,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1219,c_3648])).

cnf(c_3878,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3866,c_14])).

cnf(c_8546,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8539,c_3878])).

cnf(c_21068,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21067,c_8546])).

cnf(c_21069,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_21068])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:42:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.11/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/1.47  
% 7.11/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.11/1.47  
% 7.11/1.47  ------  iProver source info
% 7.11/1.47  
% 7.11/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.11/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.11/1.47  git: non_committed_changes: false
% 7.11/1.47  git: last_make_outside_of_git: false
% 7.11/1.47  
% 7.11/1.47  ------ 
% 7.11/1.47  
% 7.11/1.47  ------ Input Options
% 7.11/1.47  
% 7.11/1.47  --out_options                           all
% 7.11/1.47  --tptp_safe_out                         true
% 7.11/1.47  --problem_path                          ""
% 7.11/1.47  --include_path                          ""
% 7.11/1.47  --clausifier                            res/vclausify_rel
% 7.11/1.47  --clausifier_options                    ""
% 7.11/1.47  --stdin                                 false
% 7.11/1.47  --stats_out                             all
% 7.11/1.47  
% 7.11/1.47  ------ General Options
% 7.11/1.47  
% 7.11/1.47  --fof                                   false
% 7.11/1.47  --time_out_real                         305.
% 7.11/1.47  --time_out_virtual                      -1.
% 7.11/1.47  --symbol_type_check                     false
% 7.11/1.47  --clausify_out                          false
% 7.11/1.47  --sig_cnt_out                           false
% 7.11/1.47  --trig_cnt_out                          false
% 7.11/1.47  --trig_cnt_out_tolerance                1.
% 7.11/1.47  --trig_cnt_out_sk_spl                   false
% 7.11/1.47  --abstr_cl_out                          false
% 7.11/1.47  
% 7.11/1.47  ------ Global Options
% 7.11/1.47  
% 7.11/1.47  --schedule                              default
% 7.11/1.47  --add_important_lit                     false
% 7.11/1.47  --prop_solver_per_cl                    1000
% 7.11/1.47  --min_unsat_core                        false
% 7.11/1.47  --soft_assumptions                      false
% 7.11/1.47  --soft_lemma_size                       3
% 7.11/1.47  --prop_impl_unit_size                   0
% 7.11/1.47  --prop_impl_unit                        []
% 7.11/1.47  --share_sel_clauses                     true
% 7.11/1.47  --reset_solvers                         false
% 7.11/1.47  --bc_imp_inh                            [conj_cone]
% 7.11/1.47  --conj_cone_tolerance                   3.
% 7.11/1.47  --extra_neg_conj                        none
% 7.11/1.47  --large_theory_mode                     true
% 7.11/1.47  --prolific_symb_bound                   200
% 7.11/1.47  --lt_threshold                          2000
% 7.11/1.47  --clause_weak_htbl                      true
% 7.11/1.47  --gc_record_bc_elim                     false
% 7.11/1.47  
% 7.11/1.47  ------ Preprocessing Options
% 7.11/1.47  
% 7.11/1.47  --preprocessing_flag                    true
% 7.11/1.47  --time_out_prep_mult                    0.1
% 7.11/1.47  --splitting_mode                        input
% 7.11/1.47  --splitting_grd                         true
% 7.11/1.47  --splitting_cvd                         false
% 7.11/1.47  --splitting_cvd_svl                     false
% 7.11/1.47  --splitting_nvd                         32
% 7.11/1.47  --sub_typing                            true
% 7.11/1.47  --prep_gs_sim                           true
% 7.11/1.47  --prep_unflatten                        true
% 7.11/1.47  --prep_res_sim                          true
% 7.11/1.47  --prep_upred                            true
% 7.11/1.47  --prep_sem_filter                       exhaustive
% 7.11/1.47  --prep_sem_filter_out                   false
% 7.11/1.47  --pred_elim                             true
% 7.11/1.47  --res_sim_input                         true
% 7.11/1.47  --eq_ax_congr_red                       true
% 7.11/1.47  --pure_diseq_elim                       true
% 7.11/1.47  --brand_transform                       false
% 7.11/1.47  --non_eq_to_eq                          false
% 7.11/1.47  --prep_def_merge                        true
% 7.11/1.47  --prep_def_merge_prop_impl              false
% 7.11/1.47  --prep_def_merge_mbd                    true
% 7.11/1.47  --prep_def_merge_tr_red                 false
% 7.11/1.47  --prep_def_merge_tr_cl                  false
% 7.11/1.47  --smt_preprocessing                     true
% 7.11/1.47  --smt_ac_axioms                         fast
% 7.11/1.47  --preprocessed_out                      false
% 7.11/1.47  --preprocessed_stats                    false
% 7.11/1.47  
% 7.11/1.47  ------ Abstraction refinement Options
% 7.11/1.47  
% 7.11/1.47  --abstr_ref                             []
% 7.11/1.47  --abstr_ref_prep                        false
% 7.11/1.47  --abstr_ref_until_sat                   false
% 7.11/1.47  --abstr_ref_sig_restrict                funpre
% 7.11/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.47  --abstr_ref_under                       []
% 7.11/1.47  
% 7.11/1.47  ------ SAT Options
% 7.11/1.47  
% 7.11/1.47  --sat_mode                              false
% 7.11/1.47  --sat_fm_restart_options                ""
% 7.11/1.47  --sat_gr_def                            false
% 7.11/1.47  --sat_epr_types                         true
% 7.11/1.47  --sat_non_cyclic_types                  false
% 7.11/1.47  --sat_finite_models                     false
% 7.11/1.47  --sat_fm_lemmas                         false
% 7.11/1.47  --sat_fm_prep                           false
% 7.11/1.47  --sat_fm_uc_incr                        true
% 7.11/1.47  --sat_out_model                         small
% 7.11/1.47  --sat_out_clauses                       false
% 7.11/1.47  
% 7.11/1.47  ------ QBF Options
% 7.11/1.47  
% 7.11/1.47  --qbf_mode                              false
% 7.11/1.47  --qbf_elim_univ                         false
% 7.11/1.47  --qbf_dom_inst                          none
% 7.11/1.47  --qbf_dom_pre_inst                      false
% 7.11/1.47  --qbf_sk_in                             false
% 7.11/1.47  --qbf_pred_elim                         true
% 7.11/1.47  --qbf_split                             512
% 7.11/1.47  
% 7.11/1.47  ------ BMC1 Options
% 7.11/1.47  
% 7.11/1.47  --bmc1_incremental                      false
% 7.11/1.47  --bmc1_axioms                           reachable_all
% 7.11/1.47  --bmc1_min_bound                        0
% 7.11/1.47  --bmc1_max_bound                        -1
% 7.11/1.47  --bmc1_max_bound_default                -1
% 7.11/1.47  --bmc1_symbol_reachability              true
% 7.11/1.47  --bmc1_property_lemmas                  false
% 7.11/1.47  --bmc1_k_induction                      false
% 7.11/1.47  --bmc1_non_equiv_states                 false
% 7.11/1.47  --bmc1_deadlock                         false
% 7.11/1.47  --bmc1_ucm                              false
% 7.11/1.47  --bmc1_add_unsat_core                   none
% 7.11/1.47  --bmc1_unsat_core_children              false
% 7.11/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.47  --bmc1_out_stat                         full
% 7.11/1.47  --bmc1_ground_init                      false
% 7.11/1.47  --bmc1_pre_inst_next_state              false
% 7.11/1.47  --bmc1_pre_inst_state                   false
% 7.11/1.47  --bmc1_pre_inst_reach_state             false
% 7.11/1.47  --bmc1_out_unsat_core                   false
% 7.11/1.47  --bmc1_aig_witness_out                  false
% 7.11/1.47  --bmc1_verbose                          false
% 7.11/1.47  --bmc1_dump_clauses_tptp                false
% 7.11/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.47  --bmc1_dump_file                        -
% 7.11/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.47  --bmc1_ucm_extend_mode                  1
% 7.11/1.47  --bmc1_ucm_init_mode                    2
% 7.11/1.47  --bmc1_ucm_cone_mode                    none
% 7.11/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.47  --bmc1_ucm_relax_model                  4
% 7.11/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.47  --bmc1_ucm_layered_model                none
% 7.11/1.47  --bmc1_ucm_max_lemma_size               10
% 7.11/1.47  
% 7.11/1.47  ------ AIG Options
% 7.11/1.47  
% 7.11/1.47  --aig_mode                              false
% 7.11/1.47  
% 7.11/1.47  ------ Instantiation Options
% 7.11/1.47  
% 7.11/1.47  --instantiation_flag                    true
% 7.11/1.47  --inst_sos_flag                         true
% 7.11/1.47  --inst_sos_phase                        true
% 7.11/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.47  --inst_lit_sel_side                     num_symb
% 7.11/1.47  --inst_solver_per_active                1400
% 7.11/1.47  --inst_solver_calls_frac                1.
% 7.11/1.47  --inst_passive_queue_type               priority_queues
% 7.11/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.47  --inst_passive_queues_freq              [25;2]
% 7.11/1.47  --inst_dismatching                      true
% 7.11/1.47  --inst_eager_unprocessed_to_passive     true
% 7.11/1.47  --inst_prop_sim_given                   true
% 7.11/1.47  --inst_prop_sim_new                     false
% 7.11/1.47  --inst_subs_new                         false
% 7.11/1.47  --inst_eq_res_simp                      false
% 7.11/1.47  --inst_subs_given                       false
% 7.11/1.47  --inst_orphan_elimination               true
% 7.11/1.47  --inst_learning_loop_flag               true
% 7.11/1.47  --inst_learning_start                   3000
% 7.11/1.47  --inst_learning_factor                  2
% 7.11/1.47  --inst_start_prop_sim_after_learn       3
% 7.11/1.47  --inst_sel_renew                        solver
% 7.11/1.47  --inst_lit_activity_flag                true
% 7.11/1.47  --inst_restr_to_given                   false
% 7.11/1.47  --inst_activity_threshold               500
% 7.11/1.47  --inst_out_proof                        true
% 7.11/1.47  
% 7.11/1.47  ------ Resolution Options
% 7.11/1.47  
% 7.11/1.47  --resolution_flag                       true
% 7.11/1.47  --res_lit_sel                           adaptive
% 7.11/1.47  --res_lit_sel_side                      none
% 7.11/1.47  --res_ordering                          kbo
% 7.11/1.47  --res_to_prop_solver                    active
% 7.11/1.47  --res_prop_simpl_new                    false
% 7.11/1.47  --res_prop_simpl_given                  true
% 7.11/1.47  --res_passive_queue_type                priority_queues
% 7.11/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.47  --res_passive_queues_freq               [15;5]
% 7.11/1.47  --res_forward_subs                      full
% 7.11/1.47  --res_backward_subs                     full
% 7.11/1.47  --res_forward_subs_resolution           true
% 7.11/1.47  --res_backward_subs_resolution          true
% 7.11/1.47  --res_orphan_elimination                true
% 7.11/1.47  --res_time_limit                        2.
% 7.11/1.47  --res_out_proof                         true
% 7.11/1.47  
% 7.11/1.47  ------ Superposition Options
% 7.11/1.47  
% 7.11/1.47  --superposition_flag                    true
% 7.11/1.47  --sup_passive_queue_type                priority_queues
% 7.11/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.47  --demod_completeness_check              fast
% 7.11/1.47  --demod_use_ground                      true
% 7.11/1.47  --sup_to_prop_solver                    passive
% 7.11/1.47  --sup_prop_simpl_new                    true
% 7.11/1.47  --sup_prop_simpl_given                  true
% 7.11/1.47  --sup_fun_splitting                     true
% 7.11/1.47  --sup_smt_interval                      50000
% 7.11/1.47  
% 7.11/1.47  ------ Superposition Simplification Setup
% 7.11/1.47  
% 7.11/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.11/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.11/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.11/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.11/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.11/1.47  --sup_immed_triv                        [TrivRules]
% 7.11/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.47  --sup_immed_bw_main                     []
% 7.11/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.11/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.47  --sup_input_bw                          []
% 7.11/1.47  
% 7.11/1.47  ------ Combination Options
% 7.11/1.47  
% 7.11/1.47  --comb_res_mult                         3
% 7.11/1.47  --comb_sup_mult                         2
% 7.11/1.47  --comb_inst_mult                        10
% 7.11/1.47  
% 7.11/1.47  ------ Debug Options
% 7.11/1.47  
% 7.11/1.47  --dbg_backtrace                         false
% 7.11/1.47  --dbg_dump_prop_clauses                 false
% 7.11/1.47  --dbg_dump_prop_clauses_file            -
% 7.11/1.47  --dbg_out_stat                          false
% 7.11/1.47  ------ Parsing...
% 7.11/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.11/1.47  
% 7.11/1.47  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.11/1.47  
% 7.11/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.11/1.47  
% 7.11/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.11/1.47  ------ Proving...
% 7.11/1.47  ------ Problem Properties 
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  clauses                                 27
% 7.11/1.47  conjectures                             3
% 7.11/1.47  EPR                                     5
% 7.11/1.47  Horn                                    24
% 7.11/1.47  unary                                   10
% 7.11/1.47  binary                                  7
% 7.11/1.47  lits                                    59
% 7.11/1.47  lits eq                                 27
% 7.11/1.47  fd_pure                                 0
% 7.11/1.47  fd_pseudo                               0
% 7.11/1.47  fd_cond                                 1
% 7.11/1.47  fd_pseudo_cond                          1
% 7.11/1.47  AC symbols                              0
% 7.11/1.47  
% 7.11/1.47  ------ Schedule dynamic 5 is on 
% 7.11/1.47  
% 7.11/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  ------ 
% 7.11/1.47  Current options:
% 7.11/1.47  ------ 
% 7.11/1.47  
% 7.11/1.47  ------ Input Options
% 7.11/1.47  
% 7.11/1.47  --out_options                           all
% 7.11/1.47  --tptp_safe_out                         true
% 7.11/1.47  --problem_path                          ""
% 7.11/1.47  --include_path                          ""
% 7.11/1.47  --clausifier                            res/vclausify_rel
% 7.11/1.47  --clausifier_options                    ""
% 7.11/1.47  --stdin                                 false
% 7.11/1.47  --stats_out                             all
% 7.11/1.47  
% 7.11/1.47  ------ General Options
% 7.11/1.47  
% 7.11/1.47  --fof                                   false
% 7.11/1.47  --time_out_real                         305.
% 7.11/1.47  --time_out_virtual                      -1.
% 7.11/1.47  --symbol_type_check                     false
% 7.11/1.47  --clausify_out                          false
% 7.11/1.47  --sig_cnt_out                           false
% 7.11/1.47  --trig_cnt_out                          false
% 7.11/1.47  --trig_cnt_out_tolerance                1.
% 7.11/1.47  --trig_cnt_out_sk_spl                   false
% 7.11/1.47  --abstr_cl_out                          false
% 7.11/1.47  
% 7.11/1.47  ------ Global Options
% 7.11/1.47  
% 7.11/1.47  --schedule                              default
% 7.11/1.47  --add_important_lit                     false
% 7.11/1.47  --prop_solver_per_cl                    1000
% 7.11/1.47  --min_unsat_core                        false
% 7.11/1.47  --soft_assumptions                      false
% 7.11/1.47  --soft_lemma_size                       3
% 7.11/1.47  --prop_impl_unit_size                   0
% 7.11/1.47  --prop_impl_unit                        []
% 7.11/1.47  --share_sel_clauses                     true
% 7.11/1.47  --reset_solvers                         false
% 7.11/1.47  --bc_imp_inh                            [conj_cone]
% 7.11/1.47  --conj_cone_tolerance                   3.
% 7.11/1.47  --extra_neg_conj                        none
% 7.11/1.47  --large_theory_mode                     true
% 7.11/1.47  --prolific_symb_bound                   200
% 7.11/1.47  --lt_threshold                          2000
% 7.11/1.47  --clause_weak_htbl                      true
% 7.11/1.47  --gc_record_bc_elim                     false
% 7.11/1.47  
% 7.11/1.47  ------ Preprocessing Options
% 7.11/1.47  
% 7.11/1.47  --preprocessing_flag                    true
% 7.11/1.47  --time_out_prep_mult                    0.1
% 7.11/1.47  --splitting_mode                        input
% 7.11/1.47  --splitting_grd                         true
% 7.11/1.47  --splitting_cvd                         false
% 7.11/1.47  --splitting_cvd_svl                     false
% 7.11/1.47  --splitting_nvd                         32
% 7.11/1.47  --sub_typing                            true
% 7.11/1.47  --prep_gs_sim                           true
% 7.11/1.47  --prep_unflatten                        true
% 7.11/1.47  --prep_res_sim                          true
% 7.11/1.47  --prep_upred                            true
% 7.11/1.47  --prep_sem_filter                       exhaustive
% 7.11/1.47  --prep_sem_filter_out                   false
% 7.11/1.47  --pred_elim                             true
% 7.11/1.47  --res_sim_input                         true
% 7.11/1.47  --eq_ax_congr_red                       true
% 7.11/1.47  --pure_diseq_elim                       true
% 7.11/1.47  --brand_transform                       false
% 7.11/1.47  --non_eq_to_eq                          false
% 7.11/1.47  --prep_def_merge                        true
% 7.11/1.47  --prep_def_merge_prop_impl              false
% 7.11/1.47  --prep_def_merge_mbd                    true
% 7.11/1.47  --prep_def_merge_tr_red                 false
% 7.11/1.47  --prep_def_merge_tr_cl                  false
% 7.11/1.47  --smt_preprocessing                     true
% 7.11/1.47  --smt_ac_axioms                         fast
% 7.11/1.47  --preprocessed_out                      false
% 7.11/1.47  --preprocessed_stats                    false
% 7.11/1.47  
% 7.11/1.47  ------ Abstraction refinement Options
% 7.11/1.47  
% 7.11/1.47  --abstr_ref                             []
% 7.11/1.47  --abstr_ref_prep                        false
% 7.11/1.47  --abstr_ref_until_sat                   false
% 7.11/1.47  --abstr_ref_sig_restrict                funpre
% 7.11/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.47  --abstr_ref_under                       []
% 7.11/1.47  
% 7.11/1.47  ------ SAT Options
% 7.11/1.47  
% 7.11/1.47  --sat_mode                              false
% 7.11/1.47  --sat_fm_restart_options                ""
% 7.11/1.47  --sat_gr_def                            false
% 7.11/1.47  --sat_epr_types                         true
% 7.11/1.47  --sat_non_cyclic_types                  false
% 7.11/1.47  --sat_finite_models                     false
% 7.11/1.47  --sat_fm_lemmas                         false
% 7.11/1.47  --sat_fm_prep                           false
% 7.11/1.47  --sat_fm_uc_incr                        true
% 7.11/1.47  --sat_out_model                         small
% 7.11/1.47  --sat_out_clauses                       false
% 7.11/1.47  
% 7.11/1.47  ------ QBF Options
% 7.11/1.47  
% 7.11/1.47  --qbf_mode                              false
% 7.11/1.47  --qbf_elim_univ                         false
% 7.11/1.47  --qbf_dom_inst                          none
% 7.11/1.47  --qbf_dom_pre_inst                      false
% 7.11/1.47  --qbf_sk_in                             false
% 7.11/1.47  --qbf_pred_elim                         true
% 7.11/1.47  --qbf_split                             512
% 7.11/1.47  
% 7.11/1.47  ------ BMC1 Options
% 7.11/1.47  
% 7.11/1.47  --bmc1_incremental                      false
% 7.11/1.47  --bmc1_axioms                           reachable_all
% 7.11/1.47  --bmc1_min_bound                        0
% 7.11/1.47  --bmc1_max_bound                        -1
% 7.11/1.47  --bmc1_max_bound_default                -1
% 7.11/1.47  --bmc1_symbol_reachability              true
% 7.11/1.47  --bmc1_property_lemmas                  false
% 7.11/1.47  --bmc1_k_induction                      false
% 7.11/1.47  --bmc1_non_equiv_states                 false
% 7.11/1.47  --bmc1_deadlock                         false
% 7.11/1.47  --bmc1_ucm                              false
% 7.11/1.47  --bmc1_add_unsat_core                   none
% 7.11/1.47  --bmc1_unsat_core_children              false
% 7.11/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.47  --bmc1_out_stat                         full
% 7.11/1.47  --bmc1_ground_init                      false
% 7.11/1.47  --bmc1_pre_inst_next_state              false
% 7.11/1.47  --bmc1_pre_inst_state                   false
% 7.11/1.47  --bmc1_pre_inst_reach_state             false
% 7.11/1.47  --bmc1_out_unsat_core                   false
% 7.11/1.47  --bmc1_aig_witness_out                  false
% 7.11/1.47  --bmc1_verbose                          false
% 7.11/1.47  --bmc1_dump_clauses_tptp                false
% 7.11/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.47  --bmc1_dump_file                        -
% 7.11/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.47  --bmc1_ucm_extend_mode                  1
% 7.11/1.47  --bmc1_ucm_init_mode                    2
% 7.11/1.47  --bmc1_ucm_cone_mode                    none
% 7.11/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.47  --bmc1_ucm_relax_model                  4
% 7.11/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.47  --bmc1_ucm_layered_model                none
% 7.11/1.47  --bmc1_ucm_max_lemma_size               10
% 7.11/1.47  
% 7.11/1.47  ------ AIG Options
% 7.11/1.47  
% 7.11/1.47  --aig_mode                              false
% 7.11/1.47  
% 7.11/1.47  ------ Instantiation Options
% 7.11/1.47  
% 7.11/1.47  --instantiation_flag                    true
% 7.11/1.47  --inst_sos_flag                         true
% 7.11/1.47  --inst_sos_phase                        true
% 7.11/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.47  --inst_lit_sel_side                     none
% 7.11/1.47  --inst_solver_per_active                1400
% 7.11/1.47  --inst_solver_calls_frac                1.
% 7.11/1.47  --inst_passive_queue_type               priority_queues
% 7.11/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.47  --inst_passive_queues_freq              [25;2]
% 7.11/1.47  --inst_dismatching                      true
% 7.11/1.47  --inst_eager_unprocessed_to_passive     true
% 7.11/1.47  --inst_prop_sim_given                   true
% 7.11/1.47  --inst_prop_sim_new                     false
% 7.11/1.47  --inst_subs_new                         false
% 7.11/1.47  --inst_eq_res_simp                      false
% 7.11/1.47  --inst_subs_given                       false
% 7.11/1.47  --inst_orphan_elimination               true
% 7.11/1.47  --inst_learning_loop_flag               true
% 7.11/1.47  --inst_learning_start                   3000
% 7.11/1.47  --inst_learning_factor                  2
% 7.11/1.47  --inst_start_prop_sim_after_learn       3
% 7.11/1.47  --inst_sel_renew                        solver
% 7.11/1.47  --inst_lit_activity_flag                true
% 7.11/1.47  --inst_restr_to_given                   false
% 7.11/1.47  --inst_activity_threshold               500
% 7.11/1.47  --inst_out_proof                        true
% 7.11/1.47  
% 7.11/1.47  ------ Resolution Options
% 7.11/1.47  
% 7.11/1.47  --resolution_flag                       false
% 7.11/1.47  --res_lit_sel                           adaptive
% 7.11/1.47  --res_lit_sel_side                      none
% 7.11/1.47  --res_ordering                          kbo
% 7.11/1.47  --res_to_prop_solver                    active
% 7.11/1.47  --res_prop_simpl_new                    false
% 7.11/1.47  --res_prop_simpl_given                  true
% 7.11/1.47  --res_passive_queue_type                priority_queues
% 7.11/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.47  --res_passive_queues_freq               [15;5]
% 7.11/1.47  --res_forward_subs                      full
% 7.11/1.47  --res_backward_subs                     full
% 7.11/1.47  --res_forward_subs_resolution           true
% 7.11/1.47  --res_backward_subs_resolution          true
% 7.11/1.47  --res_orphan_elimination                true
% 7.11/1.47  --res_time_limit                        2.
% 7.11/1.47  --res_out_proof                         true
% 7.11/1.47  
% 7.11/1.47  ------ Superposition Options
% 7.11/1.47  
% 7.11/1.47  --superposition_flag                    true
% 7.11/1.47  --sup_passive_queue_type                priority_queues
% 7.11/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.47  --demod_completeness_check              fast
% 7.11/1.47  --demod_use_ground                      true
% 7.11/1.47  --sup_to_prop_solver                    passive
% 7.11/1.47  --sup_prop_simpl_new                    true
% 7.11/1.47  --sup_prop_simpl_given                  true
% 7.11/1.47  --sup_fun_splitting                     true
% 7.11/1.47  --sup_smt_interval                      50000
% 7.11/1.47  
% 7.11/1.47  ------ Superposition Simplification Setup
% 7.11/1.47  
% 7.11/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.11/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.11/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.11/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.11/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.11/1.47  --sup_immed_triv                        [TrivRules]
% 7.11/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.47  --sup_immed_bw_main                     []
% 7.11/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.11/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.47  --sup_input_bw                          []
% 7.11/1.47  
% 7.11/1.47  ------ Combination Options
% 7.11/1.47  
% 7.11/1.47  --comb_res_mult                         3
% 7.11/1.47  --comb_sup_mult                         2
% 7.11/1.47  --comb_inst_mult                        10
% 7.11/1.47  
% 7.11/1.47  ------ Debug Options
% 7.11/1.47  
% 7.11/1.47  --dbg_backtrace                         false
% 7.11/1.47  --dbg_dump_prop_clauses                 false
% 7.11/1.47  --dbg_dump_prop_clauses_file            -
% 7.11/1.47  --dbg_out_stat                          false
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  ------ Proving...
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  % SZS status Theorem for theBenchmark.p
% 7.11/1.47  
% 7.11/1.47   Resolution empty clause
% 7.11/1.47  
% 7.11/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.11/1.47  
% 7.11/1.47  fof(f15,conjecture,(
% 7.11/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f16,negated_conjecture,(
% 7.11/1.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.11/1.47    inference(negated_conjecture,[],[f15])).
% 7.11/1.47  
% 7.11/1.47  fof(f27,plain,(
% 7.11/1.47    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.11/1.47    inference(ennf_transformation,[],[f16])).
% 7.11/1.47  
% 7.11/1.47  fof(f28,plain,(
% 7.11/1.47    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.11/1.47    inference(flattening,[],[f27])).
% 7.11/1.47  
% 7.11/1.47  fof(f36,plain,(
% 7.11/1.47    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.11/1.47    introduced(choice_axiom,[])).
% 7.11/1.47  
% 7.11/1.47  fof(f37,plain,(
% 7.11/1.47    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.11/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f36])).
% 7.11/1.47  
% 7.11/1.47  fof(f66,plain,(
% 7.11/1.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.11/1.47    inference(cnf_transformation,[],[f37])).
% 7.11/1.47  
% 7.11/1.47  fof(f9,axiom,(
% 7.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f17,plain,(
% 7.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.11/1.47    inference(pure_predicate_removal,[],[f9])).
% 7.11/1.47  
% 7.11/1.47  fof(f20,plain,(
% 7.11/1.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.47    inference(ennf_transformation,[],[f17])).
% 7.11/1.47  
% 7.11/1.47  fof(f53,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f20])).
% 7.11/1.47  
% 7.11/1.47  fof(f6,axiom,(
% 7.11/1.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f19,plain,(
% 7.11/1.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.11/1.47    inference(ennf_transformation,[],[f6])).
% 7.11/1.47  
% 7.11/1.47  fof(f34,plain,(
% 7.11/1.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.11/1.47    inference(nnf_transformation,[],[f19])).
% 7.11/1.47  
% 7.11/1.47  fof(f48,plain,(
% 7.11/1.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.11/1.47    inference(cnf_transformation,[],[f34])).
% 7.11/1.47  
% 7.11/1.47  fof(f8,axiom,(
% 7.11/1.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f52,plain,(
% 7.11/1.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.11/1.47    inference(cnf_transformation,[],[f8])).
% 7.11/1.47  
% 7.11/1.47  fof(f3,axiom,(
% 7.11/1.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f31,plain,(
% 7.11/1.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.11/1.47    inference(nnf_transformation,[],[f3])).
% 7.11/1.47  
% 7.11/1.47  fof(f32,plain,(
% 7.11/1.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.11/1.47    inference(flattening,[],[f31])).
% 7.11/1.47  
% 7.11/1.47  fof(f44,plain,(
% 7.11/1.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.11/1.47    inference(cnf_transformation,[],[f32])).
% 7.11/1.47  
% 7.11/1.47  fof(f72,plain,(
% 7.11/1.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.11/1.47    inference(equality_resolution,[],[f44])).
% 7.11/1.47  
% 7.11/1.47  fof(f12,axiom,(
% 7.11/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f23,plain,(
% 7.11/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.11/1.47    inference(ennf_transformation,[],[f12])).
% 7.11/1.47  
% 7.11/1.47  fof(f24,plain,(
% 7.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.11/1.47    inference(flattening,[],[f23])).
% 7.11/1.47  
% 7.11/1.47  fof(f56,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.11/1.47    inference(cnf_transformation,[],[f24])).
% 7.11/1.47  
% 7.11/1.47  fof(f4,axiom,(
% 7.11/1.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f33,plain,(
% 7.11/1.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.11/1.47    inference(nnf_transformation,[],[f4])).
% 7.11/1.47  
% 7.11/1.47  fof(f45,plain,(
% 7.11/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f33])).
% 7.11/1.47  
% 7.11/1.47  fof(f1,axiom,(
% 7.11/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f29,plain,(
% 7.11/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.47    inference(nnf_transformation,[],[f1])).
% 7.11/1.47  
% 7.11/1.47  fof(f30,plain,(
% 7.11/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.47    inference(flattening,[],[f29])).
% 7.11/1.47  
% 7.11/1.47  fof(f38,plain,(
% 7.11/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.11/1.47    inference(cnf_transformation,[],[f30])).
% 7.11/1.47  
% 7.11/1.47  fof(f71,plain,(
% 7.11/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.11/1.47    inference(equality_resolution,[],[f38])).
% 7.11/1.47  
% 7.11/1.47  fof(f7,axiom,(
% 7.11/1.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f50,plain,(
% 7.11/1.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f7])).
% 7.11/1.47  
% 7.11/1.47  fof(f13,axiom,(
% 7.11/1.47    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f57,plain,(
% 7.11/1.47    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f13])).
% 7.11/1.47  
% 7.11/1.47  fof(f5,axiom,(
% 7.11/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f18,plain,(
% 7.11/1.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.11/1.47    inference(ennf_transformation,[],[f5])).
% 7.11/1.47  
% 7.11/1.47  fof(f47,plain,(
% 7.11/1.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.11/1.47    inference(cnf_transformation,[],[f18])).
% 7.11/1.47  
% 7.11/1.47  fof(f46,plain,(
% 7.11/1.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.11/1.47    inference(cnf_transformation,[],[f33])).
% 7.11/1.47  
% 7.11/1.47  fof(f51,plain,(
% 7.11/1.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.11/1.47    inference(cnf_transformation,[],[f8])).
% 7.11/1.47  
% 7.11/1.47  fof(f40,plain,(
% 7.11/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.11/1.47    inference(cnf_transformation,[],[f30])).
% 7.11/1.47  
% 7.11/1.47  fof(f43,plain,(
% 7.11/1.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.11/1.47    inference(cnf_transformation,[],[f32])).
% 7.11/1.47  
% 7.11/1.47  fof(f73,plain,(
% 7.11/1.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.11/1.47    inference(equality_resolution,[],[f43])).
% 7.11/1.47  
% 7.11/1.47  fof(f42,plain,(
% 7.11/1.47    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.11/1.47    inference(cnf_transformation,[],[f32])).
% 7.11/1.47  
% 7.11/1.47  fof(f2,axiom,(
% 7.11/1.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f41,plain,(
% 7.11/1.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.11/1.47    inference(cnf_transformation,[],[f2])).
% 7.11/1.47  
% 7.11/1.47  fof(f14,axiom,(
% 7.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f25,plain,(
% 7.11/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.47    inference(ennf_transformation,[],[f14])).
% 7.11/1.47  
% 7.11/1.47  fof(f26,plain,(
% 7.11/1.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.47    inference(flattening,[],[f25])).
% 7.11/1.47  
% 7.11/1.47  fof(f35,plain,(
% 7.11/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.47    inference(nnf_transformation,[],[f26])).
% 7.11/1.47  
% 7.11/1.47  fof(f62,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f35])).
% 7.11/1.47  
% 7.11/1.47  fof(f76,plain,(
% 7.11/1.47    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.11/1.47    inference(equality_resolution,[],[f62])).
% 7.11/1.47  
% 7.11/1.47  fof(f65,plain,(
% 7.11/1.47    v1_funct_2(sK3,sK0,sK1)),
% 7.11/1.47    inference(cnf_transformation,[],[f37])).
% 7.11/1.47  
% 7.11/1.47  fof(f68,plain,(
% 7.11/1.47    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.11/1.47    inference(cnf_transformation,[],[f37])).
% 7.11/1.47  
% 7.11/1.47  fof(f58,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f35])).
% 7.11/1.47  
% 7.11/1.47  fof(f10,axiom,(
% 7.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f21,plain,(
% 7.11/1.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.47    inference(ennf_transformation,[],[f10])).
% 7.11/1.47  
% 7.11/1.47  fof(f54,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f21])).
% 7.11/1.47  
% 7.11/1.47  fof(f60,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f35])).
% 7.11/1.47  
% 7.11/1.47  fof(f69,plain,(
% 7.11/1.47    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 7.11/1.47    inference(cnf_transformation,[],[f37])).
% 7.11/1.47  
% 7.11/1.47  fof(f64,plain,(
% 7.11/1.47    v1_funct_1(sK3)),
% 7.11/1.47    inference(cnf_transformation,[],[f37])).
% 7.11/1.47  
% 7.11/1.47  fof(f11,axiom,(
% 7.11/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.11/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.47  
% 7.11/1.47  fof(f22,plain,(
% 7.11/1.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.47    inference(ennf_transformation,[],[f11])).
% 7.11/1.47  
% 7.11/1.47  fof(f55,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f22])).
% 7.11/1.47  
% 7.11/1.47  fof(f67,plain,(
% 7.11/1.47    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 7.11/1.47    inference(cnf_transformation,[],[f37])).
% 7.11/1.47  
% 7.11/1.47  fof(f61,plain,(
% 7.11/1.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.47    inference(cnf_transformation,[],[f35])).
% 7.11/1.47  
% 7.11/1.47  fof(f77,plain,(
% 7.11/1.47    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.11/1.47    inference(equality_resolution,[],[f61])).
% 7.11/1.47  
% 7.11/1.47  cnf(c_29,negated_conjecture,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.11/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1210,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_15,plain,
% 7.11/1.47      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.11/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_11,plain,
% 7.11/1.47      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.11/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_357,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1)
% 7.11/1.47      | ~ v1_relat_1(X0) ),
% 7.11/1.47      inference(resolution,[status(thm)],[c_15,c_11]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1208,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1563,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1210,c_1208]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_13,plain,
% 7.11/1.47      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4,plain,
% 7.11/1.47      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_18,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.11/1.47      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.11/1.47      | ~ v1_relat_1(X0) ),
% 7.11/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1213,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.11/1.47      inference(cnf_transformation,[],[f45]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1217,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.11/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2709,plain,
% 7.11/1.47      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1213,c_1217]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5506,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4,c_2709]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1565,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4,c_1208]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f71]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1220,plain,
% 7.11/1.47      ( r1_tarski(X0,X0) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2707,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4,c_1213]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4494,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1220,c_2707]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8722,plain,
% 7.11/1.47      ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_5506,c_1565,c_4494]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8723,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_8722]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8726,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_13,c_8723]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_12,plain,
% 7.11/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.11/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1216,plain,
% 7.11/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.11/1.47      inference(cnf_transformation,[],[f57]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1212,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2340,plain,
% 7.11/1.47      ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1212,c_1217]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_9,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.11/1.47      inference(cnf_transformation,[],[f47]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_7,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.11/1.47      inference(cnf_transformation,[],[f46]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_213,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.11/1.47      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_214,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_213]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_268,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.11/1.47      inference(bin_hyper_res,[status(thm)],[c_9,c_214]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1209,plain,
% 7.11/1.47      ( r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | v1_relat_1(X1) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2638,plain,
% 7.11/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X0)) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_2340,c_1209]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3237,plain,
% 7.11/1.47      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1216,c_2638]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8804,plain,
% 7.11/1.47      ( r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,[status(thm)],[c_8726,c_3237]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8805,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k6_relat_1(X0),k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_8804]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_14,plain,
% 7.11/1.47      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1218,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3943,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1218,c_1565]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_0,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.11/1.47      inference(cnf_transformation,[],[f40]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1221,plain,
% 7.11/1.47      ( X0 = X1
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_9301,plain,
% 7.11/1.47      ( k1_relat_1(X0) = X1
% 7.11/1.47      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_3943,c_1221]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5,plain,
% 7.11/1.47      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2822,plain,
% 7.11/1.47      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1218,c_1208]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_6762,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_5,c_2822]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8554,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top
% 7.11/1.47      | v1_relat_1(k1_relat_1(X0)) = iProver_top
% 7.11/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_6762,c_1209]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_72,plain,
% 7.11/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_74,plain,
% 7.11/1.47      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_72]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_6,plain,
% 7.11/1.47      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 = X1
% 7.11/1.47      | k1_xboole_0 = X0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f42]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_88,plain,
% 7.11/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 = k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_6]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_89,plain,
% 7.11/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_5]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3,plain,
% 7.11/1.47      ( r1_tarski(k1_xboole_0,X0) ),
% 7.11/1.47      inference(cnf_transformation,[],[f41]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_90,plain,
% 7.11/1.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_92,plain,
% 7.11/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_90]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1389,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.11/1.47      | v1_relat_1(X0)
% 7.11/1.47      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_268]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1390,plain,
% 7.11/1.47      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) = iProver_top
% 7.11/1.47      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_1389]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1392,plain,
% 7.11/1.47      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.11/1.47      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.11/1.47      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1390]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_721,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.11/1.47      theory(equality) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1599,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1)
% 7.11/1.47      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 7.11/1.47      | X2 != X0
% 7.11/1.47      | k2_zfmisc_1(X3,X4) != X1 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_721]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1600,plain,
% 7.11/1.47      ( X0 != X1
% 7.11/1.47      | k2_zfmisc_1(X2,X3) != X4
% 7.11/1.47      | r1_tarski(X1,X4) != iProver_top
% 7.11/1.47      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_1599]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1602,plain,
% 7.11/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 != k1_xboole_0
% 7.11/1.47      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1600]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_15027,plain,
% 7.11/1.47      ( v1_relat_1(k1_relat_1(X0)) = iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_8554,c_74,c_88,c_89,c_92,c_1392,c_1602]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_15028,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top
% 7.11/1.47      | v1_relat_1(k1_relat_1(X0)) = iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_15027]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_15038,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top
% 7.11/1.47      | v1_relat_1(k1_relat_1(k6_relat_1(X0))) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_8805,c_15028]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_15044,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) = iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.11/1.47      inference(light_normalisation,[status(thm)],[c_15038,c_14]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_15118,plain,
% 7.11/1.47      ( v1_relat_1(X0) = iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_15044,c_3237]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_15119,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) = iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_15118]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19239,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.11/1.47      | k1_relat_1(X0) = X1 ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_9301,c_3237,c_15044]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19240,plain,
% 7.11/1.47      ( k1_relat_1(X0) = X1
% 7.11/1.47      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_19239]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19253,plain,
% 7.11/1.47      ( k1_relat_1(k6_relat_1(X0)) = X1
% 7.11/1.47      | r1_tarski(X1,X0) != iProver_top
% 7.11/1.47      | r1_tarski(k6_relat_1(X0),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_14,c_19240]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19257,plain,
% 7.11/1.47      ( X0 = X1
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | r1_tarski(k6_relat_1(X1),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_19253,c_14]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19383,plain,
% 7.11/1.47      ( X0 = X1
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_8805,c_19257]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19700,plain,
% 7.11/1.47      ( k1_relat_1(sK3) = sK0
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1563,c_19383]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1280,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1)
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0)
% 7.11/1.47      | sK0 != X0
% 7.11/1.47      | k1_xboole_0 != X1 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_721]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1281,plain,
% 7.11/1.47      ( sK0 != X0
% 7.11/1.47      | k1_xboole_0 != X1
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1283,plain,
% 7.11/1.47      ( sK0 != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 != k1_xboole_0
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1281]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_21,plain,
% 7.11/1.47      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.11/1.47      | k1_xboole_0 = X1
% 7.11/1.47      | k1_xboole_0 = X0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f76]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_30,negated_conjecture,
% 7.11/1.47      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.11/1.47      inference(cnf_transformation,[],[f65]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_407,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.11/1.47      | sK1 != k1_xboole_0
% 7.11/1.47      | sK0 != X1
% 7.11/1.47      | sK3 != X0
% 7.11/1.47      | k1_xboole_0 = X1
% 7.11/1.47      | k1_xboole_0 = X0 ),
% 7.11/1.47      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_408,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 7.11/1.47      | sK1 != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 = sK0
% 7.11/1.47      | k1_xboole_0 = sK3 ),
% 7.11/1.47      inference(unflattening,[status(thm)],[c_407]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1206,plain,
% 7.11/1.47      ( sK1 != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 = sK0
% 7.11/1.47      | k1_xboole_0 = sK3
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1223,plain,
% 7.11/1.47      ( sK1 != k1_xboole_0
% 7.11/1.47      | sK0 = k1_xboole_0
% 7.11/1.47      | sK3 = k1_xboole_0
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_1206,c_4]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_27,negated_conjecture,
% 7.11/1.47      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_720,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1257,plain,
% 7.11/1.47      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1312,plain,
% 7.11/1.47      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1257]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_719,plain,( X0 = X0 ),theory(equality) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1379,plain,
% 7.11/1.47      ( sK0 = sK0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_719]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1470,plain,
% 7.11/1.47      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1471,plain,
% 7.11/1.47      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1470]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1790,plain,
% 7.11/1.47      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_1223,c_27,c_88,c_89,c_1312,c_1379,c_1471]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2341,plain,
% 7.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1210,c_1217]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2349,plain,
% 7.11/1.47      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_2341,c_1209]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2452,plain,
% 7.11/1.47      ( v1_relat_1(sK3) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1216,c_2349]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_25,plain,
% 7.11/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | k1_relset_1(X1,X2,X0) = X1
% 7.11/1.47      | k1_xboole_0 = X2 ),
% 7.11/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_469,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | k1_relset_1(X1,X2,X0) = X1
% 7.11/1.47      | sK1 != X2
% 7.11/1.47      | sK0 != X1
% 7.11/1.47      | sK3 != X0
% 7.11/1.47      | k1_xboole_0 = X2 ),
% 7.11/1.47      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_470,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.11/1.47      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.11/1.47      | k1_xboole_0 = sK1 ),
% 7.11/1.47      inference(unflattening,[status(thm)],[c_469]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_472,plain,
% 7.11/1.47      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.11/1.47      inference(global_propositional_subsumption,[status(thm)],[c_470,c_29]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_16,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.11/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1215,plain,
% 7.11/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.11/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3651,plain,
% 7.11/1.47      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1210,c_1215]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3695,plain,
% 7.11/1.47      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_472,c_3651]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20066,plain,
% 7.11/1.47      ( k1_relat_1(sK3) = sK0 ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_19700,c_88,c_89,c_92,c_1283,c_1790,c_2452,c_3695]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2708,plain,
% 7.11/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_5,c_1213]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4602,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_14,c_2708]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4605,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.11/1.47      inference(light_normalisation,[status(thm)],[c_4602,c_13]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4613,plain,
% 7.11/1.47      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,[status(thm)],[c_4605,c_3237]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4614,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.47      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_4613]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4622,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1563,c_4614]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4941,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,[status(thm)],[c_4622,c_2452]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4942,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_4941]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4946,plain,
% 7.11/1.47      ( r1_tarski(k6_relat_1(k1_relat_1(sK3)),k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4942,c_1217]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1219,plain,
% 7.11/1.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3506,plain,
% 7.11/1.47      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1219,c_1221]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_6016,plain,
% 7.11/1.47      ( k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4946,c_3506]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8566,plain,
% 7.11/1.47      ( k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_6762,c_6016]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_9064,plain,
% 7.11/1.47      ( r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.11/1.47      | k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0 ),
% 7.11/1.47      inference(global_propositional_subsumption,[status(thm)],[c_8566,c_2452]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_9065,plain,
% 7.11/1.47      ( k6_relat_1(k1_relat_1(sK3)) = k1_xboole_0
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_9064]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20094,plain,
% 7.11/1.47      ( k6_relat_1(sK0) = k1_xboole_0
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_20066,c_9065]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_23,plain,
% 7.11/1.47      ( v1_funct_2(X0,X1,X2)
% 7.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | k1_relset_1(X1,X2,X0) != X1
% 7.11/1.47      | k1_xboole_0 = X2 ),
% 7.11/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_26,negated_conjecture,
% 7.11/1.47      ( ~ v1_funct_2(sK3,sK0,sK2)
% 7.11/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | ~ v1_funct_1(sK3) ),
% 7.11/1.47      inference(cnf_transformation,[],[f69]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_31,negated_conjecture,
% 7.11/1.47      ( v1_funct_1(sK3) ),
% 7.11/1.47      inference(cnf_transformation,[],[f64]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_155,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 7.11/1.47      inference(global_propositional_subsumption,[status(thm)],[c_26,c_31]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_156,negated_conjecture,
% 7.11/1.47      ( ~ v1_funct_2(sK3,sK0,sK2)
% 7.11/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_155]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_456,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | k1_relset_1(X1,X2,X0) != X1
% 7.11/1.47      | sK2 != X2
% 7.11/1.47      | sK0 != X1
% 7.11/1.47      | sK3 != X0
% 7.11/1.47      | k1_xboole_0 = X2 ),
% 7.11/1.47      inference(resolution_lifted,[status(thm)],[c_23,c_156]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_457,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | k1_relset_1(sK0,sK2,sK3) != sK0
% 7.11/1.47      | k1_xboole_0 = sK2 ),
% 7.11/1.47      inference(unflattening,[status(thm)],[c_456]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_480,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | sK1 != sK2
% 7.11/1.47      | sK0 != sK0
% 7.11/1.47      | sK3 != sK3 ),
% 7.11/1.47      inference(resolution_lifted,[status(thm)],[c_156,c_30]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_481,plain,
% 7.11/1.47      ( sK1 != sK2
% 7.11/1.47      | sK0 != sK0
% 7.11/1.47      | sK3 != sK3
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1263,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 7.11/1.47      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 7.11/1.47      | ~ v1_relat_1(sK3) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_18]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1264,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_1263]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1274,plain,
% 7.11/1.47      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1275,plain,
% 7.11/1.47      ( sK1 = sK2 | sK1 != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1274]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1382,plain,
% 7.11/1.47      ( sK3 = sK3 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_719]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1564,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),sK0) | ~ v1_relat_1(sK3) ),
% 7.11/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_1563]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1475,plain,
% 7.11/1.47      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1688,plain,
% 7.11/1.47      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1475]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2352,plain,
% 7.11/1.47      ( sK2 = sK2 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_719]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2453,plain,
% 7.11/1.47      ( v1_relat_1(sK3) ),
% 7.11/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_2452]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_17,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.11/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1214,plain,
% 7.11/1.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.11/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2830,plain,
% 7.11/1.47      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1210,c_1214]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_28,negated_conjecture,
% 7.11/1.47      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 7.11/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1211,plain,
% 7.11/1.47      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3018,plain,
% 7.11/1.47      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_2830,c_1211]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3020,plain,
% 7.11/1.47      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 7.11/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_3018]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1661,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1)
% 7.11/1.47      | r1_tarski(sK2,k1_xboole_0)
% 7.11/1.47      | sK2 != X0
% 7.11/1.47      | k1_xboole_0 != X1 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_721]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2446,plain,
% 7.11/1.47      ( ~ r1_tarski(sK2,X0)
% 7.11/1.47      | r1_tarski(sK2,k1_xboole_0)
% 7.11/1.47      | sK2 != sK2
% 7.11/1.47      | k1_xboole_0 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1661]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4425,plain,
% 7.11/1.47      ( ~ r1_tarski(sK2,sK2)
% 7.11/1.47      | r1_tarski(sK2,k1_xboole_0)
% 7.11/1.47      | sK2 != sK2
% 7.11/1.47      | k1_xboole_0 != sK2 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_2446]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1313,plain,
% 7.11/1.47      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1438,plain,
% 7.11/1.47      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1313]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_7045,plain,
% 7.11/1.47      ( k1_relat_1(sK3) != sK0 | sK0 = k1_relat_1(sK3) | sK0 != sK0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1438]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4945,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_3695,c_4942]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5062,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4945,c_1217]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8567,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_6762,c_5062]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4947,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(sK3))),X0) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(k1_relat_1(sK3))) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4942,c_1565]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4956,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(k1_relat_1(sK3))) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_4947,c_14]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2977,plain,
% 7.11/1.47      ( ~ r1_tarski(k6_relat_1(sK0),X0)
% 7.11/1.47      | ~ v1_relat_1(X0)
% 7.11/1.47      | v1_relat_1(k6_relat_1(sK0)) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_268]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2978,plain,
% 7.11/1.47      ( r1_tarski(k6_relat_1(sK0),X0) != iProver_top
% 7.11/1.47      | v1_relat_1(X0) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(sK0)) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2977]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2980,plain,
% 7.11/1.47      ( r1_tarski(k6_relat_1(sK0),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(sK0)) = iProver_top
% 7.11/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_2978]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5063,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | r1_tarski(k1_relat_1(k6_relat_1(sK0)),X0) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(sK0)) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4945,c_1565]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5072,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(sK0,X0) = iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(sK0)) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_5063,c_14]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5083,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 7.11/1.47      | v1_relat_1(k6_relat_1(sK0)) != iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_5072]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4604,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_3695,c_2708]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_34,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1254,plain,
% 7.11/1.47      ( ~ r1_tarski(sK0,k1_xboole_0)
% 7.11/1.47      | ~ r1_tarski(k1_xboole_0,sK0)
% 7.11/1.47      | sK0 = k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1255,plain,
% 7.11/1.47      ( sK0 = k1_xboole_0
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1623,plain,
% 7.11/1.47      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1624,plain,
% 7.11/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.11/1.47      | k1_xboole_0 != k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1623]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1754,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~ r1_tarski(sK3,X0) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_7]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1755,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
% 7.11/1.47      | r1_tarski(sK3,X0) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_1754]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1757,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1755]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1506,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_8]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1833,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1506]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1834,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2409,plain,
% 7.11/1.47      ( r1_tarski(k1_xboole_0,sK0) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2410,plain,
% 7.11/1.47      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1514,plain,
% 7.11/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_721]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1958,plain,
% 7.11/1.47      ( ~ r1_tarski(sK3,X0) | r1_tarski(sK3,X1) | X1 != X0 | sK3 != sK3 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1514]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2804,plain,
% 7.11/1.47      ( r1_tarski(sK3,X0)
% 7.11/1.47      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 7.11/1.47      | X0 != k2_zfmisc_1(sK0,sK1)
% 7.11/1.47      | sK3 != sK3 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1958]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2805,plain,
% 7.11/1.47      ( X0 != k2_zfmisc_1(sK0,sK1)
% 7.11/1.47      | sK3 != sK3
% 7.11/1.47      | r1_tarski(sK3,X0) = iProver_top
% 7.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_2804]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2807,plain,
% 7.11/1.47      ( sK3 != sK3
% 7.11/1.47      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
% 7.11/1.47      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_2805]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3746,plain,
% 7.11/1.47      ( X0 != X1 | X0 = k2_zfmisc_1(sK0,sK1) | k2_zfmisc_1(sK0,sK1) != X1 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1623]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3747,plain,
% 7.11/1.47      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 7.11/1.47      | k1_xboole_0 != k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_3746]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2282,plain,
% 7.11/1.47      ( k2_zfmisc_1(sK0,sK1) != X0
% 7.11/1.47      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 7.11/1.47      | k1_xboole_0 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3888,plain,
% 7.11/1.47      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
% 7.11/1.47      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 7.11/1.47      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_2282]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3890,plain,
% 7.11/1.47      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.11/1.47      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 7.11/1.47      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_3888]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_722,plain,
% 7.11/1.47      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.11/1.47      theory(equality) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4666,plain,
% 7.11/1.47      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1) | sK1 != X1 | sK0 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_722]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4667,plain,
% 7.11/1.47      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.11/1.47      | sK1 != k1_xboole_0
% 7.11/1.47      | sK0 != k1_xboole_0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_4666]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5086,plain,
% 7.11/1.47      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_4604,c_34,c_88,c_89,c_1255,c_1382,c_1624,c_1757,c_1834,
% 7.11/1.47                 c_2410,c_2452,c_2807,c_3747,c_3890,c_4667]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5087,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_5086]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5092,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1220,c_5087]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5381,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 7.11/1.47      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_5092,c_1565]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_7854,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_4956,c_74,c_88,c_89,c_92,c_1283,c_1392,c_1602,c_1790,
% 7.11/1.47                 c_2452,c_2980,c_5062,c_5083,c_5381]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_7855,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 7.11/1.47      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_7854]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8561,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_6762,c_7855]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8588,plain,
% 7.11/1.47      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_8561]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8929,plain,
% 7.11/1.47      ( r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
% 7.11/1.47      | sK1 = k1_xboole_0 ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_8567,c_2452,c_5062,c_8588]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8930,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | r1_tarski(k6_relat_1(sK0),k1_xboole_0) = iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_8929]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8935,plain,
% 7.11/1.47      ( k6_relat_1(sK0) = k1_xboole_0
% 7.11/1.47      | sK1 = k1_xboole_0
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_8930,c_3506]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8943,plain,
% 7.11/1.47      ( ~ r1_tarski(sK3,k1_xboole_0)
% 7.11/1.47      | k6_relat_1(sK0) = k1_xboole_0
% 7.11/1.47      | sK1 = k1_xboole_0 ),
% 7.11/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_8935]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_9564,plain,
% 7.11/1.47      ( r1_tarski(sK2,sK2) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_14851,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_16]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1729,plain,
% 7.11/1.47      ( X0 != X1 | X0 = sK0 | sK0 != X1 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_720]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_5275,plain,
% 7.11/1.47      ( k1_relset_1(sK0,sK2,sK3) != X0
% 7.11/1.47      | k1_relset_1(sK0,sK2,sK3) = sK0
% 7.11/1.47      | sK0 != X0 ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_1729]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_14967,plain,
% 7.11/1.47      ( k1_relset_1(sK0,sK2,sK3) != k1_relat_1(sK3)
% 7.11/1.47      | k1_relset_1(sK0,sK2,sK3) = sK0
% 7.11/1.47      | sK0 != k1_relat_1(sK3) ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_5275]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19699,plain,
% 7.11/1.47      ( k2_relat_1(sK3) = sK2 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_3018,c_19383]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19716,plain,
% 7.11/1.47      ( ~ r1_tarski(sK2,k1_xboole_0) | k2_relat_1(sK3) = sK2 ),
% 7.11/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_19699]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19825,plain,
% 7.11/1.47      ( k2_relat_1(sK3) = sK2 ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_19699,c_88,c_89,c_92,c_457,c_1263,c_1283,c_1379,c_1564,
% 7.11/1.47                 c_1790,c_2352,c_2452,c_2453,c_3020,c_3695,c_4425,c_7045,
% 7.11/1.47                 c_9564,c_14851,c_14967,c_19716,c_19700]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19842,plain,
% 7.11/1.47      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_19825,c_8723]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19844,plain,
% 7.11/1.47      ( ~ r1_tarski(sK2,k1_xboole_0)
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0)
% 7.11/1.47      | ~ v1_relat_1(sK3) ),
% 7.11/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_19842]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20331,plain,
% 7.11/1.47      ( k6_relat_1(sK0) = k1_xboole_0 ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_20094,c_88,c_89,c_92,c_457,c_481,c_1263,c_1264,c_1275,
% 7.11/1.47                 c_1283,c_1379,c_1382,c_1509,c_1563,c_1564,c_1688,c_1790,
% 7.11/1.47                 c_2352,c_2452,c_2453,c_3018,c_3020,c_3695,c_4426,c_7045,
% 7.11/1.47                 c_8935,c_9565,c_14851,c_14967,c_19700,c_19830]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20377,plain,
% 7.11/1.47      ( k2_relat_1(k1_xboole_0) = sK0 ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_20331,c_13]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2003,plain,
% 7.11/1.47      ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_4,c_1212]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2342,plain,
% 7.11/1.47      ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_2003,c_1217]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3866,plain,
% 7.11/1.47      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_2342,c_3506]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3879,plain,
% 7.11/1.47      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_3866,c_13]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20379,plain,
% 7.11/1.47      ( sK0 = k1_xboole_0 ),
% 7.11/1.47      inference(light_normalisation,[status(thm)],[c_20377,c_3879]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_22,plain,
% 7.11/1.47      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.11/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.11/1.47      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.11/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_427,plain,
% 7.11/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.11/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 7.11/1.47      | sK2 != X1
% 7.11/1.47      | sK0 != k1_xboole_0
% 7.11/1.47      | sK3 != X0 ),
% 7.11/1.47      inference(resolution_lifted,[status(thm)],[c_22,c_156]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_428,plain,
% 7.11/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.11/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 7.11/1.47      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.11/1.47      | sK0 != k1_xboole_0 ),
% 7.11/1.47      inference(unflattening,[status(thm)],[c_427]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1205,plain,
% 7.11/1.47      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.11/1.47      | sK0 != k1_xboole_0
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_1224,plain,
% 7.11/1.47      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.11/1.47      | sK0 != k1_xboole_0
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_1205,c_5]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20471,plain,
% 7.11/1.47      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.11/1.47      | k1_xboole_0 != k1_xboole_0
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_20379,c_1224]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20481,plain,
% 7.11/1.47      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.11/1.47      inference(equality_resolution_simp,[status(thm)],[c_20471]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20482,plain,
% 7.11/1.47      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_20481,c_5]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4426,plain,
% 7.11/1.47      ( sK2 != sK2
% 7.11/1.47      | k1_xboole_0 != sK2
% 7.11/1.47      | r1_tarski(sK2,sK2) != iProver_top
% 7.11/1.47      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_4425]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_9565,plain,
% 7.11/1.47      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.11/1.47      inference(predicate_to_equality,[status(thm)],[c_9564]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19382,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | sK0 = X0
% 7.11/1.47      | r1_tarski(X0,sK0) != iProver_top
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_8930,c_19257]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19386,plain,
% 7.11/1.47      ( sK1 = k1_xboole_0
% 7.11/1.47      | sK0 = k1_xboole_0
% 7.11/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.11/1.47      | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 7.11/1.47      inference(instantiation,[status(thm)],[c_19382]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4495,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1563,c_2707]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4936,plain,
% 7.11/1.47      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.11/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.11/1.47      inference(global_propositional_subsumption,[status(thm)],[c_4495,c_2452]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_4937,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(renaming,[status(thm)],[c_4936]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19830,plain,
% 7.11/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.11/1.47      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_19825,c_4937]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_21065,plain,
% 7.11/1.47      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
% 7.11/1.47      inference(global_propositional_subsumption,
% 7.11/1.47                [status(thm)],
% 7.11/1.47                [c_20482,c_88,c_89,c_92,c_457,c_1224,c_1263,c_1264,c_1283,
% 7.11/1.47                 c_1379,c_1509,c_1563,c_1564,c_1790,c_2352,c_2452,c_2453,
% 7.11/1.47                 c_3018,c_3020,c_3695,c_4426,c_7045,c_9565,c_14692,c_14851,
% 7.11/1.47                 c_14967,c_19700,c_19830]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20468,plain,
% 7.11/1.47      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_20379,c_2341]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20483,plain,
% 7.11/1.47      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_20468,c_5]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20820,plain,
% 7.11/1.47      ( sK3 = k1_xboole_0 ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_20483,c_3506]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_19833,plain,
% 7.11/1.47      ( k2_relset_1(sK0,sK1,sK3) = sK2 ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_19825,c_2830]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20407,plain,
% 7.11/1.47      ( k2_relset_1(k1_xboole_0,sK1,sK3) = sK2 ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_20379,c_19833]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20875,plain,
% 7.11/1.47      ( k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) = sK2 ),
% 7.11/1.47      inference(light_normalisation,[status(thm)],[c_20407,c_20407,c_20820]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_2827,plain,
% 7.11/1.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.11/1.47      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1218,c_1214]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_7282,plain,
% 7.11/1.47      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1219,c_2827]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_7288,plain,
% 7.11/1.47      ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.11/1.47      inference(light_normalisation,[status(thm)],[c_7282,c_3879]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_20876,plain,
% 7.11/1.47      ( sK2 = k1_xboole_0 ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_20875,c_7288]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_21067,plain,
% 7.11/1.47      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 7.11/1.47      inference(light_normalisation,[status(thm)],[c_21065,c_20820,c_20876]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3648,plain,
% 7.11/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.11/1.47      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1218,c_1215]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8539,plain,
% 7.11/1.47      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_1219,c_3648]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_3878,plain,
% 7.11/1.47      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.11/1.47      inference(superposition,[status(thm)],[c_3866,c_14]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_8546,plain,
% 7.11/1.47      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.11/1.47      inference(light_normalisation,[status(thm)],[c_8539,c_3878]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_21068,plain,
% 7.11/1.47      ( k1_xboole_0 != k1_xboole_0 ),
% 7.11/1.47      inference(demodulation,[status(thm)],[c_21067,c_8546]) ).
% 7.11/1.47  
% 7.11/1.47  cnf(c_21069,plain,
% 7.11/1.47      ( $false ),
% 7.11/1.47      inference(equality_resolution_simp,[status(thm)],[c_21068]) ).
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.11/1.47  
% 7.11/1.47  ------                               Statistics
% 7.11/1.47  
% 7.11/1.47  ------ General
% 7.11/1.47  
% 7.11/1.47  abstr_ref_over_cycles:                  0
% 7.11/1.47  abstr_ref_under_cycles:                 0
% 7.11/1.47  gc_basic_clause_elim:                   0
% 7.11/1.47  forced_gc_time:                         0
% 7.11/1.47  parsing_time:                           0.008
% 7.11/1.47  unif_index_cands_time:                  0.
% 7.11/1.47  unif_index_add_time:                    0.
% 7.11/1.47  orderings_time:                         0.
% 7.11/1.47  out_proof_time:                         0.017
% 7.11/1.47  total_time:                             0.581
% 7.11/1.47  num_of_symbols:                         49
% 7.11/1.47  num_of_terms:                           12276
% 7.11/1.47  
% 7.11/1.47  ------ Preprocessing
% 7.11/1.47  
% 7.11/1.47  num_of_splits:                          0
% 7.11/1.47  num_of_split_atoms:                     0
% 7.11/1.47  num_of_reused_defs:                     0
% 7.11/1.47  num_eq_ax_congr_red:                    7
% 7.11/1.47  num_of_sem_filtered_clauses:            2
% 7.11/1.47  num_of_subtypes:                        0
% 7.11/1.47  monotx_restored_types:                  0
% 7.11/1.47  sat_num_of_epr_types:                   0
% 7.11/1.47  sat_num_of_non_cyclic_types:            0
% 7.11/1.47  sat_guarded_non_collapsed_types:        0
% 7.11/1.47  num_pure_diseq_elim:                    0
% 7.11/1.47  simp_replaced_by:                       0
% 7.11/1.47  res_preprocessed:                       135
% 7.11/1.47  prep_upred:                             0
% 7.11/1.47  prep_unflattend:                        33
% 7.11/1.47  smt_new_axioms:                         0
% 7.11/1.47  pred_elim_cands:                        3
% 7.11/1.47  pred_elim:                              2
% 7.11/1.47  pred_elim_cl:                           3
% 7.11/1.47  pred_elim_cycles:                       4
% 7.11/1.47  merged_defs:                            8
% 7.11/1.47  merged_defs_ncl:                        0
% 7.11/1.47  bin_hyper_res:                          9
% 7.11/1.47  prep_cycles:                            4
% 7.11/1.47  pred_elim_time:                         0.004
% 7.11/1.47  splitting_time:                         0.
% 7.11/1.47  sem_filter_time:                        0.
% 7.11/1.47  monotx_time:                            0.
% 7.11/1.47  subtype_inf_time:                       0.
% 7.11/1.47  
% 7.11/1.47  ------ Problem properties
% 7.11/1.47  
% 7.11/1.47  clauses:                                27
% 7.11/1.47  conjectures:                            3
% 7.11/1.47  epr:                                    5
% 7.11/1.47  horn:                                   24
% 7.11/1.47  ground:                                 10
% 7.11/1.47  unary:                                  10
% 7.11/1.47  binary:                                 7
% 7.11/1.47  lits:                                   59
% 7.11/1.47  lits_eq:                                27
% 7.11/1.47  fd_pure:                                0
% 7.11/1.47  fd_pseudo:                              0
% 7.11/1.47  fd_cond:                                1
% 7.11/1.47  fd_pseudo_cond:                         1
% 7.11/1.47  ac_symbols:                             0
% 7.11/1.47  
% 7.11/1.47  ------ Propositional Solver
% 7.11/1.47  
% 7.11/1.47  prop_solver_calls:                      32
% 7.11/1.47  prop_fast_solver_calls:                 1633
% 7.11/1.47  smt_solver_calls:                       0
% 7.11/1.47  smt_fast_solver_calls:                  0
% 7.11/1.47  prop_num_of_clauses:                    8515
% 7.11/1.47  prop_preprocess_simplified:             16713
% 7.11/1.47  prop_fo_subsumed:                       84
% 7.11/1.47  prop_solver_time:                       0.
% 7.11/1.47  smt_solver_time:                        0.
% 7.11/1.47  smt_fast_solver_time:                   0.
% 7.11/1.47  prop_fast_solver_time:                  0.
% 7.11/1.47  prop_unsat_core_time:                   0.
% 7.11/1.47  
% 7.11/1.47  ------ QBF
% 7.11/1.47  
% 7.11/1.47  qbf_q_res:                              0
% 7.11/1.47  qbf_num_tautologies:                    0
% 7.11/1.47  qbf_prep_cycles:                        0
% 7.11/1.47  
% 7.11/1.47  ------ BMC1
% 7.11/1.47  
% 7.11/1.47  bmc1_current_bound:                     -1
% 7.11/1.47  bmc1_last_solved_bound:                 -1
% 7.11/1.47  bmc1_unsat_core_size:                   -1
% 7.11/1.47  bmc1_unsat_core_parents_size:           -1
% 7.11/1.47  bmc1_merge_next_fun:                    0
% 7.11/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.11/1.47  
% 7.11/1.47  ------ Instantiation
% 7.11/1.47  
% 7.11/1.47  inst_num_of_clauses:                    2734
% 7.11/1.47  inst_num_in_passive:                    517
% 7.11/1.47  inst_num_in_active:                     1242
% 7.11/1.47  inst_num_in_unprocessed:                975
% 7.11/1.47  inst_num_of_loops:                      1480
% 7.11/1.47  inst_num_of_learning_restarts:          0
% 7.11/1.47  inst_num_moves_active_passive:          234
% 7.11/1.47  inst_lit_activity:                      0
% 7.11/1.47  inst_lit_activity_moves:                0
% 7.11/1.47  inst_num_tautologies:                   0
% 7.11/1.47  inst_num_prop_implied:                  0
% 7.11/1.47  inst_num_existing_simplified:           0
% 7.11/1.47  inst_num_eq_res_simplified:             0
% 7.11/1.47  inst_num_child_elim:                    0
% 7.11/1.47  inst_num_of_dismatching_blockings:      1332
% 7.11/1.47  inst_num_of_non_proper_insts:           3896
% 7.11/1.47  inst_num_of_duplicates:                 0
% 7.11/1.47  inst_inst_num_from_inst_to_res:         0
% 7.11/1.47  inst_dismatching_checking_time:         0.
% 7.11/1.47  
% 7.11/1.47  ------ Resolution
% 7.11/1.47  
% 7.11/1.47  res_num_of_clauses:                     0
% 7.11/1.47  res_num_in_passive:                     0
% 7.11/1.47  res_num_in_active:                      0
% 7.11/1.47  res_num_of_loops:                       139
% 7.11/1.47  res_forward_subset_subsumed:            273
% 7.11/1.47  res_backward_subset_subsumed:           0
% 7.11/1.47  res_forward_subsumed:                   0
% 7.11/1.47  res_backward_subsumed:                  0
% 7.11/1.47  res_forward_subsumption_resolution:     0
% 7.11/1.47  res_backward_subsumption_resolution:    0
% 7.11/1.47  res_clause_to_clause_subsumption:       3396
% 7.11/1.47  res_orphan_elimination:                 0
% 7.11/1.47  res_tautology_del:                      260
% 7.11/1.47  res_num_eq_res_simplified:              1
% 7.11/1.47  res_num_sel_changes:                    0
% 7.11/1.47  res_moves_from_active_to_pass:          0
% 7.11/1.47  
% 7.11/1.47  ------ Superposition
% 7.11/1.47  
% 7.11/1.47  sup_time_total:                         0.
% 7.11/1.47  sup_time_generating:                    0.
% 7.11/1.47  sup_time_sim_full:                      0.
% 7.11/1.47  sup_time_sim_immed:                     0.
% 7.11/1.47  
% 7.11/1.47  sup_num_of_clauses:                     222
% 7.11/1.47  sup_num_in_active:                      85
% 7.11/1.47  sup_num_in_passive:                     137
% 7.11/1.47  sup_num_of_loops:                       295
% 7.11/1.47  sup_fw_superposition:                   514
% 7.11/1.47  sup_bw_superposition:                   321
% 7.11/1.47  sup_immediate_simplified:               356
% 7.11/1.47  sup_given_eliminated:                   6
% 7.11/1.47  comparisons_done:                       0
% 7.11/1.47  comparisons_avoided:                    204
% 7.11/1.47  
% 7.11/1.47  ------ Simplifications
% 7.11/1.47  
% 7.11/1.47  
% 7.11/1.47  sim_fw_subset_subsumed:                 64
% 7.11/1.47  sim_bw_subset_subsumed:                 37
% 7.11/1.47  sim_fw_subsumed:                        82
% 7.11/1.47  sim_bw_subsumed:                        74
% 7.11/1.47  sim_fw_subsumption_res:                 0
% 7.11/1.47  sim_bw_subsumption_res:                 0
% 7.11/1.47  sim_tautology_del:                      25
% 7.11/1.47  sim_eq_tautology_del:                   133
% 7.11/1.47  sim_eq_res_simp:                        2
% 7.11/1.47  sim_fw_demodulated:                     152
% 7.11/1.47  sim_bw_demodulated:                     169
% 7.11/1.47  sim_light_normalised:                   166
% 7.11/1.47  sim_joinable_taut:                      0
% 7.11/1.47  sim_joinable_simp:                      0
% 7.11/1.47  sim_ac_normalised:                      0
% 7.11/1.47  sim_smt_subsumption:                    0
% 7.11/1.47  
%------------------------------------------------------------------------------
