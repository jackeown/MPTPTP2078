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
% DateTime   : Thu Dec  3 12:04:00 EST 2020

% Result     : Theorem 31.53s
% Output     : CNFRefutation 31.53s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4926)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f53,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f53])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f38])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1539,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1542,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2801,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1542])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1541,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2225,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1541])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2531,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2225,c_36])).

cnf(c_2804,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2801,c_2531])).

cnf(c_3101,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2804,c_36])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1547,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2374,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1547])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1553,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4295,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2374,c_1553])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1557,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2307,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1557])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_250,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_251])).

cnf(c_1537,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_2528,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_1537])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2571,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2572,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2571])).

cnf(c_4501,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4295,c_2528,c_2572])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1555,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1544,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1544])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1545,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4151,c_1545])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1546,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6367,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4655,c_1546])).

cnf(c_12791,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | v4_relat_1(X1,X0) != iProver_top
    | r1_tarski(X1,sK3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_6367])).

cnf(c_87403,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
    | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4501,c_12791])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1543,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3319,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2531,c_1543])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3596,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3319,c_36,c_38])).

cnf(c_3603,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3596,c_1557])).

cnf(c_4107,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3603,c_1537])).

cnf(c_15,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5315,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5316,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5315])).

cnf(c_87634,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_87403,c_2528,c_2572,c_4107,c_5316])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_512,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1532,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_2537,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2531,c_1532])).

cnf(c_87637,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87634,c_2537])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_860,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1606,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1614,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_859,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1627,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1651,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1551,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1973,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1551])).

cnf(c_1777,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2003,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_2004,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_1549,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1559,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2164,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_1559])).

cnf(c_2219,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2164,c_1973])).

cnf(c_2222,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_1549])).

cnf(c_2390,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_2391,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_861,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2770,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_2771,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_2773,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1540,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_528,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_530,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_33])).

cnf(c_2911,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1539,c_1546])).

cnf(c_3049,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_530,c_2911])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1548,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4284,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_1548])).

cnf(c_7592,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4284,c_2528,c_2572])).

cnf(c_7593,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7592])).

cnf(c_7600,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1540,c_7593])).

cnf(c_7963,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7600,c_1555])).

cnf(c_8061,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4501,c_7963])).

cnf(c_50413,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5315])).

cnf(c_50414,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50413])).

cnf(c_6364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4655,c_1544])).

cnf(c_35906,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_6364])).

cnf(c_95,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1560,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4173,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_1560])).

cnf(c_4574,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_1537])).

cnf(c_4653,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1545])).

cnf(c_4805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4653,c_1544])).

cnf(c_6392,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4805,c_1547])).

cnf(c_10202,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_6392])).

cnf(c_2375,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1547])).

cnf(c_2640,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2641,plain,
    ( v4_relat_1(sK3,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2640])).

cnf(c_3097,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1769,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_2030,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_5830,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_5831,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK0
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5830])).

cnf(c_6387,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4805])).

cnf(c_10604,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10202,c_31,c_108,c_109,c_2374,c_2375,c_2391,c_2528,c_2572,c_2641,c_3097,c_5831,c_6387])).

cnf(c_36124,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35906,c_95,c_2572,c_4574,c_4655,c_10604])).

cnf(c_36125,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_36124])).

cnf(c_36133,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_36125,c_1544])).

cnf(c_37601,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_36133])).

cnf(c_37802,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(X0,sK1)) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_37601,c_1557])).

cnf(c_1558,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1544])).

cnf(c_4155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4154,c_3])).

cnf(c_4714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_4155])).

cnf(c_37837,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_37802,c_4714])).

cnf(c_97,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_107,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_538,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_1608,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1609,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_1605,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1612,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_1618,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1621,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1622,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1621])).

cnf(c_1687,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK2)
    | r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1642,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X1)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_1710,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_1709,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X0)
    | k1_xboole_0 != X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1708])).

cnf(c_1711,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_1778,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1777])).

cnf(c_1780,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_863,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1897,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1898,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_1975,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1973])).

cnf(c_2022,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1792,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_2039,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_2040,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_2099,plain,
    ( v4_relat_1(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2101,plain,
    ( v4_relat_1(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_2120,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2223,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2222])).

cnf(c_2367,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2368,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2367])).

cnf(c_2382,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2375])).

cnf(c_2407,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2529,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2528])).

cnf(c_2611,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2613,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_2619,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2620,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2619])).

cnf(c_3013,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3013])).

cnf(c_3016,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3014])).

cnf(c_3493,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(sK3,X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_1555])).

cnf(c_3499,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3493])).

cnf(c_2203,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),X2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3727,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_3728,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3727])).

cnf(c_3730,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3728])).

cnf(c_4389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k1_relat_1(X0),sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4391,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),sK2) ),
    inference(instantiation,[status(thm)],[c_4389])).

cnf(c_4624,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4625,plain,
    ( v4_relat_1(sK3,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4624])).

cnf(c_4627,plain,
    ( v4_relat_1(sK3,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4625])).

cnf(c_3496,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v4_relat_1(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1559])).

cnf(c_8369,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4501,c_3496])).

cnf(c_4110,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4107])).

cnf(c_8447,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8369,c_2572,c_4110])).

cnf(c_4654,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3596,c_1545])).

cnf(c_10087,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4654])).

cnf(c_10279,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8447,c_10087])).

cnf(c_5318,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5316])).

cnf(c_6361,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4655])).

cnf(c_8449,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8447,c_6361])).

cnf(c_11127,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10279,c_1973,c_2222,c_2528,c_2572,c_5318,c_8449])).

cnf(c_11131,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11127,c_1557])).

cnf(c_11273,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11131,c_1559])).

cnf(c_11820,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11273,c_4654])).

cnf(c_11839,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11820,c_11273])).

cnf(c_2373,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1547])).

cnf(c_3251,plain,
    ( v4_relat_1(k7_relat_1(k2_zfmisc_1(X0,X1),X2),X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_2373])).

cnf(c_85,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8279,plain,
    ( v4_relat_1(k7_relat_1(k2_zfmisc_1(X0,X1),X2),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3251,c_85])).

cnf(c_8368,plain,
    ( k1_relat_1(k7_relat_1(k2_zfmisc_1(k1_xboole_0,X0),X1)) = k1_xboole_0
    | v1_relat_1(k7_relat_1(k2_zfmisc_1(k1_xboole_0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_3496])).

cnf(c_8371,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(k7_relat_1(k1_xboole_0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8368,c_3])).

cnf(c_8372,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8371,c_2219])).

cnf(c_3508,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3496])).

cnf(c_8409,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8372,c_107,c_1973,c_2222,c_2382,c_3508])).

cnf(c_11840,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11839,c_8409])).

cnf(c_11847,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11840])).

cnf(c_11849,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11847])).

cnf(c_3125,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_12115,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_3125])).

cnf(c_12116,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12115])).

cnf(c_17292,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_4714])).

cnf(c_17449,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17292,c_1557])).

cnf(c_2241,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k7_relat_1(X2,X3),X2)
    | X1 != X2
    | X0 != k7_relat_1(X2,X3) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_8119,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(X1,X2),X1)
    | X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_21751,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | X0 != sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_8119])).

cnf(c_21753,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_21751])).

cnf(c_37603,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_36133])).

cnf(c_2949,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5718,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ r1_tarski(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_2949])).

cnf(c_5719,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5718])).

cnf(c_38111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37603,c_2374,c_2528,c_2572,c_2641,c_4653,c_5719])).

cnf(c_38118,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38111,c_1557])).

cnf(c_38484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38118,c_4714])).

cnf(c_8116,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_41643,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8116])).

cnf(c_41653,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) = iProver_top
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41643])).

cnf(c_41655,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3) != iProver_top
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41653])).

cnf(c_16579,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_48039,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_16579])).

cnf(c_49493,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_49896,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_50814,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
    | X2 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_51205,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),X1)
    | X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_50814])).

cnf(c_51823,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | X0 != sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_51205])).

cnf(c_52718,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_51823])).

cnf(c_52719,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | sK3 != sK3
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3) = iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52718])).

cnf(c_53304,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_53307,plain,
    ( k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53304])).

cnf(c_53383,plain,
    ( r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37837,c_35,c_33,c_31,c_97,c_106,c_107,c_108,c_109,c_538,c_1609,c_1612,c_1614,c_1618,c_1622,c_1627,c_1651,c_1687,c_1710,c_1711,c_1780,c_1898,c_1973,c_1975,c_2022,c_2040,c_2101,c_2120,c_2222,c_2223,c_2368,c_2382,c_2391,c_2407,c_2528,c_2529,c_2571,c_2572,c_2613,c_2620,c_2773,c_3016,c_3499,c_3730,c_4391,c_4627,c_11849,c_12116,c_17449,c_21753,c_38484,c_41655,c_48039,c_49493,c_49896,c_50413,c_50414,c_52719,c_53307])).

cnf(c_2282,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2283,plain,
    ( k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_2285,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2283])).

cnf(c_2090,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(k7_relat_1(X1,X2),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3784,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK3,X1))
    | r1_tarski(X0,sK3)
    | ~ r1_tarski(k7_relat_1(sK3,X1),sK3) ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_3785,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3784])).

cnf(c_3787,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3785])).

cnf(c_4803,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4653,c_1557])).

cnf(c_17304,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_4714])).

cnf(c_2238,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X2),X3)
    | X1 != X3
    | X0 != k1_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_20289,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,X1))
    | ~ r1_tarski(k1_relat_1(X2),X3)
    | X0 != k1_relat_1(X2)
    | k7_relat_1(sK3,X1) != X3 ),
    inference(instantiation,[status(thm)],[c_2238])).

cnf(c_20315,plain,
    ( X0 != k1_relat_1(X1)
    | k7_relat_1(sK3,X2) != X3
    | r1_tarski(X0,k7_relat_1(sK3,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20289])).

cnf(c_20317,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_20315])).

cnf(c_2725,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK3)
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_41545,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_2725])).

cnf(c_41554,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41545])).

cnf(c_41556,plain,
    ( r1_tarski(sK0,sK3) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41554])).

cnf(c_53389,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_53383,c_31,c_97,c_107,c_108,c_109,c_1614,c_1627,c_1711,c_1780,c_1898,c_1973,c_2120,c_2222,c_2285,c_2374,c_2382,c_2391,c_2528,c_2572,c_2641,c_2773,c_3016,c_3499,c_3730,c_3787,c_4627,c_5318,c_5719,c_11273,c_17304,c_20317,c_41556])).

cnf(c_53390,plain,
    ( r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_53389])).

cnf(c_53395,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_53390])).

cnf(c_52370,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_54745,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_52370])).

cnf(c_54746,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54745])).

cnf(c_52473,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_55189,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_52473])).

cnf(c_60450,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_55189])).

cnf(c_60451,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK2 != sK2
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60450])).

cnf(c_51813,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),X0)
    | r1_tarski(k7_relat_1(sK3,sK2),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_52923,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),X0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_51813])).

cnf(c_60660,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1))
    | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_52923])).

cnf(c_60661,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60660])).

cnf(c_51524,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X0))
    | ~ r1_tarski(k7_relat_1(sK3,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_68114,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_51524])).

cnf(c_68118,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68114])).

cnf(c_51325,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_84320,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_51325])).

cnf(c_84321,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84320])).

cnf(c_87764,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_87637,c_35,c_33,c_38,c_31,c_97,c_106,c_107,c_108,c_109,c_538,c_1609,c_1612,c_1614,c_1618,c_1622,c_1627,c_1651,c_1687,c_1710,c_1711,c_1898,c_1973,c_1975,c_2004,c_2022,c_2040,c_2101,c_2120,c_2222,c_2223,c_2368,c_2374,c_2382,c_2391,c_2407,c_2528,c_2529,c_2571,c_2572,c_2613,c_2620,c_2641,c_2773,c_3016,c_3097,c_3499,c_3730,c_4391,c_4627,c_4926,c_5831,c_7600,c_8061,c_11849,c_12116,c_17449,c_21753,c_41655,c_48039,c_49493,c_49896,c_50413,c_50414,c_52719,c_53307,c_54746,c_60451,c_60661,c_68118,c_84321])).

cnf(c_87768,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3101,c_87764])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 31.53/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.53/4.50  
% 31.53/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.53/4.50  
% 31.53/4.50  ------  iProver source info
% 31.53/4.50  
% 31.53/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.53/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.53/4.50  git: non_committed_changes: false
% 31.53/4.50  git: last_make_outside_of_git: false
% 31.53/4.50  
% 31.53/4.50  ------ 
% 31.53/4.50  
% 31.53/4.50  ------ Input Options
% 31.53/4.50  
% 31.53/4.50  --out_options                           all
% 31.53/4.50  --tptp_safe_out                         true
% 31.53/4.50  --problem_path                          ""
% 31.53/4.50  --include_path                          ""
% 31.53/4.50  --clausifier                            res/vclausify_rel
% 31.53/4.50  --clausifier_options                    ""
% 31.53/4.50  --stdin                                 false
% 31.53/4.50  --stats_out                             all
% 31.53/4.50  
% 31.53/4.50  ------ General Options
% 31.53/4.50  
% 31.53/4.50  --fof                                   false
% 31.53/4.50  --time_out_real                         305.
% 31.53/4.50  --time_out_virtual                      -1.
% 31.53/4.50  --symbol_type_check                     false
% 31.53/4.50  --clausify_out                          false
% 31.53/4.50  --sig_cnt_out                           false
% 31.53/4.50  --trig_cnt_out                          false
% 31.53/4.50  --trig_cnt_out_tolerance                1.
% 31.53/4.50  --trig_cnt_out_sk_spl                   false
% 31.53/4.50  --abstr_cl_out                          false
% 31.53/4.50  
% 31.53/4.50  ------ Global Options
% 31.53/4.50  
% 31.53/4.50  --schedule                              default
% 31.53/4.50  --add_important_lit                     false
% 31.53/4.50  --prop_solver_per_cl                    1000
% 31.53/4.50  --min_unsat_core                        false
% 31.53/4.50  --soft_assumptions                      false
% 31.53/4.50  --soft_lemma_size                       3
% 31.53/4.50  --prop_impl_unit_size                   0
% 31.53/4.50  --prop_impl_unit                        []
% 31.53/4.50  --share_sel_clauses                     true
% 31.53/4.50  --reset_solvers                         false
% 31.53/4.50  --bc_imp_inh                            [conj_cone]
% 31.53/4.50  --conj_cone_tolerance                   3.
% 31.53/4.50  --extra_neg_conj                        none
% 31.53/4.50  --large_theory_mode                     true
% 31.53/4.50  --prolific_symb_bound                   200
% 31.53/4.50  --lt_threshold                          2000
% 31.53/4.50  --clause_weak_htbl                      true
% 31.53/4.50  --gc_record_bc_elim                     false
% 31.53/4.50  
% 31.53/4.50  ------ Preprocessing Options
% 31.53/4.50  
% 31.53/4.50  --preprocessing_flag                    true
% 31.53/4.50  --time_out_prep_mult                    0.1
% 31.53/4.50  --splitting_mode                        input
% 31.53/4.50  --splitting_grd                         true
% 31.53/4.50  --splitting_cvd                         false
% 31.53/4.50  --splitting_cvd_svl                     false
% 31.53/4.50  --splitting_nvd                         32
% 31.53/4.50  --sub_typing                            true
% 31.53/4.50  --prep_gs_sim                           true
% 31.53/4.50  --prep_unflatten                        true
% 31.53/4.50  --prep_res_sim                          true
% 31.53/4.50  --prep_upred                            true
% 31.53/4.50  --prep_sem_filter                       exhaustive
% 31.53/4.50  --prep_sem_filter_out                   false
% 31.53/4.50  --pred_elim                             true
% 31.53/4.50  --res_sim_input                         true
% 31.53/4.50  --eq_ax_congr_red                       true
% 31.53/4.50  --pure_diseq_elim                       true
% 31.53/4.50  --brand_transform                       false
% 31.53/4.50  --non_eq_to_eq                          false
% 31.53/4.50  --prep_def_merge                        true
% 31.53/4.50  --prep_def_merge_prop_impl              false
% 31.53/4.50  --prep_def_merge_mbd                    true
% 31.53/4.50  --prep_def_merge_tr_red                 false
% 31.53/4.50  --prep_def_merge_tr_cl                  false
% 31.53/4.50  --smt_preprocessing                     true
% 31.53/4.50  --smt_ac_axioms                         fast
% 31.53/4.50  --preprocessed_out                      false
% 31.53/4.50  --preprocessed_stats                    false
% 31.53/4.50  
% 31.53/4.50  ------ Abstraction refinement Options
% 31.53/4.50  
% 31.53/4.50  --abstr_ref                             []
% 31.53/4.50  --abstr_ref_prep                        false
% 31.53/4.50  --abstr_ref_until_sat                   false
% 31.53/4.50  --abstr_ref_sig_restrict                funpre
% 31.53/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.53/4.50  --abstr_ref_under                       []
% 31.53/4.50  
% 31.53/4.50  ------ SAT Options
% 31.53/4.50  
% 31.53/4.50  --sat_mode                              false
% 31.53/4.50  --sat_fm_restart_options                ""
% 31.53/4.50  --sat_gr_def                            false
% 31.53/4.50  --sat_epr_types                         true
% 31.53/4.50  --sat_non_cyclic_types                  false
% 31.53/4.50  --sat_finite_models                     false
% 31.53/4.50  --sat_fm_lemmas                         false
% 31.53/4.50  --sat_fm_prep                           false
% 31.53/4.50  --sat_fm_uc_incr                        true
% 31.53/4.50  --sat_out_model                         small
% 31.53/4.50  --sat_out_clauses                       false
% 31.53/4.50  
% 31.53/4.50  ------ QBF Options
% 31.53/4.50  
% 31.53/4.50  --qbf_mode                              false
% 31.53/4.50  --qbf_elim_univ                         false
% 31.53/4.50  --qbf_dom_inst                          none
% 31.53/4.50  --qbf_dom_pre_inst                      false
% 31.53/4.50  --qbf_sk_in                             false
% 31.53/4.50  --qbf_pred_elim                         true
% 31.53/4.50  --qbf_split                             512
% 31.53/4.50  
% 31.53/4.50  ------ BMC1 Options
% 31.53/4.50  
% 31.53/4.50  --bmc1_incremental                      false
% 31.53/4.50  --bmc1_axioms                           reachable_all
% 31.53/4.50  --bmc1_min_bound                        0
% 31.53/4.50  --bmc1_max_bound                        -1
% 31.53/4.50  --bmc1_max_bound_default                -1
% 31.53/4.50  --bmc1_symbol_reachability              true
% 31.53/4.50  --bmc1_property_lemmas                  false
% 31.53/4.50  --bmc1_k_induction                      false
% 31.53/4.50  --bmc1_non_equiv_states                 false
% 31.53/4.50  --bmc1_deadlock                         false
% 31.53/4.50  --bmc1_ucm                              false
% 31.53/4.50  --bmc1_add_unsat_core                   none
% 31.53/4.50  --bmc1_unsat_core_children              false
% 31.53/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.53/4.50  --bmc1_out_stat                         full
% 31.53/4.50  --bmc1_ground_init                      false
% 31.53/4.50  --bmc1_pre_inst_next_state              false
% 31.53/4.50  --bmc1_pre_inst_state                   false
% 31.53/4.50  --bmc1_pre_inst_reach_state             false
% 31.53/4.50  --bmc1_out_unsat_core                   false
% 31.53/4.50  --bmc1_aig_witness_out                  false
% 31.53/4.50  --bmc1_verbose                          false
% 31.53/4.50  --bmc1_dump_clauses_tptp                false
% 31.53/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.53/4.50  --bmc1_dump_file                        -
% 31.53/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.53/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.53/4.50  --bmc1_ucm_extend_mode                  1
% 31.53/4.50  --bmc1_ucm_init_mode                    2
% 31.53/4.50  --bmc1_ucm_cone_mode                    none
% 31.53/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.53/4.50  --bmc1_ucm_relax_model                  4
% 31.53/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.53/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.53/4.50  --bmc1_ucm_layered_model                none
% 31.53/4.50  --bmc1_ucm_max_lemma_size               10
% 31.53/4.50  
% 31.53/4.50  ------ AIG Options
% 31.53/4.50  
% 31.53/4.50  --aig_mode                              false
% 31.53/4.50  
% 31.53/4.50  ------ Instantiation Options
% 31.53/4.50  
% 31.53/4.50  --instantiation_flag                    true
% 31.53/4.50  --inst_sos_flag                         true
% 31.53/4.50  --inst_sos_phase                        true
% 31.53/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.53/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.53/4.50  --inst_lit_sel_side                     num_symb
% 31.53/4.50  --inst_solver_per_active                1400
% 31.53/4.50  --inst_solver_calls_frac                1.
% 31.53/4.50  --inst_passive_queue_type               priority_queues
% 31.53/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.53/4.50  --inst_passive_queues_freq              [25;2]
% 31.53/4.50  --inst_dismatching                      true
% 31.53/4.50  --inst_eager_unprocessed_to_passive     true
% 31.53/4.50  --inst_prop_sim_given                   true
% 31.53/4.50  --inst_prop_sim_new                     false
% 31.53/4.50  --inst_subs_new                         false
% 31.53/4.50  --inst_eq_res_simp                      false
% 31.53/4.50  --inst_subs_given                       false
% 31.53/4.50  --inst_orphan_elimination               true
% 31.53/4.50  --inst_learning_loop_flag               true
% 31.53/4.50  --inst_learning_start                   3000
% 31.53/4.50  --inst_learning_factor                  2
% 31.53/4.50  --inst_start_prop_sim_after_learn       3
% 31.53/4.50  --inst_sel_renew                        solver
% 31.53/4.50  --inst_lit_activity_flag                true
% 31.53/4.50  --inst_restr_to_given                   false
% 31.53/4.50  --inst_activity_threshold               500
% 31.53/4.50  --inst_out_proof                        true
% 31.53/4.50  
% 31.53/4.50  ------ Resolution Options
% 31.53/4.50  
% 31.53/4.50  --resolution_flag                       true
% 31.53/4.50  --res_lit_sel                           adaptive
% 31.53/4.50  --res_lit_sel_side                      none
% 31.53/4.50  --res_ordering                          kbo
% 31.53/4.50  --res_to_prop_solver                    active
% 31.53/4.50  --res_prop_simpl_new                    false
% 31.53/4.50  --res_prop_simpl_given                  true
% 31.53/4.50  --res_passive_queue_type                priority_queues
% 31.53/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.53/4.50  --res_passive_queues_freq               [15;5]
% 31.53/4.50  --res_forward_subs                      full
% 31.53/4.50  --res_backward_subs                     full
% 31.53/4.50  --res_forward_subs_resolution           true
% 31.53/4.50  --res_backward_subs_resolution          true
% 31.53/4.50  --res_orphan_elimination                true
% 31.53/4.50  --res_time_limit                        2.
% 31.53/4.50  --res_out_proof                         true
% 31.53/4.50  
% 31.53/4.50  ------ Superposition Options
% 31.53/4.50  
% 31.53/4.50  --superposition_flag                    true
% 31.53/4.50  --sup_passive_queue_type                priority_queues
% 31.53/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.53/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.53/4.50  --demod_completeness_check              fast
% 31.53/4.50  --demod_use_ground                      true
% 31.53/4.50  --sup_to_prop_solver                    passive
% 31.53/4.50  --sup_prop_simpl_new                    true
% 31.53/4.50  --sup_prop_simpl_given                  true
% 31.53/4.50  --sup_fun_splitting                     true
% 31.53/4.50  --sup_smt_interval                      50000
% 31.53/4.50  
% 31.53/4.50  ------ Superposition Simplification Setup
% 31.53/4.50  
% 31.53/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.53/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.53/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.53/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.53/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.53/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.53/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.53/4.50  --sup_immed_triv                        [TrivRules]
% 31.53/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.53/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.53/4.50  --sup_immed_bw_main                     []
% 31.53/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.53/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.53/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.53/4.50  --sup_input_bw                          []
% 31.53/4.50  
% 31.53/4.50  ------ Combination Options
% 31.53/4.50  
% 31.53/4.50  --comb_res_mult                         3
% 31.53/4.50  --comb_sup_mult                         2
% 31.53/4.50  --comb_inst_mult                        10
% 31.53/4.50  
% 31.53/4.50  ------ Debug Options
% 31.53/4.50  
% 31.53/4.50  --dbg_backtrace                         false
% 31.53/4.50  --dbg_dump_prop_clauses                 false
% 31.53/4.50  --dbg_dump_prop_clauses_file            -
% 31.53/4.50  --dbg_out_stat                          false
% 31.53/4.50  ------ Parsing...
% 31.53/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.53/4.50  
% 31.53/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.53/4.50  
% 31.53/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.53/4.50  
% 31.53/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.53/4.50  ------ Proving...
% 31.53/4.50  ------ Problem Properties 
% 31.53/4.50  
% 31.53/4.50  
% 31.53/4.50  clauses                                 35
% 31.53/4.50  conjectures                             4
% 31.53/4.50  EPR                                     6
% 31.53/4.50  Horn                                    32
% 31.53/4.50  unary                                   6
% 31.53/4.50  binary                                  8
% 31.53/4.50  lits                                    93
% 31.53/4.50  lits eq                                 28
% 31.53/4.50  fd_pure                                 0
% 31.53/4.50  fd_pseudo                               0
% 31.53/4.50  fd_cond                                 2
% 31.53/4.50  fd_pseudo_cond                          0
% 31.53/4.50  AC symbols                              0
% 31.53/4.50  
% 31.53/4.50  ------ Schedule dynamic 5 is on 
% 31.53/4.50  
% 31.53/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.53/4.50  
% 31.53/4.50  
% 31.53/4.50  ------ 
% 31.53/4.50  Current options:
% 31.53/4.50  ------ 
% 31.53/4.50  
% 31.53/4.50  ------ Input Options
% 31.53/4.50  
% 31.53/4.50  --out_options                           all
% 31.53/4.50  --tptp_safe_out                         true
% 31.53/4.50  --problem_path                          ""
% 31.53/4.50  --include_path                          ""
% 31.53/4.50  --clausifier                            res/vclausify_rel
% 31.53/4.50  --clausifier_options                    ""
% 31.53/4.50  --stdin                                 false
% 31.53/4.50  --stats_out                             all
% 31.53/4.50  
% 31.53/4.50  ------ General Options
% 31.53/4.50  
% 31.53/4.50  --fof                                   false
% 31.53/4.50  --time_out_real                         305.
% 31.53/4.50  --time_out_virtual                      -1.
% 31.53/4.50  --symbol_type_check                     false
% 31.53/4.50  --clausify_out                          false
% 31.53/4.50  --sig_cnt_out                           false
% 31.53/4.50  --trig_cnt_out                          false
% 31.53/4.50  --trig_cnt_out_tolerance                1.
% 31.53/4.50  --trig_cnt_out_sk_spl                   false
% 31.53/4.50  --abstr_cl_out                          false
% 31.53/4.50  
% 31.53/4.50  ------ Global Options
% 31.53/4.50  
% 31.53/4.50  --schedule                              default
% 31.53/4.50  --add_important_lit                     false
% 31.53/4.50  --prop_solver_per_cl                    1000
% 31.53/4.50  --min_unsat_core                        false
% 31.53/4.50  --soft_assumptions                      false
% 31.53/4.50  --soft_lemma_size                       3
% 31.53/4.50  --prop_impl_unit_size                   0
% 31.53/4.50  --prop_impl_unit                        []
% 31.53/4.50  --share_sel_clauses                     true
% 31.53/4.50  --reset_solvers                         false
% 31.53/4.50  --bc_imp_inh                            [conj_cone]
% 31.53/4.50  --conj_cone_tolerance                   3.
% 31.53/4.50  --extra_neg_conj                        none
% 31.53/4.50  --large_theory_mode                     true
% 31.53/4.50  --prolific_symb_bound                   200
% 31.53/4.50  --lt_threshold                          2000
% 31.53/4.50  --clause_weak_htbl                      true
% 31.53/4.50  --gc_record_bc_elim                     false
% 31.53/4.50  
% 31.53/4.50  ------ Preprocessing Options
% 31.53/4.50  
% 31.53/4.50  --preprocessing_flag                    true
% 31.53/4.50  --time_out_prep_mult                    0.1
% 31.53/4.50  --splitting_mode                        input
% 31.53/4.50  --splitting_grd                         true
% 31.53/4.50  --splitting_cvd                         false
% 31.53/4.50  --splitting_cvd_svl                     false
% 31.53/4.50  --splitting_nvd                         32
% 31.53/4.50  --sub_typing                            true
% 31.53/4.50  --prep_gs_sim                           true
% 31.53/4.50  --prep_unflatten                        true
% 31.53/4.50  --prep_res_sim                          true
% 31.53/4.50  --prep_upred                            true
% 31.53/4.50  --prep_sem_filter                       exhaustive
% 31.53/4.50  --prep_sem_filter_out                   false
% 31.53/4.50  --pred_elim                             true
% 31.53/4.50  --res_sim_input                         true
% 31.53/4.50  --eq_ax_congr_red                       true
% 31.53/4.50  --pure_diseq_elim                       true
% 31.53/4.50  --brand_transform                       false
% 31.53/4.50  --non_eq_to_eq                          false
% 31.53/4.50  --prep_def_merge                        true
% 31.53/4.50  --prep_def_merge_prop_impl              false
% 31.53/4.50  --prep_def_merge_mbd                    true
% 31.53/4.50  --prep_def_merge_tr_red                 false
% 31.53/4.50  --prep_def_merge_tr_cl                  false
% 31.53/4.50  --smt_preprocessing                     true
% 31.53/4.50  --smt_ac_axioms                         fast
% 31.53/4.50  --preprocessed_out                      false
% 31.53/4.50  --preprocessed_stats                    false
% 31.53/4.50  
% 31.53/4.50  ------ Abstraction refinement Options
% 31.53/4.50  
% 31.53/4.50  --abstr_ref                             []
% 31.53/4.50  --abstr_ref_prep                        false
% 31.53/4.50  --abstr_ref_until_sat                   false
% 31.53/4.50  --abstr_ref_sig_restrict                funpre
% 31.53/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.53/4.50  --abstr_ref_under                       []
% 31.53/4.50  
% 31.53/4.50  ------ SAT Options
% 31.53/4.50  
% 31.53/4.50  --sat_mode                              false
% 31.53/4.50  --sat_fm_restart_options                ""
% 31.53/4.50  --sat_gr_def                            false
% 31.53/4.50  --sat_epr_types                         true
% 31.53/4.50  --sat_non_cyclic_types                  false
% 31.53/4.50  --sat_finite_models                     false
% 31.53/4.50  --sat_fm_lemmas                         false
% 31.53/4.50  --sat_fm_prep                           false
% 31.53/4.50  --sat_fm_uc_incr                        true
% 31.53/4.50  --sat_out_model                         small
% 31.53/4.50  --sat_out_clauses                       false
% 31.53/4.50  
% 31.53/4.50  ------ QBF Options
% 31.53/4.50  
% 31.53/4.50  --qbf_mode                              false
% 31.53/4.50  --qbf_elim_univ                         false
% 31.53/4.50  --qbf_dom_inst                          none
% 31.53/4.50  --qbf_dom_pre_inst                      false
% 31.53/4.50  --qbf_sk_in                             false
% 31.53/4.50  --qbf_pred_elim                         true
% 31.53/4.50  --qbf_split                             512
% 31.53/4.50  
% 31.53/4.50  ------ BMC1 Options
% 31.53/4.50  
% 31.53/4.50  --bmc1_incremental                      false
% 31.53/4.50  --bmc1_axioms                           reachable_all
% 31.53/4.50  --bmc1_min_bound                        0
% 31.53/4.50  --bmc1_max_bound                        -1
% 31.53/4.50  --bmc1_max_bound_default                -1
% 31.53/4.50  --bmc1_symbol_reachability              true
% 31.53/4.50  --bmc1_property_lemmas                  false
% 31.53/4.50  --bmc1_k_induction                      false
% 31.53/4.50  --bmc1_non_equiv_states                 false
% 31.53/4.50  --bmc1_deadlock                         false
% 31.53/4.50  --bmc1_ucm                              false
% 31.53/4.50  --bmc1_add_unsat_core                   none
% 31.53/4.50  --bmc1_unsat_core_children              false
% 31.53/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.53/4.50  --bmc1_out_stat                         full
% 31.53/4.50  --bmc1_ground_init                      false
% 31.53/4.50  --bmc1_pre_inst_next_state              false
% 31.53/4.50  --bmc1_pre_inst_state                   false
% 31.53/4.50  --bmc1_pre_inst_reach_state             false
% 31.53/4.50  --bmc1_out_unsat_core                   false
% 31.53/4.50  --bmc1_aig_witness_out                  false
% 31.53/4.50  --bmc1_verbose                          false
% 31.53/4.50  --bmc1_dump_clauses_tptp                false
% 31.53/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.53/4.50  --bmc1_dump_file                        -
% 31.53/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.53/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.53/4.50  --bmc1_ucm_extend_mode                  1
% 31.53/4.50  --bmc1_ucm_init_mode                    2
% 31.53/4.50  --bmc1_ucm_cone_mode                    none
% 31.53/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.53/4.50  --bmc1_ucm_relax_model                  4
% 31.53/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.53/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.53/4.50  --bmc1_ucm_layered_model                none
% 31.53/4.50  --bmc1_ucm_max_lemma_size               10
% 31.53/4.50  
% 31.53/4.50  ------ AIG Options
% 31.53/4.50  
% 31.53/4.50  --aig_mode                              false
% 31.53/4.50  
% 31.53/4.50  ------ Instantiation Options
% 31.53/4.50  
% 31.53/4.50  --instantiation_flag                    true
% 31.53/4.50  --inst_sos_flag                         true
% 31.53/4.50  --inst_sos_phase                        true
% 31.53/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.53/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.53/4.50  --inst_lit_sel_side                     none
% 31.53/4.50  --inst_solver_per_active                1400
% 31.53/4.50  --inst_solver_calls_frac                1.
% 31.53/4.50  --inst_passive_queue_type               priority_queues
% 31.53/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.53/4.50  --inst_passive_queues_freq              [25;2]
% 31.53/4.50  --inst_dismatching                      true
% 31.53/4.50  --inst_eager_unprocessed_to_passive     true
% 31.53/4.50  --inst_prop_sim_given                   true
% 31.53/4.50  --inst_prop_sim_new                     false
% 31.53/4.50  --inst_subs_new                         false
% 31.53/4.50  --inst_eq_res_simp                      false
% 31.53/4.50  --inst_subs_given                       false
% 31.53/4.50  --inst_orphan_elimination               true
% 31.53/4.50  --inst_learning_loop_flag               true
% 31.53/4.50  --inst_learning_start                   3000
% 31.53/4.50  --inst_learning_factor                  2
% 31.53/4.50  --inst_start_prop_sim_after_learn       3
% 31.53/4.50  --inst_sel_renew                        solver
% 31.53/4.50  --inst_lit_activity_flag                true
% 31.53/4.50  --inst_restr_to_given                   false
% 31.53/4.50  --inst_activity_threshold               500
% 31.53/4.50  --inst_out_proof                        true
% 31.53/4.50  
% 31.53/4.50  ------ Resolution Options
% 31.53/4.50  
% 31.53/4.50  --resolution_flag                       false
% 31.53/4.50  --res_lit_sel                           adaptive
% 31.53/4.50  --res_lit_sel_side                      none
% 31.53/4.50  --res_ordering                          kbo
% 31.53/4.50  --res_to_prop_solver                    active
% 31.53/4.50  --res_prop_simpl_new                    false
% 31.53/4.50  --res_prop_simpl_given                  true
% 31.53/4.50  --res_passive_queue_type                priority_queues
% 31.53/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.53/4.50  --res_passive_queues_freq               [15;5]
% 31.53/4.50  --res_forward_subs                      full
% 31.53/4.50  --res_backward_subs                     full
% 31.53/4.50  --res_forward_subs_resolution           true
% 31.53/4.50  --res_backward_subs_resolution          true
% 31.53/4.50  --res_orphan_elimination                true
% 31.53/4.50  --res_time_limit                        2.
% 31.53/4.50  --res_out_proof                         true
% 31.53/4.50  
% 31.53/4.50  ------ Superposition Options
% 31.53/4.50  
% 31.53/4.50  --superposition_flag                    true
% 31.53/4.50  --sup_passive_queue_type                priority_queues
% 31.53/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.53/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.53/4.50  --demod_completeness_check              fast
% 31.53/4.50  --demod_use_ground                      true
% 31.53/4.50  --sup_to_prop_solver                    passive
% 31.53/4.50  --sup_prop_simpl_new                    true
% 31.53/4.50  --sup_prop_simpl_given                  true
% 31.53/4.50  --sup_fun_splitting                     true
% 31.53/4.50  --sup_smt_interval                      50000
% 31.53/4.50  
% 31.53/4.50  ------ Superposition Simplification Setup
% 31.53/4.50  
% 31.53/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.53/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.53/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.53/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.53/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.53/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.53/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.53/4.50  --sup_immed_triv                        [TrivRules]
% 31.53/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.53/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.53/4.50  --sup_immed_bw_main                     []
% 31.53/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.53/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.53/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.53/4.50  --sup_input_bw                          []
% 31.53/4.50  
% 31.53/4.50  ------ Combination Options
% 31.53/4.50  
% 31.53/4.50  --comb_res_mult                         3
% 31.53/4.50  --comb_sup_mult                         2
% 31.53/4.50  --comb_inst_mult                        10
% 31.53/4.50  
% 31.53/4.50  ------ Debug Options
% 31.53/4.50  
% 31.53/4.50  --dbg_backtrace                         false
% 31.53/4.50  --dbg_dump_prop_clauses                 false
% 31.53/4.50  --dbg_dump_prop_clauses_file            -
% 31.53/4.50  --dbg_out_stat                          false
% 31.53/4.50  
% 31.53/4.50  
% 31.53/4.50  
% 31.53/4.50  
% 31.53/4.50  ------ Proving...
% 31.53/4.50  
% 31.53/4.50  
% 31.53/4.50  % SZS status Theorem for theBenchmark.p
% 31.53/4.50  
% 31.53/4.50   Resolution empty clause
% 31.53/4.50  
% 31.53/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.53/4.50  
% 31.53/4.50  fof(f19,conjecture,(
% 31.53/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f20,negated_conjecture,(
% 31.53/4.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 31.53/4.50    inference(negated_conjecture,[],[f19])).
% 31.53/4.50  
% 31.53/4.50  fof(f46,plain,(
% 31.53/4.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 31.53/4.50    inference(ennf_transformation,[],[f20])).
% 31.53/4.50  
% 31.53/4.50  fof(f47,plain,(
% 31.53/4.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 31.53/4.50    inference(flattening,[],[f46])).
% 31.53/4.50  
% 31.53/4.50  fof(f53,plain,(
% 31.53/4.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 31.53/4.50    introduced(choice_axiom,[])).
% 31.53/4.50  
% 31.53/4.50  fof(f54,plain,(
% 31.53/4.50    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 31.53/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f53])).
% 31.53/4.50  
% 31.53/4.50  fof(f87,plain,(
% 31.53/4.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.53/4.50    inference(cnf_transformation,[],[f54])).
% 31.53/4.50  
% 31.53/4.50  fof(f17,axiom,(
% 31.53/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f42,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 31.53/4.50    inference(ennf_transformation,[],[f17])).
% 31.53/4.50  
% 31.53/4.50  fof(f43,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 31.53/4.50    inference(flattening,[],[f42])).
% 31.53/4.50  
% 31.53/4.50  fof(f82,plain,(
% 31.53/4.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f43])).
% 31.53/4.50  
% 31.53/4.50  fof(f18,axiom,(
% 31.53/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f44,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 31.53/4.50    inference(ennf_transformation,[],[f18])).
% 31.53/4.50  
% 31.53/4.50  fof(f45,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 31.53/4.50    inference(flattening,[],[f44])).
% 31.53/4.50  
% 31.53/4.50  fof(f84,plain,(
% 31.53/4.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f45])).
% 31.53/4.50  
% 31.53/4.50  fof(f85,plain,(
% 31.53/4.50    v1_funct_1(sK3)),
% 31.53/4.50    inference(cnf_transformation,[],[f54])).
% 31.53/4.50  
% 31.53/4.50  fof(f12,axiom,(
% 31.53/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f21,plain,(
% 31.53/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 31.53/4.50    inference(pure_predicate_removal,[],[f12])).
% 31.53/4.50  
% 31.53/4.50  fof(f34,plain,(
% 31.53/4.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.53/4.50    inference(ennf_transformation,[],[f21])).
% 31.53/4.50  
% 31.53/4.50  fof(f72,plain,(
% 31.53/4.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f34])).
% 31.53/4.50  
% 31.53/4.50  fof(f7,axiom,(
% 31.53/4.50    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f27,plain,(
% 31.53/4.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 31.53/4.50    inference(ennf_transformation,[],[f7])).
% 31.53/4.50  
% 31.53/4.50  fof(f28,plain,(
% 31.53/4.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 31.53/4.50    inference(flattening,[],[f27])).
% 31.53/4.50  
% 31.53/4.50  fof(f66,plain,(
% 31.53/4.50    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f28])).
% 31.53/4.50  
% 31.53/4.50  fof(f4,axiom,(
% 31.53/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f50,plain,(
% 31.53/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.53/4.50    inference(nnf_transformation,[],[f4])).
% 31.53/4.50  
% 31.53/4.50  fof(f60,plain,(
% 31.53/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f50])).
% 31.53/4.50  
% 31.53/4.50  fof(f5,axiom,(
% 31.53/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f25,plain,(
% 31.53/4.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.53/4.50    inference(ennf_transformation,[],[f5])).
% 31.53/4.50  
% 31.53/4.50  fof(f62,plain,(
% 31.53/4.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f25])).
% 31.53/4.50  
% 31.53/4.50  fof(f61,plain,(
% 31.53/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f50])).
% 31.53/4.50  
% 31.53/4.50  fof(f8,axiom,(
% 31.53/4.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f68,plain,(
% 31.53/4.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f8])).
% 31.53/4.50  
% 31.53/4.50  fof(f6,axiom,(
% 31.53/4.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f26,plain,(
% 31.53/4.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.53/4.50    inference(ennf_transformation,[],[f6])).
% 31.53/4.50  
% 31.53/4.50  fof(f51,plain,(
% 31.53/4.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.53/4.50    inference(nnf_transformation,[],[f26])).
% 31.53/4.50  
% 31.53/4.50  fof(f63,plain,(
% 31.53/4.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f51])).
% 31.53/4.50  
% 31.53/4.50  fof(f15,axiom,(
% 31.53/4.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f38,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 31.53/4.50    inference(ennf_transformation,[],[f15])).
% 31.53/4.50  
% 31.53/4.50  fof(f39,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 31.53/4.50    inference(flattening,[],[f38])).
% 31.53/4.50  
% 31.53/4.50  fof(f75,plain,(
% 31.53/4.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f39])).
% 31.53/4.50  
% 31.53/4.50  fof(f14,axiom,(
% 31.53/4.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f36,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 31.53/4.50    inference(ennf_transformation,[],[f14])).
% 31.53/4.50  
% 31.53/4.50  fof(f37,plain,(
% 31.53/4.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 31.53/4.50    inference(flattening,[],[f36])).
% 31.53/4.50  
% 31.53/4.50  fof(f74,plain,(
% 31.53/4.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f37])).
% 31.53/4.50  
% 31.53/4.50  fof(f13,axiom,(
% 31.53/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f35,plain,(
% 31.53/4.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.53/4.50    inference(ennf_transformation,[],[f13])).
% 31.53/4.50  
% 31.53/4.50  fof(f73,plain,(
% 31.53/4.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f35])).
% 31.53/4.50  
% 31.53/4.50  fof(f83,plain,(
% 31.53/4.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f43])).
% 31.53/4.50  
% 31.53/4.50  fof(f10,axiom,(
% 31.53/4.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f31,plain,(
% 31.53/4.50    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 31.53/4.50    inference(ennf_transformation,[],[f10])).
% 31.53/4.50  
% 31.53/4.50  fof(f70,plain,(
% 31.53/4.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f31])).
% 31.53/4.50  
% 31.53/4.50  fof(f16,axiom,(
% 31.53/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f40,plain,(
% 31.53/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.53/4.50    inference(ennf_transformation,[],[f16])).
% 31.53/4.50  
% 31.53/4.50  fof(f41,plain,(
% 31.53/4.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.53/4.50    inference(flattening,[],[f40])).
% 31.53/4.50  
% 31.53/4.50  fof(f52,plain,(
% 31.53/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.53/4.50    inference(nnf_transformation,[],[f41])).
% 31.53/4.50  
% 31.53/4.50  fof(f78,plain,(
% 31.53/4.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f52])).
% 31.53/4.50  
% 31.53/4.50  fof(f90,plain,(
% 31.53/4.50    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 31.53/4.50    inference(cnf_transformation,[],[f54])).
% 31.53/4.50  
% 31.53/4.50  fof(f89,plain,(
% 31.53/4.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 31.53/4.50    inference(cnf_transformation,[],[f54])).
% 31.53/4.50  
% 31.53/4.50  fof(f3,axiom,(
% 31.53/4.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f48,plain,(
% 31.53/4.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.53/4.50    inference(nnf_transformation,[],[f3])).
% 31.53/4.50  
% 31.53/4.50  fof(f49,plain,(
% 31.53/4.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.53/4.50    inference(flattening,[],[f48])).
% 31.53/4.50  
% 31.53/4.50  fof(f57,plain,(
% 31.53/4.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f49])).
% 31.53/4.50  
% 31.53/4.50  fof(f58,plain,(
% 31.53/4.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 31.53/4.50    inference(cnf_transformation,[],[f49])).
% 31.53/4.50  
% 31.53/4.50  fof(f92,plain,(
% 31.53/4.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 31.53/4.50    inference(equality_resolution,[],[f58])).
% 31.53/4.50  
% 31.53/4.50  fof(f59,plain,(
% 31.53/4.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 31.53/4.50    inference(cnf_transformation,[],[f49])).
% 31.53/4.50  
% 31.53/4.50  fof(f91,plain,(
% 31.53/4.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 31.53/4.50    inference(equality_resolution,[],[f59])).
% 31.53/4.50  
% 31.53/4.50  fof(f2,axiom,(
% 31.53/4.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f24,plain,(
% 31.53/4.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 31.53/4.50    inference(ennf_transformation,[],[f2])).
% 31.53/4.50  
% 31.53/4.50  fof(f56,plain,(
% 31.53/4.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f24])).
% 31.53/4.50  
% 31.53/4.50  fof(f88,plain,(
% 31.53/4.50    r1_tarski(sK2,sK0)),
% 31.53/4.50    inference(cnf_transformation,[],[f54])).
% 31.53/4.50  
% 31.53/4.50  fof(f76,plain,(
% 31.53/4.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.53/4.50    inference(cnf_transformation,[],[f52])).
% 31.53/4.50  
% 31.53/4.50  fof(f86,plain,(
% 31.53/4.50    v1_funct_2(sK3,sK0,sK1)),
% 31.53/4.50    inference(cnf_transformation,[],[f54])).
% 31.53/4.50  
% 31.53/4.50  fof(f11,axiom,(
% 31.53/4.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f32,plain,(
% 31.53/4.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 31.53/4.50    inference(ennf_transformation,[],[f11])).
% 31.53/4.50  
% 31.53/4.50  fof(f33,plain,(
% 31.53/4.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 31.53/4.50    inference(flattening,[],[f32])).
% 31.53/4.50  
% 31.53/4.50  fof(f71,plain,(
% 31.53/4.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f33])).
% 31.53/4.50  
% 31.53/4.50  fof(f1,axiom,(
% 31.53/4.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 31.53/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.53/4.50  
% 31.53/4.50  fof(f22,plain,(
% 31.53/4.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 31.53/4.50    inference(ennf_transformation,[],[f1])).
% 31.53/4.50  
% 31.53/4.50  fof(f23,plain,(
% 31.53/4.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 31.53/4.50    inference(flattening,[],[f22])).
% 31.53/4.50  
% 31.53/4.50  fof(f55,plain,(
% 31.53/4.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 31.53/4.50    inference(cnf_transformation,[],[f23])).
% 31.53/4.50  
% 31.53/4.50  cnf(c_33,negated_conjecture,
% 31.53/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.53/4.50      inference(cnf_transformation,[],[f87]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1539,plain,
% 31.53/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_28,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | ~ v1_funct_1(X0)
% 31.53/4.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 31.53/4.50      inference(cnf_transformation,[],[f82]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1542,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.53/4.50      | v1_funct_1(X0) != iProver_top
% 31.53/4.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2801,plain,
% 31.53/4.50      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 31.53/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1539,c_1542]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_29,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | ~ v1_funct_1(X0)
% 31.53/4.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 31.53/4.50      inference(cnf_transformation,[],[f84]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1541,plain,
% 31.53/4.50      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 31.53/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.53/4.50      | v1_funct_1(X2) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2225,plain,
% 31.53/4.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 31.53/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1539,c_1541]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_35,negated_conjecture,
% 31.53/4.50      ( v1_funct_1(sK3) ),
% 31.53/4.50      inference(cnf_transformation,[],[f85]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_36,plain,
% 31.53/4.50      ( v1_funct_1(sK3) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2531,plain,
% 31.53/4.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 31.53/4.50      inference(global_propositional_subsumption,[status(thm)],[c_2225,c_36]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2804,plain,
% 31.53/4.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 31.53/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.53/4.50      inference(light_normalisation,[status(thm)],[c_2801,c_2531]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_3101,plain,
% 31.53/4.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 31.53/4.50      inference(global_propositional_subsumption,[status(thm)],[c_2804,c_36]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_17,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.53/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1547,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) = iProver_top
% 31.53/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2374,plain,
% 31.53/4.50      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1539,c_1547]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_11,plain,
% 31.53/4.50      ( ~ v4_relat_1(X0,X1)
% 31.53/4.50      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 31.53/4.50      | ~ v1_relat_1(X0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1553,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) != iProver_top
% 31.53/4.50      | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
% 31.53/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4295,plain,
% 31.53/4.50      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
% 31.53/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_2374,c_1553]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_6,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.53/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1557,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.53/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2307,plain,
% 31.53/4.50      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1539,c_1557]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_7,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f62]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_5,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.53/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_250,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.53/4.50      inference(prop_impl,[status(thm)],[c_5]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_251,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.53/4.50      inference(renaming,[status(thm)],[c_250]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_314,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.53/4.50      inference(bin_hyper_res,[status(thm)],[c_7,c_251]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1537,plain,
% 31.53/4.50      ( r1_tarski(X0,X1) != iProver_top
% 31.53/4.50      | v1_relat_1(X1) != iProver_top
% 31.53/4.50      | v1_relat_1(X0) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2528,plain,
% 31.53/4.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.53/4.50      | v1_relat_1(sK3) = iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_2307,c_1537]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_13,plain,
% 31.53/4.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.53/4.50      inference(cnf_transformation,[],[f68]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2571,plain,
% 31.53/4.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_13]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2572,plain,
% 31.53/4.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_2571]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4501,plain,
% 31.53/4.50      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
% 31.53/4.50      inference(global_propositional_subsumption,
% 31.53/4.50                [status(thm)],
% 31.53/4.50                [c_4295,c_2528,c_2572]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_9,plain,
% 31.53/4.50      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f63]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1555,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 31.53/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_20,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | ~ r1_tarski(X3,X0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f75]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1544,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.53/4.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.53/4.50      | r1_tarski(X3,X0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4151,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1539,c_1544]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_19,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 31.53/4.50      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 31.53/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1545,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.53/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4655,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4151,c_1545]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_18,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1546,plain,
% 31.53/4.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.53/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_6367,plain,
% 31.53/4.50      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 31.53/4.50      | r1_tarski(X1,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4655,c_1546]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_12791,plain,
% 31.53/4.50      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 31.53/4.50      | v4_relat_1(X1,X0) != iProver_top
% 31.53/4.50      | r1_tarski(X1,sK3) != iProver_top
% 31.53/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1555,c_6367]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_87403,plain,
% 31.53/4.50      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
% 31.53/4.50      | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
% 31.53/4.50      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4501,c_12791]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_27,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | ~ v1_funct_1(X0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f83]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1543,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.53/4.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.53/4.50      | v1_funct_1(X0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_3319,plain,
% 31.53/4.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.53/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.53/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_2531,c_1543]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_38,plain,
% 31.53/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_3596,plain,
% 31.53/4.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.53/4.50      inference(global_propositional_subsumption,
% 31.53/4.50                [status(thm)],
% 31.53/4.50                [c_3319,c_36,c_38]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_3603,plain,
% 31.53/4.50      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_3596,c_1557]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4107,plain,
% 31.53/4.50      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 31.53/4.50      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_3603,c_1537]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_15,plain,
% 31.53/4.50      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f70]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_5315,plain,
% 31.53/4.50      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_15]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_5316,plain,
% 31.53/4.50      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 31.53/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_5315]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_87634,plain,
% 31.53/4.50      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 31.53/4.50      inference(global_propositional_subsumption,
% 31.53/4.50                [status(thm)],
% 31.53/4.50                [c_87403,c_2528,c_2572,c_4107,c_5316]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_24,plain,
% 31.53/4.50      ( v1_funct_2(X0,X1,X2)
% 31.53/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | k1_relset_1(X1,X2,X0) != X1
% 31.53/4.50      | k1_xboole_0 = X2 ),
% 31.53/4.50      inference(cnf_transformation,[],[f78]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_30,negated_conjecture,
% 31.53/4.50      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 31.53/4.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 31.53/4.50      inference(cnf_transformation,[],[f90]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_511,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.53/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.53/4.50      | k1_relset_1(X1,X2,X0) != X1
% 31.53/4.50      | sK2 != X1
% 31.53/4.50      | sK1 != X2
% 31.53/4.50      | k1_xboole_0 = X2 ),
% 31.53/4.50      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_512,plain,
% 31.53/4.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.53/4.50      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 31.53/4.50      | k1_xboole_0 = sK1 ),
% 31.53/4.50      inference(unflattening,[status(thm)],[c_511]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1532,plain,
% 31.53/4.50      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 31.53/4.50      | k1_xboole_0 = sK1
% 31.53/4.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.53/4.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2537,plain,
% 31.53/4.50      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 31.53/4.50      | sK1 = k1_xboole_0
% 31.53/4.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.53/4.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.53/4.50      inference(demodulation,[status(thm)],[c_2531,c_1532]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_87637,plain,
% 31.53/4.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 31.53/4.50      | sK1 = k1_xboole_0
% 31.53/4.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.53/4.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.53/4.50      inference(demodulation,[status(thm)],[c_87634,c_2537]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_31,negated_conjecture,
% 31.53/4.50      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 31.53/4.50      inference(cnf_transformation,[],[f89]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4,plain,
% 31.53/4.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 31.53/4.50      | k1_xboole_0 = X0
% 31.53/4.50      | k1_xboole_0 = X1 ),
% 31.53/4.50      inference(cnf_transformation,[],[f57]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_108,plain,
% 31.53/4.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.53/4.50      | k1_xboole_0 = k1_xboole_0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_4]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_3,plain,
% 31.53/4.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.53/4.50      inference(cnf_transformation,[],[f92]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_109,plain,
% 31.53/4.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_860,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1606,plain,
% 31.53/4.50      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_860]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1614,plain,
% 31.53/4.50      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_1606]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_859,plain,( X0 = X0 ),theory(equality) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1627,plain,
% 31.53/4.50      ( sK0 = sK0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_859]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1651,plain,
% 31.53/4.50      ( sK2 = sK2 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_859]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2,plain,
% 31.53/4.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.53/4.50      inference(cnf_transformation,[],[f91]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1551,plain,
% 31.53/4.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1973,plain,
% 31.53/4.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_2,c_1551]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1777,plain,
% 31.53/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_6]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2003,plain,
% 31.53/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.53/4.50      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_1777]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2004,plain,
% 31.53/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.53/4.50      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_2003]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1549,plain,
% 31.53/4.50      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 31.53/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 31.53/4.50      inference(cnf_transformation,[],[f56]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1559,plain,
% 31.53/4.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2164,plain,
% 31.53/4.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 31.53/4.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1549,c_1559]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2219,plain,
% 31.53/4.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.53/4.50      inference(global_propositional_subsumption,[status(thm)],[c_2164,c_1973]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2222,plain,
% 31.53/4.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 31.53/4.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_2219,c_1549]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2390,plain,
% 31.53/4.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_860]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2391,plain,
% 31.53/4.50      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_2390]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_861,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.53/4.50      theory(equality) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2770,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,X1)
% 31.53/4.50      | r1_tarski(sK0,k1_xboole_0)
% 31.53/4.50      | sK0 != X0
% 31.53/4.50      | k1_xboole_0 != X1 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_861]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2771,plain,
% 31.53/4.50      ( sK0 != X0
% 31.53/4.50      | k1_xboole_0 != X1
% 31.53/4.50      | r1_tarski(X0,X1) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2773,plain,
% 31.53/4.50      ( sK0 != k1_xboole_0
% 31.53/4.50      | k1_xboole_0 != k1_xboole_0
% 31.53/4.50      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 31.53/4.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_2771]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_32,negated_conjecture,
% 31.53/4.50      ( r1_tarski(sK2,sK0) ),
% 31.53/4.50      inference(cnf_transformation,[],[f88]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1540,plain,
% 31.53/4.50      ( r1_tarski(sK2,sK0) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_26,plain,
% 31.53/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.53/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | k1_relset_1(X1,X2,X0) = X1
% 31.53/4.50      | k1_xboole_0 = X2 ),
% 31.53/4.50      inference(cnf_transformation,[],[f76]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_34,negated_conjecture,
% 31.53/4.50      ( v1_funct_2(sK3,sK0,sK1) ),
% 31.53/4.50      inference(cnf_transformation,[],[f86]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_527,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.50      | k1_relset_1(X1,X2,X0) = X1
% 31.53/4.50      | sK3 != X0
% 31.53/4.50      | sK1 != X2
% 31.53/4.50      | sK0 != X1
% 31.53/4.50      | k1_xboole_0 = X2 ),
% 31.53/4.50      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_528,plain,
% 31.53/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.53/4.50      | k1_relset_1(sK0,sK1,sK3) = sK0
% 31.53/4.50      | k1_xboole_0 = sK1 ),
% 31.53/4.50      inference(unflattening,[status(thm)],[c_527]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_530,plain,
% 31.53/4.50      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 31.53/4.50      inference(global_propositional_subsumption,[status(thm)],[c_528,c_33]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2911,plain,
% 31.53/4.50      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1539,c_1546]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_3049,plain,
% 31.53/4.50      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_530,c_2911]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_16,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 31.53/4.50      | ~ v1_relat_1(X1)
% 31.53/4.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 31.53/4.50      inference(cnf_transformation,[],[f71]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1548,plain,
% 31.53/4.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 31.53/4.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 31.53/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4284,plain,
% 31.53/4.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.53/4.50      | sK1 = k1_xboole_0
% 31.53/4.50      | r1_tarski(X0,sK0) != iProver_top
% 31.53/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_3049,c_1548]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_7592,plain,
% 31.53/4.50      ( r1_tarski(X0,sK0) != iProver_top
% 31.53/4.50      | sK1 = k1_xboole_0
% 31.53/4.50      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 31.53/4.50      inference(global_propositional_subsumption,
% 31.53/4.50                [status(thm)],
% 31.53/4.50                [c_4284,c_2528,c_2572]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_7593,plain,
% 31.53/4.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.53/4.50      | sK1 = k1_xboole_0
% 31.53/4.50      | r1_tarski(X0,sK0) != iProver_top ),
% 31.53/4.50      inference(renaming,[status(thm)],[c_7592]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_7600,plain,
% 31.53/4.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1540,c_7593]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_7963,plain,
% 31.53/4.50      ( sK1 = k1_xboole_0
% 31.53/4.50      | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
% 31.53/4.50      | r1_tarski(sK2,X0) = iProver_top
% 31.53/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_7600,c_1555]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_8061,plain,
% 31.53/4.50      ( sK1 = k1_xboole_0
% 31.53/4.50      | r1_tarski(sK2,sK2) = iProver_top
% 31.53/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4501,c_7963]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_50413,plain,
% 31.53/4.50      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~ v1_relat_1(sK3) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_5315]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_50414,plain,
% 31.53/4.50      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
% 31.53/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_50413]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_6364,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(X0,X2) != iProver_top
% 31.53/4.50      | r1_tarski(X2,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4655,c_1544]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_35906,plain,
% 31.53/4.50      ( sK1 = k1_xboole_0
% 31.53/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(sK3,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_3049,c_6364]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_95,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 31.53/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_0,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 31.53/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1560,plain,
% 31.53/4.50      ( r1_tarski(X0,X1) != iProver_top
% 31.53/4.50      | r1_tarski(X2,X0) != iProver_top
% 31.53/4.50      | r1_tarski(X2,X1) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4173,plain,
% 31.53/4.50      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_2307,c_1560]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4574,plain,
% 31.53/4.50      ( r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | v1_relat_1(X0) = iProver_top
% 31.53/4.50      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4173,c_1537]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4653,plain,
% 31.53/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1539,c_1545]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4805,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4653,c_1544]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_6392,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_4805,c_1547]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_10202,plain,
% 31.53/4.50      ( sK1 = k1_xboole_0
% 31.53/4.50      | v4_relat_1(X0,X1) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_3049,c_6392]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2375,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) = iProver_top
% 31.53/4.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_2,c_1547]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2640,plain,
% 31.53/4.50      ( ~ v4_relat_1(sK3,sK0)
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),sK0)
% 31.53/4.50      | ~ v1_relat_1(sK3) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_9]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2641,plain,
% 31.53/4.50      ( v4_relat_1(sK3,sK0) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 31.53/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_2640]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_3097,plain,
% 31.53/4.50      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_859]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1769,plain,
% 31.53/4.50      ( ~ r1_tarski(X0,X1)
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 31.53/4.50      | k1_relat_1(sK3) != X0
% 31.53/4.50      | k1_xboole_0 != X1 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_861]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_2030,plain,
% 31.53/4.50      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 31.53/4.50      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.53/4.50      | k1_xboole_0 != X0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_1769]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_5830,plain,
% 31.53/4.50      ( ~ r1_tarski(k1_relat_1(sK3),sK0)
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 31.53/4.50      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.53/4.50      | k1_xboole_0 != sK0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_2030]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_5831,plain,
% 31.53/4.50      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 31.53/4.50      | k1_xboole_0 != sK0
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_5830]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_6387,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_3,c_4805]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_10604,plain,
% 31.53/4.50      ( v4_relat_1(X0,X1) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,X1) != iProver_top ),
% 31.53/4.50      inference(global_propositional_subsumption,
% 31.53/4.50                [status(thm)],
% 31.53/4.50                [c_10202,c_31,c_108,c_109,c_2374,c_2375,c_2391,c_2528,c_2572,
% 31.53/4.50                 c_2641,c_3097,c_5831,c_6387]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_36124,plain,
% 31.53/4.50      ( r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(sK0,X1) != iProver_top ),
% 31.53/4.50      inference(global_propositional_subsumption,
% 31.53/4.50                [status(thm)],
% 31.53/4.50                [c_35906,c_95,c_2572,c_4574,c_4655,c_10604]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_36125,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,X1) != iProver_top ),
% 31.53/4.50      inference(renaming,[status(thm)],[c_36124]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_36133,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(X0,X2) != iProver_top
% 31.53/4.50      | r1_tarski(X2,sK3) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,X1) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_36125,c_1544]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_37601,plain,
% 31.53/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.53/4.50      | r1_tarski(sK0,X0) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1540,c_36133]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_37802,plain,
% 31.53/4.50      ( r1_tarski(sK2,k2_zfmisc_1(X0,sK1)) = iProver_top
% 31.53/4.50      | r1_tarski(sK0,X0) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_37601,c_1557]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1558,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.53/4.50      | r1_tarski(X0,X1) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4154,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
% 31.53/4.50      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.53/4.50      | r1_tarski(X0,X2) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_3,c_1544]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4155,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.53/4.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.53/4.50      inference(demodulation,[status(thm)],[c_4154,c_3]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_4714,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.50      | r1_tarski(X0,X1) != iProver_top
% 31.53/4.50      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_1558,c_4155]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_37837,plain,
% 31.53/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.50      | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,X0) != iProver_top
% 31.53/4.50      | r1_tarski(sK0,sK3) != iProver_top ),
% 31.53/4.50      inference(superposition,[status(thm)],[c_37802,c_4714]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_97,plain,
% 31.53/4.50      ( v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 31.53/4.50      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 31.53/4.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_95]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_106,plain,
% 31.53/4.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 31.53/4.50      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_5]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_105,plain,
% 31.53/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.53/4.50      | r1_tarski(X0,X1) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_107,plain,
% 31.53/4.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_105]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_538,plain,
% 31.53/4.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.53/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 31.53/4.50      | sK2 != sK0
% 31.53/4.50      | sK1 != sK1 ),
% 31.53/4.50      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1608,plain,
% 31.53/4.50      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_860]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1609,plain,
% 31.53/4.50      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_1608]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1605,plain,
% 31.53/4.50      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_860]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1612,plain,
% 31.53/4.50      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_1605]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1618,plain,
% 31.53/4.50      ( sK1 = sK1 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_859]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1621,plain,
% 31.53/4.50      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_1]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1622,plain,
% 31.53/4.50      ( k1_xboole_0 = sK2 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 31.53/4.50      inference(predicate_to_equality,[status(thm)],[c_1621]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1687,plain,
% 31.53/4.50      ( ~ v4_relat_1(k1_xboole_0,sK2)
% 31.53/4.50      | r1_tarski(k1_relat_1(k1_xboole_0),sK2)
% 31.53/4.50      | ~ v1_relat_1(k1_xboole_0) ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_9]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_864,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.53/4.50      theory(equality) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1642,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,X1)
% 31.53/4.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 31.53/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
% 31.53/4.50      | k1_xboole_0 != X0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_864]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1708,plain,
% 31.53/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.53/4.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 31.53/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X1)
% 31.53/4.50      | k1_xboole_0 != X0 ),
% 31.53/4.50      inference(instantiation,[status(thm)],[c_1642]) ).
% 31.53/4.50  
% 31.53/4.50  cnf(c_1710,plain,
% 31.53/4.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 31.53/4.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 31.53/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 31.53/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1708]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1709,plain,
% 31.53/4.51      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(X0)
% 31.53/4.51      | k1_xboole_0 != X1
% 31.53/4.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_1708]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1711,plain,
% 31.53/4.51      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 31.53/4.51      | k1_xboole_0 != k1_xboole_0
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1709]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1778,plain,
% 31.53/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 31.53/4.51      | r1_tarski(sK3,X0) = iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_1777]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1780,plain,
% 31.53/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.53/4.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1778]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_863,plain,
% 31.53/4.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 31.53/4.51      theory(equality) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1897,plain,
% 31.53/4.51      ( k2_zfmisc_1(sK2,k1_xboole_0) != X0
% 31.53/4.51      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_863]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1898,plain,
% 31.53/4.51      ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0
% 31.53/4.51      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1897]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1975,plain,
% 31.53/4.51      ( v1_relat_1(k1_xboole_0) ),
% 31.53/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_1973]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2022,plain,
% 31.53/4.51      ( sK3 = sK3 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_859]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_1792,plain,
% 31.53/4.51      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_860]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2039,plain,
% 31.53/4.51      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1792]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2040,plain,
% 31.53/4.51      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2039]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2099,plain,
% 31.53/4.51      ( v4_relat_1(k1_xboole_0,sK2)
% 31.53/4.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_17]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2101,plain,
% 31.53/4.51      ( v4_relat_1(k1_xboole_0,sK2)
% 31.53/4.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2099]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2120,plain,
% 31.53/4.51      ( k2_zfmisc_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2223,plain,
% 31.53/4.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) | ~ v1_relat_1(k1_xboole_0) ),
% 31.53/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_2222]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2367,plain,
% 31.53/4.51      ( ~ r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2368,plain,
% 31.53/4.51      ( k1_xboole_0 = sK0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_2367]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2382,plain,
% 31.53/4.51      ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2375]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2407,plain,
% 31.53/4.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.53/4.51      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.53/4.51      | ~ v1_funct_1(sK3) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_28]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2529,plain,
% 31.53/4.51      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) ),
% 31.53/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_2528]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2611,plain,
% 31.53/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_20]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2613,plain,
% 31.53/4.51      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2611]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2619,plain,
% 31.53/4.51      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2620,plain,
% 31.53/4.51      ( k1_xboole_0 = sK3 | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_2619]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3013,plain,
% 31.53/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.53/4.51      | ~ r1_tarski(sK3,X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_20]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3014,plain,
% 31.53/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.53/4.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.53/4.51      | r1_tarski(sK3,X0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_3013]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3016,plain,
% 31.53/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 31.53/4.51      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_3014]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3493,plain,
% 31.53/4.51      ( sK1 = k1_xboole_0
% 31.53/4.51      | v4_relat_1(sK3,X0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) = iProver_top
% 31.53/4.51      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_3049,c_1555]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3499,plain,
% 31.53/4.51      ( sK1 = k1_xboole_0
% 31.53/4.51      | v4_relat_1(sK3,k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 31.53/4.51      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_3493]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2203,plain,
% 31.53/4.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_19]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3727,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 31.53/4.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2203]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3728,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_3727]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3730,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 31.53/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_3728]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4389,plain,
% 31.53/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 31.53/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(X0),sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_19]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4391,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(k1_xboole_0),sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_4389]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4624,plain,
% 31.53/4.51      ( v4_relat_1(sK3,k1_xboole_0)
% 31.53/4.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_17]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4625,plain,
% 31.53/4.51      ( v4_relat_1(sK3,k1_xboole_0) = iProver_top
% 31.53/4.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_4624]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4627,plain,
% 31.53/4.51      ( v4_relat_1(sK3,k1_xboole_0) = iProver_top
% 31.53/4.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_4625]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3496,plain,
% 31.53/4.51      ( k1_relat_1(X0) = k1_xboole_0
% 31.53/4.51      | v4_relat_1(X0,k1_xboole_0) != iProver_top
% 31.53/4.51      | v1_relat_1(X0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_1555,c_1559]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8369,plain,
% 31.53/4.51      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 31.53/4.51      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_4501,c_3496]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4110,plain,
% 31.53/4.51      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 31.53/4.51      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_4107]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8447,plain,
% 31.53/4.51      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 31.53/4.51      inference(global_propositional_subsumption,
% 31.53/4.51                [status(thm)],
% 31.53/4.51                [c_8369,c_2572,c_4110]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4654,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_3596,c_1545]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_10087,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_3,c_4654]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_10279,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_8447,c_10087]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_5318,plain,
% 31.53/4.51      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
% 31.53/4.51      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_5316]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_6361,plain,
% 31.53/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.51      | r1_tarski(X0,sK3) != iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_3,c_4655]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8449,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.51      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_8447,c_6361]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11127,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 31.53/4.51      inference(global_propositional_subsumption,
% 31.53/4.51                [status(thm)],
% 31.53/4.51                [c_10279,c_1973,c_2222,c_2528,c_2572,c_5318,c_8449]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11131,plain,
% 31.53/4.51      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_11127,c_1557]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11273,plain,
% 31.53/4.51      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_11131,c_1559]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11820,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_11273,c_4654]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11839,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top ),
% 31.53/4.51      inference(demodulation,[status(thm)],[c_11820,c_11273]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2373,plain,
% 31.53/4.51      ( v4_relat_1(X0,X1) = iProver_top
% 31.53/4.51      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_1558,c_1547]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3251,plain,
% 31.53/4.51      ( v4_relat_1(k7_relat_1(k2_zfmisc_1(X0,X1),X2),X0) = iProver_top
% 31.53/4.51      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_1549,c_2373]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_85,plain,
% 31.53/4.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8279,plain,
% 31.53/4.51      ( v4_relat_1(k7_relat_1(k2_zfmisc_1(X0,X1),X2),X0) = iProver_top ),
% 31.53/4.51      inference(global_propositional_subsumption,[status(thm)],[c_3251,c_85]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8368,plain,
% 31.53/4.51      ( k1_relat_1(k7_relat_1(k2_zfmisc_1(k1_xboole_0,X0),X1)) = k1_xboole_0
% 31.53/4.51      | v1_relat_1(k7_relat_1(k2_zfmisc_1(k1_xboole_0,X0),X1)) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_8279,c_3496]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8371,plain,
% 31.53/4.51      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 31.53/4.51      | v1_relat_1(k7_relat_1(k1_xboole_0,X0)) != iProver_top ),
% 31.53/4.51      inference(light_normalisation,[status(thm)],[c_8368,c_3]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8372,plain,
% 31.53/4.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 31.53/4.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(demodulation,[status(thm)],[c_8371,c_2219]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3508,plain,
% 31.53/4.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 31.53/4.51      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 31.53/4.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_3496]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8409,plain,
% 31.53/4.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.53/4.51      inference(global_propositional_subsumption,
% 31.53/4.51                [status(thm)],
% 31.53/4.51                [c_8372,c_107,c_1973,c_2222,c_2382,c_3508]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11840,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 31.53/4.51      inference(light_normalisation,[status(thm)],[c_11839,c_8409]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11847,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 31.53/4.51      | ~ r1_tarski(k1_xboole_0,X0) ),
% 31.53/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_11840]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_11849,plain,
% 31.53/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 31.53/4.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_11847]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3125,plain,
% 31.53/4.51      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_860]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_12115,plain,
% 31.53/4.51      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.53/4.51      | sK3 != X0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_3125]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_12116,plain,
% 31.53/4.51      ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 31.53/4.51      | sK3 != k1_xboole_0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_12115]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_17292,plain,
% 31.53/4.51      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_1540,c_4714]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_17449,plain,
% 31.53/4.51      ( r1_tarski(sK2,k1_xboole_0) = iProver_top
% 31.53/4.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_17292,c_1557]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2241,plain,
% 31.53/4.51      ( r1_tarski(X0,X1)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(X2,X3),X2)
% 31.53/4.51      | X1 != X2
% 31.53/4.51      | X0 != k7_relat_1(X2,X3) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_861]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8119,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(X1,X2),X1)
% 31.53/4.51      | X0 != X1
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(X1,X2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2241]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_21751,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.53/4.51      | X0 != sK3
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_8119]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_21753,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 31.53/4.51      | k1_xboole_0 != sK3 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_21751]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_37603,plain,
% 31.53/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.53/4.51      | r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_2307,c_36133]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2949,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,X1)
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 31.53/4.51      | r1_tarski(k1_relat_1(sK3),X1) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_0]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_5718,plain,
% 31.53/4.51      ( r1_tarski(k1_relat_1(sK3),X0)
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 31.53/4.51      | ~ r1_tarski(sK0,X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2949]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_5719,plain,
% 31.53/4.51      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_5718]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_38111,plain,
% 31.53/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top ),
% 31.53/4.51      inference(global_propositional_subsumption,
% 31.53/4.51                [status(thm)],
% 31.53/4.51                [c_37603,c_2374,c_2528,c_2572,c_2641,c_4653,c_5719]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_38118,plain,
% 31.53/4.51      ( r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_38111,c_1557]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_38484,plain,
% 31.53/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.51      | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_38118,c_4714]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_8116,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,X1)
% 31.53/4.51      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 31.53/4.51      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X1) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_0]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_41643,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 31.53/4.51      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3)
% 31.53/4.51      | ~ r1_tarski(sK3,X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_8116]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_41653,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) = iProver_top
% 31.53/4.51      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3) != iProver_top
% 31.53/4.51      | r1_tarski(sK3,X0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_41643]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_41655,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3) != iProver_top
% 31.53/4.51      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) = iProver_top
% 31.53/4.51      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_41653]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_16579,plain,
% 31.53/4.51      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 31.53/4.51      | k1_xboole_0 != X0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_860]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_48039,plain,
% 31.53/4.51      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 31.53/4.51      | k1_xboole_0 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_16579]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_49493,plain,
% 31.53/4.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.53/4.51      | ~ v1_funct_1(sK3)
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_29]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_49896,plain,
% 31.53/4.51      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_859]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_50814,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,X1)
% 31.53/4.51      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X2)
% 31.53/4.51      | X2 != X1
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != X0 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_861]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_51205,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),X1)
% 31.53/4.51      | X0 != X1
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_50814]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_51823,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.53/4.51      | X0 != sK3
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_51205]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_52718,plain,
% 31.53/4.51      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.53/4.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 31.53/4.51      | sK3 != sK3 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_51823]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_52719,plain,
% 31.53/4.51      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 31.53/4.51      | sK3 != sK3
% 31.53/4.51      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),sK3) = iProver_top
% 31.53/4.51      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_52718]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_53304,plain,
% 31.53/4.51      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 31.53/4.51      | k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_53307,plain,
% 31.53/4.51      ( k1_xboole_0 = k2_partfun1(sK0,sK1,sK3,sK2)
% 31.53/4.51      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_53304]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_53383,plain,
% 31.53/4.51      ( r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,sK3) != iProver_top ),
% 31.53/4.51      inference(global_propositional_subsumption,
% 31.53/4.51                [status(thm)],
% 31.53/4.51                [c_37837,c_35,c_33,c_31,c_97,c_106,c_107,c_108,c_109,c_538,
% 31.53/4.51                 c_1609,c_1612,c_1614,c_1618,c_1622,c_1627,c_1651,c_1687,
% 31.53/4.51                 c_1710,c_1711,c_1780,c_1898,c_1973,c_1975,c_2022,c_2040,
% 31.53/4.51                 c_2101,c_2120,c_2222,c_2223,c_2368,c_2382,c_2391,c_2407,
% 31.53/4.51                 c_2528,c_2529,c_2571,c_2572,c_2613,c_2620,c_2773,c_3016,
% 31.53/4.51                 c_3499,c_3730,c_4391,c_4627,c_11849,c_12116,c_17449,c_21753,
% 31.53/4.51                 c_38484,c_41655,c_48039,c_49493,c_49896,c_50413,c_50414,
% 31.53/4.51                 c_52719,c_53307]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2282,plain,
% 31.53/4.51      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
% 31.53/4.51      | k1_xboole_0 = k1_relat_1(X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_1]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2283,plain,
% 31.53/4.51      ( k1_xboole_0 = k1_relat_1(X0)
% 31.53/4.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_2282]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2285,plain,
% 31.53/4.51      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 31.53/4.51      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2283]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2090,plain,
% 31.53/4.51      ( r1_tarski(X0,X1)
% 31.53/4.51      | ~ r1_tarski(X0,k7_relat_1(X1,X2))
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(X1,X2),X1) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_0]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3784,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,k7_relat_1(sK3,X1))
% 31.53/4.51      | r1_tarski(X0,sK3)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,X1),sK3) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2090]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3785,plain,
% 31.53/4.51      ( r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top
% 31.53/4.51      | r1_tarski(X0,sK3) = iProver_top
% 31.53/4.51      | r1_tarski(k7_relat_1(sK3,X1),sK3) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_3784]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_3787,plain,
% 31.53/4.51      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_3785]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_4803,plain,
% 31.53/4.51      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 31.53/4.51      | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_4653,c_1557]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_17304,plain,
% 31.53/4.51      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.53/4.51      | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_4803,c_4714]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2238,plain,
% 31.53/4.51      ( r1_tarski(X0,X1)
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(X2),X3)
% 31.53/4.51      | X1 != X3
% 31.53/4.51      | X0 != k1_relat_1(X2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_861]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_20289,plain,
% 31.53/4.51      ( r1_tarski(X0,k7_relat_1(sK3,X1))
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(X2),X3)
% 31.53/4.51      | X0 != k1_relat_1(X2)
% 31.53/4.51      | k7_relat_1(sK3,X1) != X3 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2238]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_20315,plain,
% 31.53/4.51      ( X0 != k1_relat_1(X1)
% 31.53/4.51      | k7_relat_1(sK3,X2) != X3
% 31.53/4.51      | r1_tarski(X0,k7_relat_1(sK3,X2)) = iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(X1),X3) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_20289]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_20317,plain,
% 31.53/4.51      ( k7_relat_1(sK3,k1_xboole_0) != k1_xboole_0
% 31.53/4.51      | k1_xboole_0 != k1_relat_1(k1_xboole_0)
% 31.53/4.51      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_20315]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_2725,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK3) | r1_tarski(X0,sK3) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_0]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_41545,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK0,X0) | r1_tarski(sK0,sK3) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_2725]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_41554,plain,
% 31.53/4.51      ( r1_tarski(X0,sK3) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,sK3) = iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_41545]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_41556,plain,
% 31.53/4.51      ( r1_tarski(sK0,sK3) = iProver_top
% 31.53/4.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_41554]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_53389,plain,
% 31.53/4.51      ( r1_tarski(sK0,X0) != iProver_top
% 31.53/4.51      | r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(global_propositional_subsumption,
% 31.53/4.51                [status(thm)],
% 31.53/4.51                [c_53383,c_31,c_97,c_107,c_108,c_109,c_1614,c_1627,c_1711,
% 31.53/4.51                 c_1780,c_1898,c_1973,c_2120,c_2222,c_2285,c_2374,c_2382,
% 31.53/4.51                 c_2391,c_2528,c_2572,c_2641,c_2773,c_3016,c_3499,c_3730,
% 31.53/4.51                 c_3787,c_4627,c_5318,c_5719,c_11273,c_17304,c_20317,c_41556]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_53390,plain,
% 31.53/4.51      ( r1_tarski(k2_zfmisc_1(X0,sK1),k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(sK0,X0) != iProver_top ),
% 31.53/4.51      inference(renaming,[status(thm)],[c_53389]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_53395,plain,
% 31.53/4.51      ( r1_tarski(sK0,k1_xboole_0) != iProver_top
% 31.53/4.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_3,c_53390]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_52370,plain,
% 31.53/4.51      ( ~ r1_tarski(k7_relat_1(sK3,sK2),X0)
% 31.53/4.51      | ~ v1_relat_1(X0)
% 31.53/4.51      | v1_relat_1(k7_relat_1(sK3,sK2)) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_314]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_54745,plain,
% 31.53/4.51      ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.53/4.51      | v1_relat_1(k7_relat_1(sK3,sK2))
% 31.53/4.51      | ~ v1_relat_1(sK3) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_52370]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_54746,plain,
% 31.53/4.51      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 31.53/4.51      | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 31.53/4.51      | v1_relat_1(sK3) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_54745]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_52473,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,X1)
% 31.53/4.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 31.53/4.51      | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
% 31.53/4.51      | sK2 != X1 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_861]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_55189,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,sK2)
% 31.53/4.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 31.53/4.51      | k1_relat_1(k7_relat_1(sK3,sK2)) != X0
% 31.53/4.51      | sK2 != sK2 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_52473]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_60450,plain,
% 31.53/4.51      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 31.53/4.51      | ~ r1_tarski(sK2,sK2)
% 31.53/4.51      | k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 31.53/4.51      | sK2 != sK2 ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_55189]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_60451,plain,
% 31.53/4.51      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 31.53/4.51      | sK2 != sK2
% 31.53/4.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 31.53/4.51      | r1_tarski(sK2,sK2) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_60450]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_51813,plain,
% 31.53/4.51      ( ~ r1_tarski(X0,X1)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),X0)
% 31.53/4.51      | r1_tarski(k7_relat_1(sK3,sK2),X1) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_0]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_52923,plain,
% 31.53/4.51      ( r1_tarski(k7_relat_1(sK3,sK2),X0)
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.53/4.51      | ~ r1_tarski(sK3,X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_51813]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_60660,plain,
% 31.53/4.51      ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1))
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 31.53/4.51      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_52923]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_60661,plain,
% 31.53/4.51      ( r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 31.53/4.51      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 31.53/4.51      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_60660]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_51524,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(X0))
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),X0) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_5]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_68114,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.53/4.51      | ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_51524]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_68118,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.53/4.51      | r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_68114]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_51325,plain,
% 31.53/4.51      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 31.53/4.51      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_19]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_84320,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.53/4.51      | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.53/4.51      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
% 31.53/4.51      inference(instantiation,[status(thm)],[c_51325]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_84321,plain,
% 31.53/4.51      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 31.53/4.51      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.53/4.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
% 31.53/4.51      inference(predicate_to_equality,[status(thm)],[c_84320]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_87764,plain,
% 31.53/4.51      ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.53/4.51      inference(global_propositional_subsumption,
% 31.53/4.51                [status(thm)],
% 31.53/4.51                [c_87637,c_35,c_33,c_38,c_31,c_97,c_106,c_107,c_108,c_109,
% 31.53/4.51                 c_538,c_1609,c_1612,c_1614,c_1618,c_1622,c_1627,c_1651,
% 31.53/4.51                 c_1687,c_1710,c_1711,c_1898,c_1973,c_1975,c_2004,c_2022,
% 31.53/4.51                 c_2040,c_2101,c_2120,c_2222,c_2223,c_2368,c_2374,c_2382,
% 31.53/4.51                 c_2391,c_2407,c_2528,c_2529,c_2571,c_2572,c_2613,c_2620,
% 31.53/4.51                 c_2641,c_2773,c_3016,c_3097,c_3499,c_3730,c_4391,c_4627,
% 31.53/4.51                 c_4926,c_5831,c_7600,c_8061,c_11849,c_12116,c_17449,c_21753,
% 31.53/4.51                 c_41655,c_48039,c_49493,c_49896,c_50413,c_50414,c_52719,
% 31.53/4.51                 c_53307,c_54746,c_60451,c_60661,c_68118,c_84321]) ).
% 31.53/4.51  
% 31.53/4.51  cnf(c_87768,plain,
% 31.53/4.51      ( $false ),
% 31.53/4.51      inference(superposition,[status(thm)],[c_3101,c_87764]) ).
% 31.53/4.51  
% 31.53/4.51  
% 31.53/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.53/4.51  
% 31.53/4.51  ------                               Statistics
% 31.53/4.51  
% 31.53/4.51  ------ General
% 31.53/4.51  
% 31.53/4.51  abstr_ref_over_cycles:                  0
% 31.53/4.51  abstr_ref_under_cycles:                 0
% 31.53/4.51  gc_basic_clause_elim:                   0
% 31.53/4.51  forced_gc_time:                         0
% 31.53/4.51  parsing_time:                           0.016
% 31.53/4.51  unif_index_cands_time:                  0.
% 31.53/4.51  unif_index_add_time:                    0.
% 31.53/4.51  orderings_time:                         0.
% 31.53/4.51  out_proof_time:                         0.036
% 31.53/4.51  total_time:                             3.598
% 31.53/4.51  num_of_symbols:                         48
% 31.53/4.51  num_of_terms:                           63149
% 31.53/4.51  
% 31.53/4.51  ------ Preprocessing
% 31.53/4.51  
% 31.53/4.51  num_of_splits:                          0
% 31.53/4.51  num_of_split_atoms:                     0
% 31.53/4.51  num_of_reused_defs:                     0
% 31.53/4.51  num_eq_ax_congr_red:                    11
% 31.53/4.51  num_of_sem_filtered_clauses:            1
% 31.53/4.51  num_of_subtypes:                        0
% 31.53/4.51  monotx_restored_types:                  0
% 31.53/4.51  sat_num_of_epr_types:                   0
% 31.53/4.51  sat_num_of_non_cyclic_types:            0
% 31.53/4.51  sat_guarded_non_collapsed_types:        0
% 31.53/4.51  num_pure_diseq_elim:                    0
% 31.53/4.51  simp_replaced_by:                       0
% 31.53/4.51  res_preprocessed:                       166
% 31.53/4.51  prep_upred:                             0
% 31.53/4.51  prep_unflattend:                        33
% 31.53/4.51  smt_new_axioms:                         0
% 31.53/4.51  pred_elim_cands:                        5
% 31.53/4.51  pred_elim:                              1
% 31.53/4.51  pred_elim_cl:                           1
% 31.53/4.51  pred_elim_cycles:                       3
% 31.53/4.51  merged_defs:                            8
% 31.53/4.51  merged_defs_ncl:                        0
% 31.53/4.51  bin_hyper_res:                          9
% 31.53/4.51  prep_cycles:                            4
% 31.53/4.51  pred_elim_time:                         0.007
% 31.53/4.51  splitting_time:                         0.
% 31.53/4.51  sem_filter_time:                        0.
% 31.53/4.51  monotx_time:                            0.001
% 31.53/4.51  subtype_inf_time:                       0.
% 31.53/4.51  
% 31.53/4.51  ------ Problem properties
% 31.53/4.51  
% 31.53/4.51  clauses:                                35
% 31.53/4.51  conjectures:                            4
% 31.53/4.51  epr:                                    6
% 31.53/4.51  horn:                                   32
% 31.53/4.51  ground:                                 11
% 31.53/4.51  unary:                                  6
% 31.53/4.51  binary:                                 8
% 31.53/4.51  lits:                                   93
% 31.53/4.51  lits_eq:                                28
% 31.53/4.51  fd_pure:                                0
% 31.53/4.51  fd_pseudo:                              0
% 31.53/4.51  fd_cond:                                2
% 31.53/4.51  fd_pseudo_cond:                         0
% 31.53/4.51  ac_symbols:                             0
% 31.53/4.51  
% 31.53/4.51  ------ Propositional Solver
% 31.53/4.51  
% 31.53/4.51  prop_solver_calls:                      48
% 31.53/4.51  prop_fast_solver_calls:                 6087
% 31.53/4.51  smt_solver_calls:                       0
% 31.53/4.51  smt_fast_solver_calls:                  0
% 31.53/4.51  prop_num_of_clauses:                    43021
% 31.53/4.51  prop_preprocess_simplified:             65752
% 31.53/4.51  prop_fo_subsumed:                       693
% 31.53/4.51  prop_solver_time:                       0.
% 31.53/4.51  smt_solver_time:                        0.
% 31.53/4.51  smt_fast_solver_time:                   0.
% 31.53/4.51  prop_fast_solver_time:                  0.
% 31.53/4.51  prop_unsat_core_time:                   0.
% 31.53/4.51  
% 31.53/4.51  ------ QBF
% 31.53/4.51  
% 31.53/4.51  qbf_q_res:                              0
% 31.53/4.51  qbf_num_tautologies:                    0
% 31.53/4.51  qbf_prep_cycles:                        0
% 31.53/4.51  
% 31.53/4.51  ------ BMC1
% 31.53/4.51  
% 31.53/4.51  bmc1_current_bound:                     -1
% 31.53/4.51  bmc1_last_solved_bound:                 -1
% 31.53/4.51  bmc1_unsat_core_size:                   -1
% 31.53/4.51  bmc1_unsat_core_parents_size:           -1
% 31.53/4.51  bmc1_merge_next_fun:                    0
% 31.53/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.53/4.51  
% 31.53/4.51  ------ Instantiation
% 31.53/4.51  
% 31.53/4.51  inst_num_of_clauses:                    7569
% 31.53/4.51  inst_num_in_passive:                    3962
% 31.53/4.51  inst_num_in_active:                     5119
% 31.53/4.51  inst_num_in_unprocessed:                820
% 31.53/4.51  inst_num_of_loops:                      5819
% 31.53/4.51  inst_num_of_learning_restarts:          1
% 31.53/4.51  inst_num_moves_active_passive:          689
% 31.53/4.51  inst_lit_activity:                      0
% 31.53/4.51  inst_lit_activity_moves:                0
% 31.53/4.51  inst_num_tautologies:                   0
% 31.53/4.51  inst_num_prop_implied:                  0
% 31.53/4.51  inst_num_existing_simplified:           0
% 31.53/4.51  inst_num_eq_res_simplified:             0
% 31.53/4.51  inst_num_child_elim:                    0
% 31.53/4.51  inst_num_of_dismatching_blockings:      8101
% 31.53/4.51  inst_num_of_non_proper_insts:           12384
% 31.53/4.51  inst_num_of_duplicates:                 0
% 31.53/4.51  inst_inst_num_from_inst_to_res:         0
% 31.53/4.51  inst_dismatching_checking_time:         0.
% 31.53/4.51  
% 31.53/4.51  ------ Resolution
% 31.53/4.51  
% 31.53/4.51  res_num_of_clauses:                     47
% 31.53/4.51  res_num_in_passive:                     47
% 31.53/4.51  res_num_in_active:                      0
% 31.53/4.51  res_num_of_loops:                       170
% 31.53/4.51  res_forward_subset_subsumed:            270
% 31.53/4.51  res_backward_subset_subsumed:           0
% 31.53/4.51  res_forward_subsumed:                   0
% 31.53/4.51  res_backward_subsumed:                  0
% 31.53/4.51  res_forward_subsumption_resolution:     0
% 31.53/4.51  res_backward_subsumption_resolution:    0
% 31.53/4.51  res_clause_to_clause_subsumption:       35328
% 31.53/4.51  res_orphan_elimination:                 0
% 31.53/4.51  res_tautology_del:                      798
% 31.53/4.51  res_num_eq_res_simplified:              1
% 31.53/4.51  res_num_sel_changes:                    0
% 31.53/4.51  res_moves_from_active_to_pass:          0
% 31.53/4.51  
% 31.53/4.51  ------ Superposition
% 31.53/4.51  
% 31.53/4.51  sup_time_total:                         0.
% 31.53/4.51  sup_time_generating:                    0.
% 31.53/4.51  sup_time_sim_full:                      0.
% 31.53/4.51  sup_time_sim_immed:                     0.
% 31.53/4.51  
% 31.53/4.51  sup_num_of_clauses:                     5722
% 31.53/4.51  sup_num_in_active:                      931
% 31.53/4.51  sup_num_in_passive:                     4791
% 31.53/4.51  sup_num_of_loops:                       1162
% 31.53/4.51  sup_fw_superposition:                   6220
% 31.53/4.51  sup_bw_superposition:                   5379
% 31.53/4.51  sup_immediate_simplified:               3896
% 31.53/4.51  sup_given_eliminated:                   12
% 31.53/4.51  comparisons_done:                       0
% 31.53/4.51  comparisons_avoided:                    42
% 31.53/4.51  
% 31.53/4.51  ------ Simplifications
% 31.53/4.51  
% 31.53/4.51  
% 31.53/4.51  sim_fw_subset_subsumed:                 1192
% 31.53/4.51  sim_bw_subset_subsumed:                 254
% 31.53/4.51  sim_fw_subsumed:                        2036
% 31.53/4.51  sim_bw_subsumed:                        329
% 31.53/4.51  sim_fw_subsumption_res:                 0
% 31.53/4.51  sim_bw_subsumption_res:                 0
% 31.53/4.51  sim_tautology_del:                      119
% 31.53/4.51  sim_eq_tautology_del:                   212
% 31.53/4.51  sim_eq_res_simp:                        0
% 31.53/4.51  sim_fw_demodulated:                     276
% 31.53/4.51  sim_bw_demodulated:                     21
% 31.53/4.51  sim_light_normalised:                   453
% 31.53/4.51  sim_joinable_taut:                      0
% 31.53/4.51  sim_joinable_simp:                      0
% 31.53/4.51  sim_ac_normalised:                      0
% 31.53/4.51  sim_smt_subsumption:                    0
% 31.53/4.51  
%------------------------------------------------------------------------------
