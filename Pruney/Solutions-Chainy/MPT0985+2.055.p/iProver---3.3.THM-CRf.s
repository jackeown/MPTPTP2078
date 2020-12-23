%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:31 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2632)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f59,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f60,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f59])).

fof(f63,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f60,f63])).

fof(f109,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f111,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f64])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f107,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f57])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f51])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f112,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f64])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k2_relat_1(X0) != k1_xboole_0 )
        & ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_xboole_0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f77,f97])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f118,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f81,f97])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f113,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f97])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f123,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f104])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f117,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f82,f97])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f114,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f97])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1954,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1966,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3746,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1966])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1982,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3801,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3746,c_1982])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5794,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_1962])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1965,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4835,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1954,c_1965])).

cnf(c_42,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4841,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4835,c_42])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1981,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3802,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3746,c_1981])).

cnf(c_5031,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4841,c_3802])).

cnf(c_5836,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5794,c_5031])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_47,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_755,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_43])).

cnf(c_756,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2286,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2287,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2286])).

cnf(c_2302,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2303,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2302])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2505,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2526,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2505])).

cnf(c_1334,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3017,plain,
    ( X0 != X1
    | X0 = k2_funct_1(sK2)
    | k2_funct_1(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_3975,plain,
    ( X0 = k2_funct_1(sK2)
    | X0 != k4_relat_1(sK2)
    | k2_funct_1(sK2) != k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3017])).

cnf(c_4746,plain,
    ( k2_funct_1(sK2) != k4_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2)
    | k4_relat_1(sK2) != k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3975])).

cnf(c_1333,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4747,plain,
    ( k4_relat_1(sK2) = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_1343,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2542,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | X0 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_6013,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_1(k4_relat_1(sK2))
    | k4_relat_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2542])).

cnf(c_6017,plain,
    ( k4_relat_1(sK2) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6013])).

cnf(c_6669,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5836,c_46,c_47,c_44,c_49,c_756,c_2287,c_2302,c_2303,c_2526,c_4746,c_4747,c_6017])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1957,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6677,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,X0) = iProver_top
    | v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6669,c_1957])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1961,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5649,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_1961])).

cnf(c_5653,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5649,c_5031])).

cnf(c_13433,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6677,c_46,c_47,c_44,c_49,c_756,c_2287,c_2302,c_2303,c_2526,c_4746,c_4747,c_5653,c_6017])).

cnf(c_13434,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13433])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7950,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6669,c_1964])).

cnf(c_7953,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7950,c_3801])).

cnf(c_1952,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1975,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6801,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_1975])).

cnf(c_7202,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6801,c_46,c_44,c_756,c_2302])).

cnf(c_41,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1956,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_2339,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1956,c_47,c_49,c_51,c_2287,c_2303])).

cnf(c_2340,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2339])).

cnf(c_7207,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7202,c_2340])).

cnf(c_12221,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7953,c_7207])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_1])).

cnf(c_478,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_24])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_478])).

cnf(c_2413,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_2414,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2413])).

cnf(c_12403,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12221,c_49,c_2414])).

cnf(c_13442,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13434,c_12403])).

cnf(c_13530,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13442,c_49,c_2414])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1979,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13685,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13530,c_1979])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1978,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4174,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_1978])).

cnf(c_4178,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4174,c_3802])).

cnf(c_4318,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4178,c_49,c_2303,c_2526])).

cnf(c_4319,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4318])).

cnf(c_5026,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4841,c_4319])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1980,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5053,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4841,c_1980])).

cnf(c_5477,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5053,c_49,c_2303])).

cnf(c_5478,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5477])).

cnf(c_13845,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13685,c_44,c_49,c_2302,c_2414,c_2632,c_2691,c_7007,c_13442])).

cnf(c_13851,plain,
    ( v1_funct_2(k4_relat_1(k1_xboole_0),sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13845,c_12403])).

cnf(c_12,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_17,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1971,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2770,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1971])).

cnf(c_3339,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2770,c_1981])).

cnf(c_9,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2418,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_9])).

cnf(c_3341,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3339,c_2418])).

cnf(c_3757,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_1979])).

cnf(c_139,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_141,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_4064,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3757,c_141,c_2770])).

cnf(c_13933,plain,
    ( v1_funct_2(k1_xboole_0,sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13851,c_4064])).

cnf(c_13563,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13530,c_5026])).

cnf(c_13583,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13563])).

cnf(c_16534,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13933,c_13583])).

cnf(c_1949,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_2452,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1949])).

cnf(c_30,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1963,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7944,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1963,c_1964])).

cnf(c_7986,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7944,c_9])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_funct_2(X0,k1_xboole_0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1958,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8144,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7986,c_1958])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_31,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_453,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_partfun1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_31])).

cnf(c_454,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_partfun1(X0)) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_16,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_458,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_partfun1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_16])).

cnf(c_459,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_1950,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_8148,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7986,c_1950])).

cnf(c_8187,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8144,c_8148])).

cnf(c_8188,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8187,c_12])).

cnf(c_1972,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2910,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1972])).

cnf(c_8349,plain,
    ( r1_tarski(k1_xboole_0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8188,c_2910])).

cnf(c_8350,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8349])).

cnf(c_8356,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_8350])).

cnf(c_13552,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13530,c_8356])).

cnf(c_3034,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1963,c_1949])).

cnf(c_10,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3036,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3034,c_10])).

cnf(c_3042,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3036])).

cnf(c_15108,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13552,c_3042])).

cnf(c_16536,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16534,c_15108])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.67/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.00  
% 3.67/1.00  ------  iProver source info
% 3.67/1.00  
% 3.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.00  git: non_committed_changes: false
% 3.67/1.00  git: last_make_outside_of_git: false
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             all
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         305.
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              default
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           true
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             true
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     num_symb
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       true
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  ------ Parsing...
% 3.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/1.00  ------ Proving...
% 3.67/1.00  ------ Problem Properties 
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  clauses                                 40
% 3.67/1.00  conjectures                             6
% 3.67/1.00  EPR                                     3
% 3.67/1.00  Horn                                    38
% 3.67/1.00  unary                                   12
% 3.67/1.00  binary                                  8
% 3.67/1.00  lits                                    109
% 3.67/1.00  lits eq                                 27
% 3.67/1.00  fd_pure                                 0
% 3.67/1.00  fd_pseudo                               0
% 3.67/1.00  fd_cond                                 4
% 3.67/1.00  fd_pseudo_cond                          1
% 3.67/1.00  AC symbols                              0
% 3.67/1.00  
% 3.67/1.00  ------ Schedule dynamic 5 is on 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  Current options:
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             all
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         305.
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              default
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           true
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             true
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     none
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       false
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ Proving...
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS status Theorem for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00   Resolution empty clause
% 3.67/1.00  
% 3.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  fof(f26,conjecture,(
% 3.67/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f27,negated_conjecture,(
% 3.67/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.67/1.00    inference(negated_conjecture,[],[f26])).
% 3.67/1.00  
% 3.67/1.00  fof(f59,plain,(
% 3.67/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.67/1.00    inference(ennf_transformation,[],[f27])).
% 3.67/1.00  
% 3.67/1.00  fof(f60,plain,(
% 3.67/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.67/1.00    inference(flattening,[],[f59])).
% 3.67/1.00  
% 3.67/1.00  fof(f63,plain,(
% 3.67/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f64,plain,(
% 3.67/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f60,f63])).
% 3.67/1.00  
% 3.67/1.00  fof(f109,plain,(
% 3.67/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.67/1.00    inference(cnf_transformation,[],[f64])).
% 3.67/1.00  
% 3.67/1.00  fof(f17,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f48,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(ennf_transformation,[],[f17])).
% 3.67/1.00  
% 3.67/1.00  fof(f89,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f48])).
% 3.67/1.00  
% 3.67/1.00  fof(f3,axiom,(
% 3.67/1.00    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f31,plain,(
% 3.67/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f3])).
% 3.67/1.00  
% 3.67/1.00  fof(f69,plain,(
% 3.67/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f31])).
% 3.67/1.00  
% 3.67/1.00  fof(f24,axiom,(
% 3.67/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f55,plain,(
% 3.67/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f24])).
% 3.67/1.00  
% 3.67/1.00  fof(f56,plain,(
% 3.67/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(flattening,[],[f55])).
% 3.67/1.00  
% 3.67/1.00  fof(f100,plain,(
% 3.67/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f56])).
% 3.67/1.00  
% 3.67/1.00  fof(f19,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f50,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(ennf_transformation,[],[f19])).
% 3.67/1.00  
% 3.67/1.00  fof(f91,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f50])).
% 3.67/1.00  
% 3.67/1.00  fof(f111,plain,(
% 3.67/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.67/1.00    inference(cnf_transformation,[],[f64])).
% 3.67/1.00  
% 3.67/1.00  fof(f68,plain,(
% 3.67/1.00    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f31])).
% 3.67/1.00  
% 3.67/1.00  fof(f107,plain,(
% 3.67/1.00    v1_funct_1(sK2)),
% 3.67/1.00    inference(cnf_transformation,[],[f64])).
% 3.67/1.00  
% 3.67/1.00  fof(f9,axiom,(
% 3.67/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f36,plain,(
% 3.67/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f9])).
% 3.67/1.00  
% 3.67/1.00  fof(f37,plain,(
% 3.67/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(flattening,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f78,plain,(
% 3.67/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f37])).
% 3.67/1.00  
% 3.67/1.00  fof(f110,plain,(
% 3.67/1.00    v2_funct_1(sK2)),
% 3.67/1.00    inference(cnf_transformation,[],[f64])).
% 3.67/1.00  
% 3.67/1.00  fof(f10,axiom,(
% 3.67/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f38,plain,(
% 3.67/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f10])).
% 3.67/1.00  
% 3.67/1.00  fof(f39,plain,(
% 3.67/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(flattening,[],[f38])).
% 3.67/1.00  
% 3.67/1.00  fof(f80,plain,(
% 3.67/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f39])).
% 3.67/1.00  
% 3.67/1.00  fof(f2,axiom,(
% 3.67/1.00    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f30,plain,(
% 3.67/1.00    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f2])).
% 3.67/1.00  
% 3.67/1.00  fof(f67,plain,(
% 3.67/1.00    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f30])).
% 3.67/1.00  
% 3.67/1.00  fof(f25,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f57,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.67/1.00    inference(ennf_transformation,[],[f25])).
% 3.67/1.00  
% 3.67/1.00  fof(f58,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.67/1.00    inference(flattening,[],[f57])).
% 3.67/1.00  
% 3.67/1.00  fof(f103,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f58])).
% 3.67/1.00  
% 3.67/1.00  fof(f99,plain,(
% 3.67/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f56])).
% 3.67/1.00  
% 3.67/1.00  fof(f20,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f51,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.67/1.00    inference(ennf_transformation,[],[f20])).
% 3.67/1.00  
% 3.67/1.00  fof(f52,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.67/1.00    inference(flattening,[],[f51])).
% 3.67/1.00  
% 3.67/1.00  fof(f92,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f52])).
% 3.67/1.00  
% 3.67/1.00  fof(f112,plain,(
% 3.67/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.67/1.00    inference(cnf_transformation,[],[f64])).
% 3.67/1.00  
% 3.67/1.00  fof(f18,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f28,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.67/1.00    inference(pure_predicate_removal,[],[f18])).
% 3.67/1.00  
% 3.67/1.00  fof(f49,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(ennf_transformation,[],[f28])).
% 3.67/1.00  
% 3.67/1.00  fof(f90,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f49])).
% 3.67/1.00  
% 3.67/1.00  fof(f1,axiom,(
% 3.67/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f29,plain,(
% 3.67/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.67/1.00    inference(ennf_transformation,[],[f1])).
% 3.67/1.00  
% 3.67/1.00  fof(f61,plain,(
% 3.67/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.67/1.00    inference(nnf_transformation,[],[f29])).
% 3.67/1.00  
% 3.67/1.00  fof(f65,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f61])).
% 3.67/1.00  
% 3.67/1.00  fof(f4,axiom,(
% 3.67/1.00    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f32,plain,(
% 3.67/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f4])).
% 3.67/1.00  
% 3.67/1.00  fof(f33,plain,(
% 3.67/1.00    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(flattening,[],[f32])).
% 3.67/1.00  
% 3.67/1.00  fof(f70,plain,(
% 3.67/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f33])).
% 3.67/1.00  
% 3.67/1.00  fof(f5,axiom,(
% 3.67/1.00    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f34,plain,(
% 3.67/1.00    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(ennf_transformation,[],[f5])).
% 3.67/1.00  
% 3.67/1.00  fof(f62,plain,(
% 3.67/1.00    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0) & (k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.67/1.00    inference(nnf_transformation,[],[f34])).
% 3.67/1.00  
% 3.67/1.00  fof(f73,plain,(
% 3.67/1.00    ( ! [X0] : (k1_relat_1(X0) = k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f62])).
% 3.67/1.00  
% 3.67/1.00  fof(f71,plain,(
% 3.67/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f33])).
% 3.67/1.00  
% 3.67/1.00  fof(f8,axiom,(
% 3.67/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f77,plain,(
% 3.67/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.67/1.00    inference(cnf_transformation,[],[f8])).
% 3.67/1.00  
% 3.67/1.00  fof(f23,axiom,(
% 3.67/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f97,plain,(
% 3.67/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f23])).
% 3.67/1.00  
% 3.67/1.00  fof(f116,plain,(
% 3.67/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.67/1.00    inference(definition_unfolding,[],[f77,f97])).
% 3.67/1.00  
% 3.67/1.00  fof(f11,axiom,(
% 3.67/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f81,plain,(
% 3.67/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f11])).
% 3.67/1.00  
% 3.67/1.00  fof(f118,plain,(
% 3.67/1.00    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.67/1.00    inference(definition_unfolding,[],[f81,f97])).
% 3.67/1.00  
% 3.67/1.00  fof(f6,axiom,(
% 3.67/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f75,plain,(
% 3.67/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.67/1.00    inference(cnf_transformation,[],[f6])).
% 3.67/1.00  
% 3.67/1.00  fof(f113,plain,(
% 3.67/1.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.67/1.00    inference(definition_unfolding,[],[f75,f97])).
% 3.67/1.00  
% 3.67/1.00  fof(f22,axiom,(
% 3.67/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f96,plain,(
% 3.67/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f22])).
% 3.67/1.00  
% 3.67/1.00  fof(f104,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f58])).
% 3.67/1.00  
% 3.67/1.00  fof(f123,plain,(
% 3.67/1.00    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 3.67/1.00    inference(equality_resolution,[],[f104])).
% 3.67/1.00  
% 3.67/1.00  fof(f21,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f53,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(ennf_transformation,[],[f21])).
% 3.67/1.00  
% 3.67/1.00  fof(f54,plain,(
% 3.67/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.67/1.00    inference(flattening,[],[f53])).
% 3.67/1.00  
% 3.67/1.00  fof(f94,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f54])).
% 3.67/1.00  
% 3.67/1.00  fof(f95,plain,(
% 3.67/1.00    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f22])).
% 3.67/1.00  
% 3.67/1.00  fof(f82,plain,(
% 3.67/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f11])).
% 3.67/1.00  
% 3.67/1.00  fof(f117,plain,(
% 3.67/1.00    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 3.67/1.00    inference(definition_unfolding,[],[f82,f97])).
% 3.67/1.00  
% 3.67/1.00  fof(f74,plain,(
% 3.67/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.67/1.00    inference(cnf_transformation,[],[f6])).
% 3.67/1.00  
% 3.67/1.00  fof(f114,plain,(
% 3.67/1.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.67/1.00    inference(definition_unfolding,[],[f74,f97])).
% 3.67/1.00  
% 3.67/1.00  cnf(c_44,negated_conjecture,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1954,plain,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_24,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1966,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3746,plain,
% 3.67/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1954,c_1966]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3,plain,
% 3.67/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1982,plain,
% 3.67/1.00      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3801,plain,
% 3.67/1.00      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_3746,c_1982]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_32,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.67/1.00      | ~ v1_funct_1(X0)
% 3.67/1.00      | ~ v1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1962,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5794,plain,
% 3.67/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.67/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.67/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_3801,c_1962]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_26,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1965,plain,
% 3.67/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.67/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4835,plain,
% 3.67/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1954,c_1965]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_42,negated_conjecture,
% 3.67/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.67/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4841,plain,
% 3.67/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_4835,c_42]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4,plain,
% 3.67/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1981,plain,
% 3.67/1.00      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3802,plain,
% 3.67/1.00      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_3746,c_1981]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5031,plain,
% 3.67/1.00      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_4841,c_3802]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5836,plain,
% 3.67/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.67/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.67/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_5794,c_5031]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_46,negated_conjecture,
% 3.67/1.00      ( v1_funct_1(sK2) ),
% 3.67/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_47,plain,
% 3.67/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_49,plain,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13,plain,
% 3.67/1.00      ( ~ v1_funct_1(X0)
% 3.67/1.00      | ~ v2_funct_1(X0)
% 3.67/1.00      | ~ v1_relat_1(X0)
% 3.67/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_43,negated_conjecture,
% 3.67/1.00      ( v2_funct_1(sK2) ),
% 3.67/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_755,plain,
% 3.67/1.00      ( ~ v1_funct_1(X0)
% 3.67/1.00      | ~ v1_relat_1(X0)
% 3.67/1.00      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.67/1.00      | sK2 != X0 ),
% 3.67/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_43]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_756,plain,
% 3.67/1.00      ( ~ v1_funct_1(sK2)
% 3.67/1.00      | ~ v1_relat_1(sK2)
% 3.67/1.00      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.67/1.00      inference(unflattening,[status(thm)],[c_755]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14,plain,
% 3.67/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2286,plain,
% 3.67/1.00      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2287,plain,
% 3.67/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.67/1.00      | v1_funct_1(sK2) != iProver_top
% 3.67/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2286]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2302,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.67/1.00      | v1_relat_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2303,plain,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.67/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2302]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2,plain,
% 3.67/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2505,plain,
% 3.67/1.00      ( v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2526,plain,
% 3.67/1.00      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 3.67/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2505]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1334,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3017,plain,
% 3.67/1.00      ( X0 != X1 | X0 = k2_funct_1(sK2) | k2_funct_1(sK2) != X1 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1334]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3975,plain,
% 3.67/1.00      ( X0 = k2_funct_1(sK2)
% 3.67/1.00      | X0 != k4_relat_1(sK2)
% 3.67/1.00      | k2_funct_1(sK2) != k4_relat_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_3017]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4746,plain,
% 3.67/1.00      ( k2_funct_1(sK2) != k4_relat_1(sK2)
% 3.67/1.00      | k4_relat_1(sK2) = k2_funct_1(sK2)
% 3.67/1.00      | k4_relat_1(sK2) != k4_relat_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_3975]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1333,plain,( X0 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4747,plain,
% 3.67/1.00      ( k4_relat_1(sK2) = k4_relat_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1333]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1343,plain,
% 3.67/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.67/1.00      theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2542,plain,
% 3.67/1.00      ( v1_funct_1(X0)
% 3.67/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.67/1.00      | X0 != k2_funct_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_1343]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6013,plain,
% 3.67/1.00      ( ~ v1_funct_1(k2_funct_1(sK2))
% 3.67/1.00      | v1_funct_1(k4_relat_1(sK2))
% 3.67/1.00      | k4_relat_1(sK2) != k2_funct_1(sK2) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_2542]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6017,plain,
% 3.67/1.00      ( k4_relat_1(sK2) != k2_funct_1(sK2)
% 3.67/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.67/1.00      | v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_6013]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6669,plain,
% 3.67/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_5836,c_46,c_47,c_44,c_49,c_756,c_2287,c_2302,c_2303,
% 3.67/1.00                 c_2526,c_4746,c_4747,c_6017]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_38,plain,
% 3.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.67/1.00      | v1_funct_2(X0,X1,X3)
% 3.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | ~ r1_tarski(X2,X3)
% 3.67/1.00      | ~ v1_funct_1(X0)
% 3.67/1.00      | k1_xboole_0 = X2 ),
% 3.67/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1957,plain,
% 3.67/1.00      ( k1_xboole_0 = X0
% 3.67/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.67/1.00      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.67/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.67/1.00      | r1_tarski(X0,X3) != iProver_top
% 3.67/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6677,plain,
% 3.67/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.67/1.00      | v1_funct_2(k4_relat_1(sK2),sK1,X0) = iProver_top
% 3.67/1.00      | v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
% 3.67/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 3.67/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_6669,c_1957]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_33,plain,
% 3.67/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.67/1.00      | ~ v1_funct_1(X0)
% 3.67/1.00      | ~ v1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1961,plain,
% 3.67/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5649,plain,
% 3.67/1.00      ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) = iProver_top
% 3.67/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.67/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_3801,c_1961]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5653,plain,
% 3.67/1.00      ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) = iProver_top
% 3.67/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.67/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_5649,c_5031]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13433,plain,
% 3.67/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 3.67/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 3.67/1.00      | v1_funct_2(k4_relat_1(sK2),sK1,X0) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_6677,c_46,c_47,c_44,c_49,c_756,c_2287,c_2302,c_2303,
% 3.67/1.00                 c_2526,c_4746,c_4747,c_5653,c_6017]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13434,plain,
% 3.67/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.67/1.00      | v1_funct_2(k4_relat_1(sK2),sK1,X0) = iProver_top
% 3.67/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_13433]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_27,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.67/1.00      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.67/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1964,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.67/1.00      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7950,plain,
% 3.67/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.67/1.00      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_6669,c_1964]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7953,plain,
% 3.67/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.67/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_7950,c_3801]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1952,plain,
% 3.67/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1975,plain,
% 3.67/1.00      ( k2_funct_1(X0) = k4_relat_1(X0)
% 3.67/1.00      | v1_funct_1(X0) != iProver_top
% 3.67/1.00      | v2_funct_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6801,plain,
% 3.67/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 3.67/1.00      | v2_funct_1(sK2) != iProver_top
% 3.67/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1952,c_1975]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7202,plain,
% 3.67/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_6801,c_46,c_44,c_756,c_2302]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_41,negated_conjecture,
% 3.67/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.67/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.67/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1956,plain,
% 3.67/1.00      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 3.67/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.67/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_51,plain,
% 3.67/1.00      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 3.67/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.67/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2339,plain,
% 3.67/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.67/1.00      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_1956,c_47,c_49,c_51,c_2287,c_2303]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2340,plain,
% 3.67/1.00      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 3.67/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_2339]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7207,plain,
% 3.67/1.00      ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top
% 3.67/1.00      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_7202,c_2340]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12221,plain,
% 3.67/1.00      ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top
% 3.67/1.00      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_7953,c_7207]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_25,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1,plain,
% 3.67/1.00      ( r1_tarski(k1_relat_1(X0),X1) | ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_474,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.67/1.00      | ~ v1_relat_1(X0) ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_25,c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_478,plain,
% 3.67/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.67/1.00      inference(global_propositional_subsumption,[status(thm)],[c_474,c_24]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_479,plain,
% 3.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_478]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2413,plain,
% 3.67/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.67/1.00      | r1_tarski(k1_relat_1(sK2),sK0) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_479]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2414,plain,
% 3.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.67/1.00      | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2413]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12403,plain,
% 3.67/1.00      ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_12221,c_49,c_2414]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13442,plain,
% 3.67/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.67/1.00      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_13434,c_12403]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13530,plain,
% 3.67/1.00      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_13442,c_49,c_2414]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6,plain,
% 3.67/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1979,plain,
% 3.67/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.67/1.00      | k1_xboole_0 = X0
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13685,plain,
% 3.67/1.00      ( sK2 = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_13530,c_1979]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7,plain,
% 3.67/1.00      ( ~ v1_relat_1(X0)
% 3.67/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.67/1.00      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1978,plain,
% 3.67/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.67/1.00      | k1_relat_1(X0) = k1_xboole_0
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4174,plain,
% 3.67/1.00      ( k1_relat_1(k4_relat_1(sK2)) = k1_xboole_0
% 3.67/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 3.67/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_3801,c_1978]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4178,plain,
% 3.67/1.00      ( k2_relat_1(sK2) = k1_xboole_0
% 3.67/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 3.67/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_4174,c_3802]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4318,plain,
% 3.67/1.00      ( k1_relat_1(sK2) != k1_xboole_0 | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_4178,c_49,c_2303,c_2526]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4319,plain,
% 3.67/1.00      ( k2_relat_1(sK2) = k1_xboole_0 | k1_relat_1(sK2) != k1_xboole_0 ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_4318]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5026,plain,
% 3.67/1.00      ( k1_relat_1(sK2) != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_4841,c_4319]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5,plain,
% 3.67/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1980,plain,
% 3.67/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.67/1.00      | k1_xboole_0 = X0
% 3.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5053,plain,
% 3.67/1.00      ( sK1 != k1_xboole_0
% 3.67/1.00      | sK2 = k1_xboole_0
% 3.67/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_4841,c_1980]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5477,plain,
% 3.67/1.00      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_5053,c_49,c_2303]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5478,plain,
% 3.67/1.00      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_5477]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13845,plain,
% 3.67/1.00      ( sK2 = k1_xboole_0 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_13685,c_44,c_49,c_2302,c_2414,c_2632,c_2691,c_7007,c_13442]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13851,plain,
% 3.67/1.00      ( v1_funct_2(k4_relat_1(k1_xboole_0),sK1,sK0) != iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_13845,c_12403]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12,plain,
% 3.67/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17,plain,
% 3.67/1.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1971,plain,
% 3.67/1.00      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2770,plain,
% 3.67/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_12,c_1971]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3339,plain,
% 3.67/1.00      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2770,c_1981]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_9,plain,
% 3.67/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2418,plain,
% 3.67/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_12,c_9]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3341,plain,
% 3.67/1.00      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_3339,c_2418]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3757,plain,
% 3.67/1.00      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
% 3.67/1.00      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_3341,c_1979]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_139,plain,
% 3.67/1.00      ( v1_relat_1(X0) != iProver_top
% 3.67/1.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_141,plain,
% 3.67/1.00      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 3.67/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_139]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4064,plain,
% 3.67/1.00      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_3757,c_141,c_2770]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13933,plain,
% 3.67/1.00      ( v1_funct_2(k1_xboole_0,sK1,sK0) != iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_13851,c_4064]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13563,plain,
% 3.67/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_13530,c_5026]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13583,plain,
% 3.67/1.00      ( sK1 = k1_xboole_0 ),
% 3.67/1.00      inference(equality_resolution_simp,[status(thm)],[c_13563]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_16534,plain,
% 3.67/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) != iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_13933,c_13583]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1949,plain,
% 3.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.67/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2452,plain,
% 3.67/1.00      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1954,c_1949]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_30,plain,
% 3.67/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1963,plain,
% 3.67/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7944,plain,
% 3.67/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.67/1.00      | r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1963,c_1964]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7986,plain,
% 3.67/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.67/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_7944,c_9]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_37,plain,
% 3.67/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.67/1.00      | v1_funct_2(X0,k1_xboole_0,X2)
% 3.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.67/1.00      | ~ r1_tarski(X1,X2)
% 3.67/1.00      | ~ v1_funct_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f123]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1958,plain,
% 3.67/1.00      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 3.67/1.00      | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
% 3.67/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 3.67/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.67/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8144,plain,
% 3.67/1.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) != iProver_top
% 3.67/1.00      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X1) = iProver_top
% 3.67/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.67/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.67/1.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_7986,c_1958]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_28,plain,
% 3.67/1.00      ( v1_funct_2(X0,X1,X2)
% 3.67/1.00      | ~ v1_partfun1(X0,X1)
% 3.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | ~ v1_funct_1(X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_31,plain,
% 3.67/1.00      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_453,plain,
% 3.67/1.00      ( v1_funct_2(X0,X1,X2)
% 3.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.67/1.00      | ~ v1_funct_1(X0)
% 3.67/1.00      | X3 != X1
% 3.67/1.00      | k6_partfun1(X3) != X0 ),
% 3.67/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_31]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_454,plain,
% 3.67/1.00      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 3.67/1.00      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/1.00      | ~ v1_funct_1(k6_partfun1(X0)) ),
% 3.67/1.00      inference(unflattening,[status(thm)],[c_453]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_16,plain,
% 3.67/1.00      ( v1_funct_1(k6_partfun1(X0)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_458,plain,
% 3.67/1.00      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.67/1.00      | v1_funct_2(k6_partfun1(X0),X0,X1) ),
% 3.67/1.00      inference(global_propositional_subsumption,[status(thm)],[c_454,c_16]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_459,plain,
% 3.67/1.00      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 3.67/1.00      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_458]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1950,plain,
% 3.67/1.00      ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
% 3.67/1.00      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8148,plain,
% 3.67/1.00      ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
% 3.67/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_7986,c_1950]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8187,plain,
% 3.67/1.00      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
% 3.67/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.67/1.00      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.67/1.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.67/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_8144,c_8148]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8188,plain,
% 3.67/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 3.67/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.67/1.00      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.67/1.00      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_8187,c_12]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1972,plain,
% 3.67/1.00      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2910,plain,
% 3.67/1.00      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_12,c_1972]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8349,plain,
% 3.67/1.00      ( r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.67/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.67/1.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8188,c_2910]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8350,plain,
% 3.67/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 3.67/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.67/1.00      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_8349]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8356,plain,
% 3.67/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) = iProver_top
% 3.67/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2452,c_8350]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13552,plain,
% 3.67/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) = iProver_top
% 3.67/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_13530,c_8356]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3034,plain,
% 3.67/1.00      ( r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_1963,c_1949]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_10,plain,
% 3.67/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3036,plain,
% 3.67/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_3034,c_10]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3042,plain,
% 3.67/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_3036]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_15108,plain,
% 3.67/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_13552,c_3042]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_16536,plain,
% 3.67/1.00      ( $false ),
% 3.67/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_16534,c_15108]) ).
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  ------                               Statistics
% 3.67/1.00  
% 3.67/1.00  ------ General
% 3.67/1.00  
% 3.67/1.00  abstr_ref_over_cycles:                  0
% 3.67/1.00  abstr_ref_under_cycles:                 0
% 3.67/1.00  gc_basic_clause_elim:                   0
% 3.67/1.00  forced_gc_time:                         0
% 3.67/1.00  parsing_time:                           0.031
% 3.67/1.00  unif_index_cands_time:                  0.
% 3.67/1.00  unif_index_add_time:                    0.
% 3.67/1.00  orderings_time:                         0.
% 3.67/1.00  out_proof_time:                         0.014
% 3.67/1.00  total_time:                             0.449
% 3.67/1.00  num_of_symbols:                         52
% 3.67/1.00  num_of_terms:                           13487
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing
% 3.67/1.00  
% 3.67/1.00  num_of_splits:                          0
% 3.67/1.00  num_of_split_atoms:                     0
% 3.67/1.00  num_of_reused_defs:                     0
% 3.67/1.00  num_eq_ax_congr_red:                    12
% 3.67/1.00  num_of_sem_filtered_clauses:            1
% 3.67/1.00  num_of_subtypes:                        0
% 3.67/1.00  monotx_restored_types:                  0
% 3.67/1.00  sat_num_of_epr_types:                   0
% 3.67/1.00  sat_num_of_non_cyclic_types:            0
% 3.67/1.00  sat_guarded_non_collapsed_types:        0
% 3.67/1.00  num_pure_diseq_elim:                    0
% 3.67/1.00  simp_replaced_by:                       0
% 3.67/1.00  res_preprocessed:                       196
% 3.67/1.00  prep_upred:                             0
% 3.67/1.00  prep_unflattend:                        28
% 3.67/1.00  smt_new_axioms:                         0
% 3.67/1.00  pred_elim_cands:                        6
% 3.67/1.00  pred_elim:                              2
% 3.67/1.00  pred_elim_cl:                           3
% 3.67/1.00  pred_elim_cycles:                       6
% 3.67/1.00  merged_defs:                            0
% 3.67/1.00  merged_defs_ncl:                        0
% 3.67/1.00  bin_hyper_res:                          0
% 3.67/1.00  prep_cycles:                            4
% 3.67/1.00  pred_elim_time:                         0.02
% 3.67/1.00  splitting_time:                         0.
% 3.67/1.00  sem_filter_time:                        0.
% 3.67/1.00  monotx_time:                            0.001
% 3.67/1.00  subtype_inf_time:                       0.
% 3.67/1.00  
% 3.67/1.00  ------ Problem properties
% 3.67/1.00  
% 3.67/1.00  clauses:                                40
% 3.67/1.00  conjectures:                            6
% 3.67/1.00  epr:                                    3
% 3.67/1.00  horn:                                   38
% 3.67/1.00  ground:                                 7
% 3.67/1.00  unary:                                  12
% 3.67/1.00  binary:                                 8
% 3.67/1.00  lits:                                   109
% 3.67/1.00  lits_eq:                                27
% 3.67/1.00  fd_pure:                                0
% 3.67/1.00  fd_pseudo:                              0
% 3.67/1.00  fd_cond:                                4
% 3.67/1.00  fd_pseudo_cond:                         1
% 3.67/1.00  ac_symbols:                             0
% 3.67/1.00  
% 3.67/1.00  ------ Propositional Solver
% 3.67/1.00  
% 3.67/1.00  prop_solver_calls:                      28
% 3.67/1.00  prop_fast_solver_calls:                 1935
% 3.67/1.00  smt_solver_calls:                       0
% 3.67/1.00  smt_fast_solver_calls:                  0
% 3.67/1.00  prop_num_of_clauses:                    5869
% 3.67/1.00  prop_preprocess_simplified:             13703
% 3.67/1.00  prop_fo_subsumed:                       137
% 3.67/1.00  prop_solver_time:                       0.
% 3.67/1.00  smt_solver_time:                        0.
% 3.67/1.00  smt_fast_solver_time:                   0.
% 3.67/1.00  prop_fast_solver_time:                  0.
% 3.67/1.00  prop_unsat_core_time:                   0.
% 3.67/1.00  
% 3.67/1.00  ------ QBF
% 3.67/1.00  
% 3.67/1.00  qbf_q_res:                              0
% 3.67/1.00  qbf_num_tautologies:                    0
% 3.67/1.00  qbf_prep_cycles:                        0
% 3.67/1.00  
% 3.67/1.00  ------ BMC1
% 3.67/1.00  
% 3.67/1.00  bmc1_current_bound:                     -1
% 3.67/1.00  bmc1_last_solved_bound:                 -1
% 3.67/1.00  bmc1_unsat_core_size:                   -1
% 3.67/1.00  bmc1_unsat_core_parents_size:           -1
% 3.67/1.00  bmc1_merge_next_fun:                    0
% 3.67/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation
% 3.67/1.00  
% 3.67/1.00  inst_num_of_clauses:                    2006
% 3.67/1.00  inst_num_in_passive:                    162
% 3.67/1.00  inst_num_in_active:                     887
% 3.67/1.00  inst_num_in_unprocessed:                966
% 3.67/1.00  inst_num_of_loops:                      940
% 3.67/1.00  inst_num_of_learning_restarts:          0
% 3.67/1.00  inst_num_moves_active_passive:          51
% 3.67/1.00  inst_lit_activity:                      0
% 3.67/1.00  inst_lit_activity_moves:                0
% 3.67/1.00  inst_num_tautologies:                   0
% 3.67/1.00  inst_num_prop_implied:                  0
% 3.67/1.00  inst_num_existing_simplified:           0
% 3.67/1.00  inst_num_eq_res_simplified:             0
% 3.67/1.00  inst_num_child_elim:                    0
% 3.67/1.00  inst_num_of_dismatching_blockings:      460
% 3.67/1.00  inst_num_of_non_proper_insts:           1765
% 3.67/1.00  inst_num_of_duplicates:                 0
% 3.67/1.00  inst_inst_num_from_inst_to_res:         0
% 3.67/1.00  inst_dismatching_checking_time:         0.
% 3.67/1.00  
% 3.67/1.00  ------ Resolution
% 3.67/1.00  
% 3.67/1.00  res_num_of_clauses:                     0
% 3.67/1.00  res_num_in_passive:                     0
% 3.67/1.00  res_num_in_active:                      0
% 3.67/1.00  res_num_of_loops:                       200
% 3.67/1.00  res_forward_subset_subsumed:            47
% 3.67/1.00  res_backward_subset_subsumed:           20
% 3.67/1.00  res_forward_subsumed:                   0
% 3.67/1.00  res_backward_subsumed:                  0
% 3.67/1.00  res_forward_subsumption_resolution:     0
% 3.67/1.00  res_backward_subsumption_resolution:    0
% 3.67/1.00  res_clause_to_clause_subsumption:       1074
% 3.67/1.00  res_orphan_elimination:                 0
% 3.67/1.00  res_tautology_del:                      122
% 3.67/1.00  res_num_eq_res_simplified:              0
% 3.67/1.00  res_num_sel_changes:                    0
% 3.67/1.00  res_moves_from_active_to_pass:          0
% 3.67/1.00  
% 3.67/1.00  ------ Superposition
% 3.67/1.00  
% 3.67/1.00  sup_time_total:                         0.
% 3.67/1.00  sup_time_generating:                    0.
% 3.67/1.00  sup_time_sim_full:                      0.
% 3.67/1.00  sup_time_sim_immed:                     0.
% 3.67/1.00  
% 3.67/1.00  sup_num_of_clauses:                     182
% 3.67/1.00  sup_num_in_active:                      97
% 3.67/1.00  sup_num_in_passive:                     85
% 3.67/1.00  sup_num_of_loops:                       187
% 3.67/1.00  sup_fw_superposition:                   221
% 3.67/1.00  sup_bw_superposition:                   197
% 3.67/1.00  sup_immediate_simplified:               281
% 3.67/1.00  sup_given_eliminated:                   0
% 3.67/1.00  comparisons_done:                       0
% 3.67/1.00  comparisons_avoided:                    0
% 3.67/1.00  
% 3.67/1.00  ------ Simplifications
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  sim_fw_subset_subsumed:                 53
% 3.67/1.00  sim_bw_subset_subsumed:                 12
% 3.67/1.00  sim_fw_subsumed:                        48
% 3.67/1.00  sim_bw_subsumed:                        6
% 3.67/1.00  sim_fw_subsumption_res:                 8
% 3.67/1.00  sim_bw_subsumption_res:                 0
% 3.67/1.00  sim_tautology_del:                      10
% 3.67/1.00  sim_eq_tautology_del:                   63
% 3.67/1.00  sim_eq_res_simp:                        10
% 3.67/1.00  sim_fw_demodulated:                     18
% 3.67/1.00  sim_bw_demodulated:                     82
% 3.67/1.00  sim_light_normalised:                   202
% 3.67/1.00  sim_joinable_taut:                      0
% 3.67/1.00  sim_joinable_simp:                      0
% 3.67/1.00  sim_ac_normalised:                      0
% 3.67/1.00  sim_smt_subsumption:                    0
% 3.67/1.00  
%------------------------------------------------------------------------------
