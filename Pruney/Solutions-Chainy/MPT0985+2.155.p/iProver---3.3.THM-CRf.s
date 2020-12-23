%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:52 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_101)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f38,plain,
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

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f38])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1680,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1689,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2169,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1680,c_1689])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_236,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_237,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_294,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_237])).

cnf(c_1678,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_5204,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_1678])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1883,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2083,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_2084,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2083])).

cnf(c_1866,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_2172,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_2173,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2267,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2268,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2267])).

cnf(c_5304,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5204,c_34,c_2084,c_2173,c_2268])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_434,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_435,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_437,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_31])).

cnf(c_1675,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_5308,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5304,c_1675])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1683,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2431,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1680,c_1683])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2432,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2431,c_27])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_420,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_421,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_423,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_31])).

cnf(c_1676,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_2512,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2432,c_1676])).

cnf(c_2617,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2512,c_34,c_2084,c_2173,c_2268])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3643,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2617,c_1681])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1751,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1752,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1751])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2030,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2031,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2030])).

cnf(c_4037,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3643,c_32,c_34,c_1752,c_2031,c_2084,c_2173,c_2268])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_648,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_649,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_1666,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_2619,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2617,c_1666])).

cnf(c_2810,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2619])).

cnf(c_650,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_2812,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2810,c_32,c_34,c_650,c_1752,c_2031,c_2084,c_2173,c_2268,c_2512])).

cnf(c_4047,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4037,c_2812])).

cnf(c_5314,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5308,c_4047])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_509,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_493,c_23])).

cnf(c_1673,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_5339,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k2_funct_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5308,c_1673])).

cnf(c_5342,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5339,c_2617])).

cnf(c_1005,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1902,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2422,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_638,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_640,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_29])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1684,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2518,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1680,c_1684])).

cnf(c_2614,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_640,c_2518])).

cnf(c_4058,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4047])).

cnf(c_1007,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1925,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK0)
    | X2 != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_2107,plain,
    ( ~ r1_tarski(X0,sK0)
    | r1_tarski(X1,sK0)
    | X1 != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_3733,plain,
    ( ~ r1_tarski(X0,sK0)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | k2_relat_1(k2_funct_1(sK2)) != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_4605,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3733])).

cnf(c_2527,plain,
    ( r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,sK0)
    | X0 != sK0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_5007,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ r1_tarski(sK0,sK0)
    | k1_relat_1(sK2) != sK0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_5541,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5342,c_31,c_29,c_435,c_1902,c_2083,c_2172,c_2267,c_2422,c_2614,c_4058,c_4605,c_5007])).

cnf(c_3503,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_1673])).

cnf(c_3768,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3503,c_32,c_34,c_2084,c_2173,c_2268])).

cnf(c_5550,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5541,c_3768])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_100,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_105,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1775,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1777,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_2831,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3770,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3768])).

cnf(c_2532,plain,
    ( r1_tarski(X0,sK0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | X0 != k1_xboole_0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_5004,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | k1_relat_1(sK2) != k1_xboole_0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_6487,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5550,c_31,c_29,c_100,c_101,c_105,c_435,c_1778,c_1902,c_2083,c_2172,c_2267,c_2422,c_2614,c_2831,c_3768,c_4058,c_4605,c_5007,c_5004])).

cnf(c_1692,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_399,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_400,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_404,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_31])).

cnf(c_1677,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_6502,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6487,c_1677])).

cnf(c_89,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2160,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_2161,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2160])).

cnf(c_2239,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2240,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_7228,plain,
    ( r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6502,c_89,c_2161,c_2240])).

cnf(c_7229,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7228])).

cnf(c_1691,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1682,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3070,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_1682])).

cnf(c_5925,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1691,c_3070])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5928,plain,
    ( m1_subset_1(k9_relat_1(k1_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5925,c_1685])).

cnf(c_6136,plain,
    ( m1_subset_1(k9_relat_1(k1_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_5928])).

cnf(c_6952,plain,
    ( m1_subset_1(k9_relat_1(k1_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_6136])).

cnf(c_6957,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6952,c_1689])).

cnf(c_1693,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2997,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1693])).

cnf(c_7071,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6957,c_2997])).

cnf(c_7232,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7229,c_7071])).

cnf(c_7236,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1692,c_7232])).

cnf(c_7237,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1691,c_7232])).

cnf(c_7257,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7236,c_7237])).

cnf(c_7432,plain,
    ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5314,c_6487,c_7257])).

cnf(c_2832,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7432,c_2832])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.76/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/1.00  
% 3.76/1.00  ------  iProver source info
% 3.76/1.00  
% 3.76/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.76/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/1.00  git: non_committed_changes: false
% 3.76/1.00  git: last_make_outside_of_git: false
% 3.76/1.00  
% 3.76/1.00  ------ 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options
% 3.76/1.00  
% 3.76/1.00  --out_options                           all
% 3.76/1.00  --tptp_safe_out                         true
% 3.76/1.00  --problem_path                          ""
% 3.76/1.00  --include_path                          ""
% 3.76/1.00  --clausifier                            res/vclausify_rel
% 3.76/1.00  --clausifier_options                    ""
% 3.76/1.00  --stdin                                 false
% 3.76/1.00  --stats_out                             all
% 3.76/1.00  
% 3.76/1.00  ------ General Options
% 3.76/1.00  
% 3.76/1.00  --fof                                   false
% 3.76/1.00  --time_out_real                         305.
% 3.76/1.00  --time_out_virtual                      -1.
% 3.76/1.00  --symbol_type_check                     false
% 3.76/1.00  --clausify_out                          false
% 3.76/1.00  --sig_cnt_out                           false
% 3.76/1.00  --trig_cnt_out                          false
% 3.76/1.00  --trig_cnt_out_tolerance                1.
% 3.76/1.00  --trig_cnt_out_sk_spl                   false
% 3.76/1.00  --abstr_cl_out                          false
% 3.76/1.00  
% 3.76/1.00  ------ Global Options
% 3.76/1.00  
% 3.76/1.00  --schedule                              default
% 3.76/1.00  --add_important_lit                     false
% 3.76/1.00  --prop_solver_per_cl                    1000
% 3.76/1.00  --min_unsat_core                        false
% 3.76/1.00  --soft_assumptions                      false
% 3.76/1.00  --soft_lemma_size                       3
% 3.76/1.00  --prop_impl_unit_size                   0
% 3.76/1.00  --prop_impl_unit                        []
% 3.76/1.00  --share_sel_clauses                     true
% 3.76/1.00  --reset_solvers                         false
% 3.76/1.00  --bc_imp_inh                            [conj_cone]
% 3.76/1.00  --conj_cone_tolerance                   3.
% 3.76/1.00  --extra_neg_conj                        none
% 3.76/1.00  --large_theory_mode                     true
% 3.76/1.00  --prolific_symb_bound                   200
% 3.76/1.00  --lt_threshold                          2000
% 3.76/1.00  --clause_weak_htbl                      true
% 3.76/1.00  --gc_record_bc_elim                     false
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing Options
% 3.76/1.00  
% 3.76/1.00  --preprocessing_flag                    true
% 3.76/1.00  --time_out_prep_mult                    0.1
% 3.76/1.00  --splitting_mode                        input
% 3.76/1.00  --splitting_grd                         true
% 3.76/1.00  --splitting_cvd                         false
% 3.76/1.00  --splitting_cvd_svl                     false
% 3.76/1.00  --splitting_nvd                         32
% 3.76/1.00  --sub_typing                            true
% 3.76/1.00  --prep_gs_sim                           true
% 3.76/1.00  --prep_unflatten                        true
% 3.76/1.00  --prep_res_sim                          true
% 3.76/1.00  --prep_upred                            true
% 3.76/1.00  --prep_sem_filter                       exhaustive
% 3.76/1.00  --prep_sem_filter_out                   false
% 3.76/1.00  --pred_elim                             true
% 3.76/1.00  --res_sim_input                         true
% 3.76/1.00  --eq_ax_congr_red                       true
% 3.76/1.00  --pure_diseq_elim                       true
% 3.76/1.00  --brand_transform                       false
% 3.76/1.00  --non_eq_to_eq                          false
% 3.76/1.00  --prep_def_merge                        true
% 3.76/1.00  --prep_def_merge_prop_impl              false
% 3.76/1.00  --prep_def_merge_mbd                    true
% 3.76/1.00  --prep_def_merge_tr_red                 false
% 3.76/1.00  --prep_def_merge_tr_cl                  false
% 3.76/1.00  --smt_preprocessing                     true
% 3.76/1.00  --smt_ac_axioms                         fast
% 3.76/1.00  --preprocessed_out                      false
% 3.76/1.00  --preprocessed_stats                    false
% 3.76/1.00  
% 3.76/1.00  ------ Abstraction refinement Options
% 3.76/1.00  
% 3.76/1.00  --abstr_ref                             []
% 3.76/1.00  --abstr_ref_prep                        false
% 3.76/1.00  --abstr_ref_until_sat                   false
% 3.76/1.00  --abstr_ref_sig_restrict                funpre
% 3.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.00  --abstr_ref_under                       []
% 3.76/1.00  
% 3.76/1.00  ------ SAT Options
% 3.76/1.00  
% 3.76/1.00  --sat_mode                              false
% 3.76/1.00  --sat_fm_restart_options                ""
% 3.76/1.00  --sat_gr_def                            false
% 3.76/1.00  --sat_epr_types                         true
% 3.76/1.00  --sat_non_cyclic_types                  false
% 3.76/1.00  --sat_finite_models                     false
% 3.76/1.00  --sat_fm_lemmas                         false
% 3.76/1.00  --sat_fm_prep                           false
% 3.76/1.00  --sat_fm_uc_incr                        true
% 3.76/1.00  --sat_out_model                         small
% 3.76/1.00  --sat_out_clauses                       false
% 3.76/1.00  
% 3.76/1.00  ------ QBF Options
% 3.76/1.00  
% 3.76/1.00  --qbf_mode                              false
% 3.76/1.00  --qbf_elim_univ                         false
% 3.76/1.00  --qbf_dom_inst                          none
% 3.76/1.00  --qbf_dom_pre_inst                      false
% 3.76/1.00  --qbf_sk_in                             false
% 3.76/1.00  --qbf_pred_elim                         true
% 3.76/1.00  --qbf_split                             512
% 3.76/1.00  
% 3.76/1.00  ------ BMC1 Options
% 3.76/1.00  
% 3.76/1.00  --bmc1_incremental                      false
% 3.76/1.00  --bmc1_axioms                           reachable_all
% 3.76/1.00  --bmc1_min_bound                        0
% 3.76/1.00  --bmc1_max_bound                        -1
% 3.76/1.00  --bmc1_max_bound_default                -1
% 3.76/1.00  --bmc1_symbol_reachability              true
% 3.76/1.00  --bmc1_property_lemmas                  false
% 3.76/1.00  --bmc1_k_induction                      false
% 3.76/1.00  --bmc1_non_equiv_states                 false
% 3.76/1.00  --bmc1_deadlock                         false
% 3.76/1.00  --bmc1_ucm                              false
% 3.76/1.00  --bmc1_add_unsat_core                   none
% 3.76/1.00  --bmc1_unsat_core_children              false
% 3.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.00  --bmc1_out_stat                         full
% 3.76/1.00  --bmc1_ground_init                      false
% 3.76/1.00  --bmc1_pre_inst_next_state              false
% 3.76/1.00  --bmc1_pre_inst_state                   false
% 3.76/1.00  --bmc1_pre_inst_reach_state             false
% 3.76/1.00  --bmc1_out_unsat_core                   false
% 3.76/1.00  --bmc1_aig_witness_out                  false
% 3.76/1.00  --bmc1_verbose                          false
% 3.76/1.00  --bmc1_dump_clauses_tptp                false
% 3.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.00  --bmc1_dump_file                        -
% 3.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.00  --bmc1_ucm_extend_mode                  1
% 3.76/1.00  --bmc1_ucm_init_mode                    2
% 3.76/1.00  --bmc1_ucm_cone_mode                    none
% 3.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.00  --bmc1_ucm_relax_model                  4
% 3.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.00  --bmc1_ucm_layered_model                none
% 3.76/1.00  --bmc1_ucm_max_lemma_size               10
% 3.76/1.00  
% 3.76/1.00  ------ AIG Options
% 3.76/1.00  
% 3.76/1.00  --aig_mode                              false
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation Options
% 3.76/1.00  
% 3.76/1.00  --instantiation_flag                    true
% 3.76/1.00  --inst_sos_flag                         true
% 3.76/1.00  --inst_sos_phase                        true
% 3.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel_side                     num_symb
% 3.76/1.00  --inst_solver_per_active                1400
% 3.76/1.00  --inst_solver_calls_frac                1.
% 3.76/1.00  --inst_passive_queue_type               priority_queues
% 3.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.00  --inst_passive_queues_freq              [25;2]
% 3.76/1.00  --inst_dismatching                      true
% 3.76/1.00  --inst_eager_unprocessed_to_passive     true
% 3.76/1.00  --inst_prop_sim_given                   true
% 3.76/1.00  --inst_prop_sim_new                     false
% 3.76/1.00  --inst_subs_new                         false
% 3.76/1.00  --inst_eq_res_simp                      false
% 3.76/1.00  --inst_subs_given                       false
% 3.76/1.00  --inst_orphan_elimination               true
% 3.76/1.00  --inst_learning_loop_flag               true
% 3.76/1.00  --inst_learning_start                   3000
% 3.76/1.00  --inst_learning_factor                  2
% 3.76/1.00  --inst_start_prop_sim_after_learn       3
% 3.76/1.00  --inst_sel_renew                        solver
% 3.76/1.00  --inst_lit_activity_flag                true
% 3.76/1.00  --inst_restr_to_given                   false
% 3.76/1.00  --inst_activity_threshold               500
% 3.76/1.00  --inst_out_proof                        true
% 3.76/1.00  
% 3.76/1.00  ------ Resolution Options
% 3.76/1.00  
% 3.76/1.00  --resolution_flag                       true
% 3.76/1.00  --res_lit_sel                           adaptive
% 3.76/1.00  --res_lit_sel_side                      none
% 3.76/1.00  --res_ordering                          kbo
% 3.76/1.00  --res_to_prop_solver                    active
% 3.76/1.00  --res_prop_simpl_new                    false
% 3.76/1.00  --res_prop_simpl_given                  true
% 3.76/1.00  --res_passive_queue_type                priority_queues
% 3.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.00  --res_passive_queues_freq               [15;5]
% 3.76/1.00  --res_forward_subs                      full
% 3.76/1.00  --res_backward_subs                     full
% 3.76/1.00  --res_forward_subs_resolution           true
% 3.76/1.00  --res_backward_subs_resolution          true
% 3.76/1.00  --res_orphan_elimination                true
% 3.76/1.00  --res_time_limit                        2.
% 3.76/1.00  --res_out_proof                         true
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Options
% 3.76/1.00  
% 3.76/1.00  --superposition_flag                    true
% 3.76/1.00  --sup_passive_queue_type                priority_queues
% 3.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.76/1.00  --demod_completeness_check              fast
% 3.76/1.00  --demod_use_ground                      true
% 3.76/1.00  --sup_to_prop_solver                    passive
% 3.76/1.00  --sup_prop_simpl_new                    true
% 3.76/1.00  --sup_prop_simpl_given                  true
% 3.76/1.00  --sup_fun_splitting                     true
% 3.76/1.00  --sup_smt_interval                      50000
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Simplification Setup
% 3.76/1.00  
% 3.76/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.76/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.76/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.76/1.00  --sup_immed_triv                        [TrivRules]
% 3.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_bw_main                     []
% 3.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_input_bw                          []
% 3.76/1.00  
% 3.76/1.00  ------ Combination Options
% 3.76/1.00  
% 3.76/1.00  --comb_res_mult                         3
% 3.76/1.00  --comb_sup_mult                         2
% 3.76/1.00  --comb_inst_mult                        10
% 3.76/1.00  
% 3.76/1.00  ------ Debug Options
% 3.76/1.00  
% 3.76/1.00  --dbg_backtrace                         false
% 3.76/1.00  --dbg_dump_prop_clauses                 false
% 3.76/1.00  --dbg_dump_prop_clauses_file            -
% 3.76/1.00  --dbg_out_stat                          false
% 3.76/1.00  ------ Parsing...
% 3.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/1.00  ------ Proving...
% 3.76/1.00  ------ Problem Properties 
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  clauses                                 31
% 3.76/1.00  conjectures                             3
% 3.76/1.00  EPR                                     5
% 3.76/1.00  Horn                                    27
% 3.76/1.00  unary                                   6
% 3.76/1.00  binary                                  9
% 3.76/1.00  lits                                    90
% 3.76/1.00  lits eq                                 31
% 3.76/1.00  fd_pure                                 0
% 3.76/1.00  fd_pseudo                               0
% 3.76/1.00  fd_cond                                 2
% 3.76/1.00  fd_pseudo_cond                          1
% 3.76/1.00  AC symbols                              0
% 3.76/1.00  
% 3.76/1.00  ------ Schedule dynamic 5 is on 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ 
% 3.76/1.00  Current options:
% 3.76/1.00  ------ 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options
% 3.76/1.00  
% 3.76/1.00  --out_options                           all
% 3.76/1.00  --tptp_safe_out                         true
% 3.76/1.00  --problem_path                          ""
% 3.76/1.00  --include_path                          ""
% 3.76/1.00  --clausifier                            res/vclausify_rel
% 3.76/1.00  --clausifier_options                    ""
% 3.76/1.00  --stdin                                 false
% 3.76/1.00  --stats_out                             all
% 3.76/1.00  
% 3.76/1.00  ------ General Options
% 3.76/1.00  
% 3.76/1.00  --fof                                   false
% 3.76/1.00  --time_out_real                         305.
% 3.76/1.00  --time_out_virtual                      -1.
% 3.76/1.00  --symbol_type_check                     false
% 3.76/1.00  --clausify_out                          false
% 3.76/1.00  --sig_cnt_out                           false
% 3.76/1.00  --trig_cnt_out                          false
% 3.76/1.00  --trig_cnt_out_tolerance                1.
% 3.76/1.00  --trig_cnt_out_sk_spl                   false
% 3.76/1.00  --abstr_cl_out                          false
% 3.76/1.00  
% 3.76/1.00  ------ Global Options
% 3.76/1.00  
% 3.76/1.00  --schedule                              default
% 3.76/1.00  --add_important_lit                     false
% 3.76/1.00  --prop_solver_per_cl                    1000
% 3.76/1.00  --min_unsat_core                        false
% 3.76/1.00  --soft_assumptions                      false
% 3.76/1.00  --soft_lemma_size                       3
% 3.76/1.00  --prop_impl_unit_size                   0
% 3.76/1.00  --prop_impl_unit                        []
% 3.76/1.00  --share_sel_clauses                     true
% 3.76/1.00  --reset_solvers                         false
% 3.76/1.00  --bc_imp_inh                            [conj_cone]
% 3.76/1.00  --conj_cone_tolerance                   3.
% 3.76/1.00  --extra_neg_conj                        none
% 3.76/1.00  --large_theory_mode                     true
% 3.76/1.00  --prolific_symb_bound                   200
% 3.76/1.00  --lt_threshold                          2000
% 3.76/1.00  --clause_weak_htbl                      true
% 3.76/1.00  --gc_record_bc_elim                     false
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing Options
% 3.76/1.00  
% 3.76/1.00  --preprocessing_flag                    true
% 3.76/1.00  --time_out_prep_mult                    0.1
% 3.76/1.00  --splitting_mode                        input
% 3.76/1.00  --splitting_grd                         true
% 3.76/1.00  --splitting_cvd                         false
% 3.76/1.00  --splitting_cvd_svl                     false
% 3.76/1.00  --splitting_nvd                         32
% 3.76/1.00  --sub_typing                            true
% 3.76/1.00  --prep_gs_sim                           true
% 3.76/1.00  --prep_unflatten                        true
% 3.76/1.00  --prep_res_sim                          true
% 3.76/1.00  --prep_upred                            true
% 3.76/1.00  --prep_sem_filter                       exhaustive
% 3.76/1.00  --prep_sem_filter_out                   false
% 3.76/1.00  --pred_elim                             true
% 3.76/1.00  --res_sim_input                         true
% 3.76/1.00  --eq_ax_congr_red                       true
% 3.76/1.00  --pure_diseq_elim                       true
% 3.76/1.00  --brand_transform                       false
% 3.76/1.00  --non_eq_to_eq                          false
% 3.76/1.00  --prep_def_merge                        true
% 3.76/1.00  --prep_def_merge_prop_impl              false
% 3.76/1.00  --prep_def_merge_mbd                    true
% 3.76/1.00  --prep_def_merge_tr_red                 false
% 3.76/1.00  --prep_def_merge_tr_cl                  false
% 3.76/1.00  --smt_preprocessing                     true
% 3.76/1.00  --smt_ac_axioms                         fast
% 3.76/1.00  --preprocessed_out                      false
% 3.76/1.00  --preprocessed_stats                    false
% 3.76/1.00  
% 3.76/1.00  ------ Abstraction refinement Options
% 3.76/1.00  
% 3.76/1.00  --abstr_ref                             []
% 3.76/1.00  --abstr_ref_prep                        false
% 3.76/1.00  --abstr_ref_until_sat                   false
% 3.76/1.00  --abstr_ref_sig_restrict                funpre
% 3.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.00  --abstr_ref_under                       []
% 3.76/1.00  
% 3.76/1.00  ------ SAT Options
% 3.76/1.00  
% 3.76/1.00  --sat_mode                              false
% 3.76/1.00  --sat_fm_restart_options                ""
% 3.76/1.00  --sat_gr_def                            false
% 3.76/1.00  --sat_epr_types                         true
% 3.76/1.00  --sat_non_cyclic_types                  false
% 3.76/1.00  --sat_finite_models                     false
% 3.76/1.00  --sat_fm_lemmas                         false
% 3.76/1.00  --sat_fm_prep                           false
% 3.76/1.00  --sat_fm_uc_incr                        true
% 3.76/1.00  --sat_out_model                         small
% 3.76/1.00  --sat_out_clauses                       false
% 3.76/1.00  
% 3.76/1.00  ------ QBF Options
% 3.76/1.00  
% 3.76/1.00  --qbf_mode                              false
% 3.76/1.00  --qbf_elim_univ                         false
% 3.76/1.00  --qbf_dom_inst                          none
% 3.76/1.00  --qbf_dom_pre_inst                      false
% 3.76/1.00  --qbf_sk_in                             false
% 3.76/1.00  --qbf_pred_elim                         true
% 3.76/1.00  --qbf_split                             512
% 3.76/1.00  
% 3.76/1.00  ------ BMC1 Options
% 3.76/1.00  
% 3.76/1.00  --bmc1_incremental                      false
% 3.76/1.00  --bmc1_axioms                           reachable_all
% 3.76/1.00  --bmc1_min_bound                        0
% 3.76/1.00  --bmc1_max_bound                        -1
% 3.76/1.00  --bmc1_max_bound_default                -1
% 3.76/1.00  --bmc1_symbol_reachability              true
% 3.76/1.00  --bmc1_property_lemmas                  false
% 3.76/1.00  --bmc1_k_induction                      false
% 3.76/1.00  --bmc1_non_equiv_states                 false
% 3.76/1.00  --bmc1_deadlock                         false
% 3.76/1.00  --bmc1_ucm                              false
% 3.76/1.00  --bmc1_add_unsat_core                   none
% 3.76/1.00  --bmc1_unsat_core_children              false
% 3.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.00  --bmc1_out_stat                         full
% 3.76/1.00  --bmc1_ground_init                      false
% 3.76/1.00  --bmc1_pre_inst_next_state              false
% 3.76/1.00  --bmc1_pre_inst_state                   false
% 3.76/1.00  --bmc1_pre_inst_reach_state             false
% 3.76/1.00  --bmc1_out_unsat_core                   false
% 3.76/1.00  --bmc1_aig_witness_out                  false
% 3.76/1.00  --bmc1_verbose                          false
% 3.76/1.00  --bmc1_dump_clauses_tptp                false
% 3.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.00  --bmc1_dump_file                        -
% 3.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.00  --bmc1_ucm_extend_mode                  1
% 3.76/1.00  --bmc1_ucm_init_mode                    2
% 3.76/1.00  --bmc1_ucm_cone_mode                    none
% 3.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.00  --bmc1_ucm_relax_model                  4
% 3.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.00  --bmc1_ucm_layered_model                none
% 3.76/1.00  --bmc1_ucm_max_lemma_size               10
% 3.76/1.00  
% 3.76/1.00  ------ AIG Options
% 3.76/1.00  
% 3.76/1.00  --aig_mode                              false
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation Options
% 3.76/1.00  
% 3.76/1.00  --instantiation_flag                    true
% 3.76/1.00  --inst_sos_flag                         true
% 3.76/1.00  --inst_sos_phase                        true
% 3.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel_side                     none
% 3.76/1.00  --inst_solver_per_active                1400
% 3.76/1.00  --inst_solver_calls_frac                1.
% 3.76/1.00  --inst_passive_queue_type               priority_queues
% 3.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.00  --inst_passive_queues_freq              [25;2]
% 3.76/1.00  --inst_dismatching                      true
% 3.76/1.00  --inst_eager_unprocessed_to_passive     true
% 3.76/1.00  --inst_prop_sim_given                   true
% 3.76/1.00  --inst_prop_sim_new                     false
% 3.76/1.00  --inst_subs_new                         false
% 3.76/1.00  --inst_eq_res_simp                      false
% 3.76/1.00  --inst_subs_given                       false
% 3.76/1.00  --inst_orphan_elimination               true
% 3.76/1.00  --inst_learning_loop_flag               true
% 3.76/1.00  --inst_learning_start                   3000
% 3.76/1.00  --inst_learning_factor                  2
% 3.76/1.00  --inst_start_prop_sim_after_learn       3
% 3.76/1.00  --inst_sel_renew                        solver
% 3.76/1.00  --inst_lit_activity_flag                true
% 3.76/1.00  --inst_restr_to_given                   false
% 3.76/1.00  --inst_activity_threshold               500
% 3.76/1.00  --inst_out_proof                        true
% 3.76/1.00  
% 3.76/1.00  ------ Resolution Options
% 3.76/1.00  
% 3.76/1.00  --resolution_flag                       false
% 3.76/1.00  --res_lit_sel                           adaptive
% 3.76/1.00  --res_lit_sel_side                      none
% 3.76/1.00  --res_ordering                          kbo
% 3.76/1.00  --res_to_prop_solver                    active
% 3.76/1.00  --res_prop_simpl_new                    false
% 3.76/1.00  --res_prop_simpl_given                  true
% 3.76/1.00  --res_passive_queue_type                priority_queues
% 3.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.00  --res_passive_queues_freq               [15;5]
% 3.76/1.00  --res_forward_subs                      full
% 3.76/1.00  --res_backward_subs                     full
% 3.76/1.00  --res_forward_subs_resolution           true
% 3.76/1.00  --res_backward_subs_resolution          true
% 3.76/1.00  --res_orphan_elimination                true
% 3.76/1.00  --res_time_limit                        2.
% 3.76/1.00  --res_out_proof                         true
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Options
% 3.76/1.00  
% 3.76/1.00  --superposition_flag                    true
% 3.76/1.00  --sup_passive_queue_type                priority_queues
% 3.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.76/1.00  --demod_completeness_check              fast
% 3.76/1.00  --demod_use_ground                      true
% 3.76/1.00  --sup_to_prop_solver                    passive
% 3.76/1.00  --sup_prop_simpl_new                    true
% 3.76/1.00  --sup_prop_simpl_given                  true
% 3.76/1.00  --sup_fun_splitting                     true
% 3.76/1.00  --sup_smt_interval                      50000
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Simplification Setup
% 3.76/1.00  
% 3.76/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.76/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.76/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.76/1.00  --sup_immed_triv                        [TrivRules]
% 3.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_bw_main                     []
% 3.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_input_bw                          []
% 3.76/1.00  
% 3.76/1.00  ------ Combination Options
% 3.76/1.00  
% 3.76/1.00  --comb_res_mult                         3
% 3.76/1.00  --comb_sup_mult                         2
% 3.76/1.00  --comb_inst_mult                        10
% 3.76/1.00  
% 3.76/1.00  ------ Debug Options
% 3.76/1.00  
% 3.76/1.00  --dbg_backtrace                         false
% 3.76/1.00  --dbg_dump_prop_clauses                 false
% 3.76/1.00  --dbg_dump_prop_clauses_file            -
% 3.76/1.00  --dbg_out_stat                          false
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ Proving...
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS status Theorem for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  fof(f15,conjecture,(
% 3.76/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f16,negated_conjecture,(
% 3.76/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.76/1.00    inference(negated_conjecture,[],[f15])).
% 3.76/1.00  
% 3.76/1.00  fof(f32,plain,(
% 3.76/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.76/1.00    inference(ennf_transformation,[],[f16])).
% 3.76/1.00  
% 3.76/1.00  fof(f33,plain,(
% 3.76/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.76/1.00    inference(flattening,[],[f32])).
% 3.76/1.00  
% 3.76/1.00  fof(f38,plain,(
% 3.76/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f39,plain,(
% 3.76/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f38])).
% 3.76/1.00  
% 3.76/1.00  fof(f68,plain,(
% 3.76/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.76/1.00    inference(cnf_transformation,[],[f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f3,axiom,(
% 3.76/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f36,plain,(
% 3.76/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.76/1.00    inference(nnf_transformation,[],[f3])).
% 3.76/1.00  
% 3.76/1.00  fof(f44,plain,(
% 3.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f36])).
% 3.76/1.00  
% 3.76/1.00  fof(f4,axiom,(
% 3.76/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f17,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.76/1.00    inference(ennf_transformation,[],[f4])).
% 3.76/1.00  
% 3.76/1.00  fof(f46,plain,(
% 3.76/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f17])).
% 3.76/1.00  
% 3.76/1.00  fof(f45,plain,(
% 3.76/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f36])).
% 3.76/1.00  
% 3.76/1.00  fof(f5,axiom,(
% 3.76/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f47,plain,(
% 3.76/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f5])).
% 3.76/1.00  
% 3.76/1.00  fof(f8,axiom,(
% 3.76/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f22,plain,(
% 3.76/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f8])).
% 3.76/1.00  
% 3.76/1.00  fof(f23,plain,(
% 3.76/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.76/1.00    inference(flattening,[],[f22])).
% 3.76/1.00  
% 3.76/1.00  fof(f52,plain,(
% 3.76/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f23])).
% 3.76/1.00  
% 3.76/1.00  fof(f69,plain,(
% 3.76/1.00    v2_funct_1(sK2)),
% 3.76/1.00    inference(cnf_transformation,[],[f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f66,plain,(
% 3.76/1.00    v1_funct_1(sK2)),
% 3.76/1.00    inference(cnf_transformation,[],[f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f11,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f26,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f11])).
% 3.76/1.00  
% 3.76/1.00  fof(f55,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f26])).
% 3.76/1.00  
% 3.76/1.00  fof(f70,plain,(
% 3.76/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.76/1.00    inference(cnf_transformation,[],[f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f51,plain,(
% 3.76/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f23])).
% 3.76/1.00  
% 3.76/1.00  fof(f14,axiom,(
% 3.76/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f30,plain,(
% 3.76/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.76/1.00    inference(ennf_transformation,[],[f14])).
% 3.76/1.00  
% 3.76/1.00  fof(f31,plain,(
% 3.76/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.76/1.00    inference(flattening,[],[f30])).
% 3.76/1.00  
% 3.76/1.00  fof(f65,plain,(
% 3.76/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f31])).
% 3.76/1.00  
% 3.76/1.00  fof(f6,axiom,(
% 3.76/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f18,plain,(
% 3.76/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f6])).
% 3.76/1.00  
% 3.76/1.00  fof(f19,plain,(
% 3.76/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.76/1.00    inference(flattening,[],[f18])).
% 3.76/1.00  
% 3.76/1.00  fof(f49,plain,(
% 3.76/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f19])).
% 3.76/1.00  
% 3.76/1.00  fof(f48,plain,(
% 3.76/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f19])).
% 3.76/1.00  
% 3.76/1.00  fof(f64,plain,(
% 3.76/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f31])).
% 3.76/1.00  
% 3.76/1.00  fof(f71,plain,(
% 3.76/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.76/1.00    inference(cnf_transformation,[],[f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f13,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f28,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f13])).
% 3.76/1.00  
% 3.76/1.00  fof(f29,plain,(
% 3.76/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(flattening,[],[f28])).
% 3.76/1.00  
% 3.76/1.00  fof(f37,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(nnf_transformation,[],[f29])).
% 3.76/1.00  
% 3.76/1.00  fof(f61,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f37])).
% 3.76/1.00  
% 3.76/1.00  fof(f76,plain,(
% 3.76/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.76/1.00    inference(equality_resolution,[],[f61])).
% 3.76/1.00  
% 3.76/1.00  fof(f1,axiom,(
% 3.76/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f34,plain,(
% 3.76/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.76/1.00    inference(nnf_transformation,[],[f1])).
% 3.76/1.00  
% 3.76/1.00  fof(f35,plain,(
% 3.76/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.76/1.00    inference(flattening,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f40,plain,(
% 3.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.76/1.00    inference(cnf_transformation,[],[f35])).
% 3.76/1.00  
% 3.76/1.00  fof(f73,plain,(
% 3.76/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.76/1.00    inference(equality_resolution,[],[f40])).
% 3.76/1.00  
% 3.76/1.00  fof(f57,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f37])).
% 3.76/1.00  
% 3.76/1.00  fof(f67,plain,(
% 3.76/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.76/1.00    inference(cnf_transformation,[],[f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f10,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f25,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f10])).
% 3.76/1.00  
% 3.76/1.00  fof(f54,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f25])).
% 3.76/1.00  
% 3.76/1.00  fof(f2,axiom,(
% 3.76/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f43,plain,(
% 3.76/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f2])).
% 3.76/1.00  
% 3.76/1.00  fof(f42,plain,(
% 3.76/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f35])).
% 3.76/1.00  
% 3.76/1.00  fof(f7,axiom,(
% 3.76/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f20,plain,(
% 3.76/1.00    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.76/1.00    inference(ennf_transformation,[],[f7])).
% 3.76/1.00  
% 3.76/1.00  fof(f21,plain,(
% 3.76/1.00    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.76/1.00    inference(flattening,[],[f20])).
% 3.76/1.00  
% 3.76/1.00  fof(f50,plain,(
% 3.76/1.00    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f21])).
% 3.76/1.00  
% 3.76/1.00  fof(f12,axiom,(
% 3.76/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f27,plain,(
% 3.76/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f12])).
% 3.76/1.00  
% 3.76/1.00  fof(f56,plain,(
% 3.76/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f27])).
% 3.76/1.00  
% 3.76/1.00  fof(f9,axiom,(
% 3.76/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f24,plain,(
% 3.76/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f9])).
% 3.76/1.00  
% 3.76/1.00  fof(f53,plain,(
% 3.76/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f24])).
% 3.76/1.00  
% 3.76/1.00  cnf(c_29,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.76/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1680,plain,
% 3.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1689,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.76/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2169,plain,
% 3.76/1.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1680,c_1689]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.76/1.00      | ~ v1_relat_1(X1)
% 3.76/1.00      | v1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_236,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.76/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_237,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_236]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_294,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.76/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_237]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1678,plain,
% 3.76/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.76/1.00      | v1_relat_1(X1) != iProver_top
% 3.76/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5204,plain,
% 3.76/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.76/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2169,c_1678]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_34,plain,
% 3.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1883,plain,
% 3.76/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/1.00      | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2083,plain,
% 3.76/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.76/1.00      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1883]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2084,plain,
% 3.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.76/1.00      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2083]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1866,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.76/1.00      | v1_relat_1(X0)
% 3.76/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_294]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2172,plain,
% 3.76/1.00      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 3.76/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.76/1.00      | v1_relat_1(sK2) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1866]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2173,plain,
% 3.76/1.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.76/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7,plain,
% 3.76/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2267,plain,
% 3.76/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2268,plain,
% 3.76/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2267]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5304,plain,
% 3.76/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_5204,c_34,c_2084,c_2173,c_2268]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11,plain,
% 3.76/1.00      ( ~ v2_funct_1(X0)
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_28,negated_conjecture,
% 3.76/1.00      ( v2_funct_1(sK2) ),
% 3.76/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_434,plain,
% 3.76/1.00      ( ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.76/1.00      | sK2 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_435,plain,
% 3.76/1.00      ( ~ v1_funct_1(sK2)
% 3.76/1.00      | ~ v1_relat_1(sK2)
% 3.76/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_434]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_31,negated_conjecture,
% 3.76/1.00      ( v1_funct_1(sK2) ),
% 3.76/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_437,plain,
% 3.76/1.00      ( ~ v1_relat_1(sK2)
% 3.76/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_435,c_31]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1675,plain,
% 3.76/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.76/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5308,plain,
% 3.76/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_5304,c_1675]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_15,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1683,plain,
% 3.76/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.76/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2431,plain,
% 3.76/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1680,c_1683]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_27,negated_conjecture,
% 3.76/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.76/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2432,plain,
% 3.76/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_2431,c_27]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12,plain,
% 3.76/1.00      ( ~ v2_funct_1(X0)
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_420,plain,
% 3.76/1.00      ( ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.76/1.00      | sK2 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_421,plain,
% 3.76/1.00      ( ~ v1_funct_1(sK2)
% 3.76/1.00      | ~ v1_relat_1(sK2)
% 3.76/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_423,plain,
% 3.76/1.00      ( ~ v1_relat_1(sK2)
% 3.76/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_421,c_31]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1676,plain,
% 3.76/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.76/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2512,plain,
% 3.76/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.76/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2432,c_1676]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2617,plain,
% 3.76/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_2512,c_34,c_2084,c_2173,c_2268]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_23,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.76/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1681,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top
% 3.76/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3643,plain,
% 3.76/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.76/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2617,c_1681]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_32,plain,
% 3.76/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8,plain,
% 3.76/1.00      ( ~ v1_funct_1(X0)
% 3.76/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.76/1.00      | ~ v1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1751,plain,
% 3.76/1.00      ( v1_funct_1(k2_funct_1(sK2))
% 3.76/1.00      | ~ v1_funct_1(sK2)
% 3.76/1.00      | ~ v1_relat_1(sK2) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1752,plain,
% 3.76/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.76/1.00      | v1_funct_1(sK2) != iProver_top
% 3.76/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1751]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9,plain,
% 3.76/1.00      ( ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2030,plain,
% 3.76/1.00      ( ~ v1_funct_1(sK2)
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2))
% 3.76/1.00      | ~ v1_relat_1(sK2) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2031,plain,
% 3.76/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.76/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2030]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4037,plain,
% 3.76/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_3643,c_32,c_34,c_1752,c_2031,c_2084,c_2173,c_2268]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_24,plain,
% 3.76/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.76/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_26,negated_conjecture,
% 3.76/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.76/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.76/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_648,plain,
% 3.76/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.76/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k1_relat_1(X0) != sK1
% 3.76/1.00      | k2_funct_1(sK2) != X0
% 3.76/1.00      | sK0 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_649,plain,
% 3.76/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.76/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.76/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.76/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.76/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_648]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1666,plain,
% 3.76/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.76/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.76/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2619,plain,
% 3.76/1.00      ( sK1 != sK1
% 3.76/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.76/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2617,c_1666]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2810,plain,
% 3.76/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.76/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(equality_resolution_simp,[status(thm)],[c_2619]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_650,plain,
% 3.76/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.76/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.76/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2812,plain,
% 3.76/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_2810,c_32,c_34,c_650,c_1752,c_2031,c_2084,c_2173,
% 3.76/1.00                 c_2268,c_2512]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4047,plain,
% 3.76/1.00      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_4037,c_2812]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5314,plain,
% 3.76/1.00      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_5308,c_4047]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_18,plain,
% 3.76/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.76/1.00      | k1_xboole_0 = X1
% 3.76/1.00      | k1_xboole_0 = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_492,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.76/1.00      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.76/1.00      | ~ v1_funct_1(X2)
% 3.76/1.00      | ~ v1_relat_1(X2)
% 3.76/1.00      | X2 != X0
% 3.76/1.00      | k1_relat_1(X2) != X1
% 3.76/1.00      | k1_xboole_0 != X3
% 3.76/1.00      | k1_xboole_0 = X0
% 3.76/1.00      | k1_xboole_0 = X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_493,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.76/1.00      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k1_xboole_0 = X0
% 3.76/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_492]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_509,plain,
% 3.76/1.00      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k1_xboole_0 = X0
% 3.76/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.76/1.00      inference(forward_subsumption_resolution,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_493,c_23]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1673,plain,
% 3.76/1.00      ( k1_xboole_0 = X0
% 3.76/1.00      | k1_xboole_0 = k1_relat_1(X0)
% 3.76/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top
% 3.76/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5339,plain,
% 3.76/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.76/1.00      | k2_funct_1(sK2) = k1_xboole_0
% 3.76/1.00      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
% 3.76/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_5308,c_1673]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5342,plain,
% 3.76/1.00      ( k2_funct_1(sK2) = k1_xboole_0
% 3.76/1.00      | sK1 = k1_xboole_0
% 3.76/1.00      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top
% 3.76/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_5339,c_2617]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1005,plain,( X0 = X0 ),theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1902,plain,
% 3.76/1.00      ( sK0 = sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1005]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2,plain,
% 3.76/1.00      ( r1_tarski(X0,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2422,plain,
% 3.76/1.00      ( r1_tarski(sK0,sK0) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_22,plain,
% 3.76/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.76/1.00      | k1_xboole_0 = X2 ),
% 3.76/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_30,negated_conjecture,
% 3.76/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_637,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.76/1.00      | sK0 != X1
% 3.76/1.00      | sK1 != X2
% 3.76/1.00      | sK2 != X0
% 3.76/1.00      | k1_xboole_0 = X2 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_638,plain,
% 3.76/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.76/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.76/1.00      | k1_xboole_0 = sK1 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_637]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_640,plain,
% 3.76/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_638,c_29]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1684,plain,
% 3.76/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.76/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2518,plain,
% 3.76/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1680,c_1684]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2614,plain,
% 3.76/1.00      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_640,c_2518]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4058,plain,
% 3.76/1.00      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
% 3.76/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4047]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1007,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.76/1.00      theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1925,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK0) | X2 != X0 | sK0 != X1 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1007]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2107,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,sK0) | r1_tarski(X1,sK0) | X1 != X0 | sK0 != sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1925]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3733,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,sK0)
% 3.76/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.76/1.00      | k2_relat_1(k2_funct_1(sK2)) != X0
% 3.76/1.00      | sK0 != sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2107]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4605,plain,
% 3.76/1.00      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.76/1.00      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 3.76/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.76/1.00      | sK0 != sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3733]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2527,plain,
% 3.76/1.00      ( r1_tarski(X0,sK0)
% 3.76/1.00      | ~ r1_tarski(sK0,sK0)
% 3.76/1.00      | X0 != sK0
% 3.76/1.00      | sK0 != sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2107]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5007,plain,
% 3.76/1.00      ( r1_tarski(k1_relat_1(sK2),sK0)
% 3.76/1.00      | ~ r1_tarski(sK0,sK0)
% 3.76/1.00      | k1_relat_1(sK2) != sK0
% 3.76/1.00      | sK0 != sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2527]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5541,plain,
% 3.76/1.00      ( sK1 = k1_xboole_0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_5342,c_31,c_29,c_435,c_1902,c_2083,c_2172,c_2267,
% 3.76/1.00                 c_2422,c_2614,c_4058,c_4605,c_5007]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3503,plain,
% 3.76/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.76/1.00      | sK2 = k1_xboole_0
% 3.76/1.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.76/1.00      | v1_funct_1(sK2) != iProver_top
% 3.76/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2432,c_1673]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3768,plain,
% 3.76/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.76/1.00      | sK2 = k1_xboole_0
% 3.76/1.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_3503,c_32,c_34,c_2084,c_2173,c_2268]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5550,plain,
% 3.76/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.76/1.00      | sK2 = k1_xboole_0
% 3.76/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_5541,c_3768]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_100,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_0,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.76/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_105,plain,
% 3.76/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.76/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1775,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1)
% 3.76/1.00      | r1_tarski(sK1,k1_xboole_0)
% 3.76/1.00      | sK1 != X0
% 3.76/1.00      | k1_xboole_0 != X1 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1007]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1777,plain,
% 3.76/1.00      ( r1_tarski(sK1,k1_xboole_0)
% 3.76/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.76/1.00      | sK1 != k1_xboole_0
% 3.76/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1775]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2831,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,sK0) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3770,plain,
% 3.76/1.00      ( ~ r1_tarski(sK1,k1_xboole_0)
% 3.76/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 3.76/1.00      | sK2 = k1_xboole_0 ),
% 3.76/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3768]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2532,plain,
% 3.76/1.00      ( r1_tarski(X0,sK0)
% 3.76/1.00      | ~ r1_tarski(k1_xboole_0,sK0)
% 3.76/1.00      | X0 != k1_xboole_0
% 3.76/1.00      | sK0 != sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2107]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5004,plain,
% 3.76/1.00      ( r1_tarski(k1_relat_1(sK2),sK0)
% 3.76/1.00      | ~ r1_tarski(k1_xboole_0,sK0)
% 3.76/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 3.76/1.00      | sK0 != sK0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2532]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6487,plain,
% 3.76/1.00      ( sK2 = k1_xboole_0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_5550,c_31,c_29,c_100,c_101,c_105,c_435,c_1778,c_1902,
% 3.76/1.00                 c_2083,c_2172,c_2267,c_2422,c_2614,c_2831,c_3768,c_4058,
% 3.76/1.00                 c_4605,c_5007,c_5004]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1692,plain,
% 3.76/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.76/1.00      | ~ v2_funct_1(X1)
% 3.76/1.00      | ~ v1_funct_1(X1)
% 3.76/1.00      | ~ v1_relat_1(X1)
% 3.76/1.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_399,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.76/1.00      | ~ v1_funct_1(X1)
% 3.76/1.00      | ~ v1_relat_1(X1)
% 3.76/1.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.76/1.00      | sK2 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_400,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.76/1.00      | ~ v1_funct_1(sK2)
% 3.76/1.00      | ~ v1_relat_1(sK2)
% 3.76/1.00      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_399]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_404,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.76/1.00      | ~ v1_relat_1(sK2)
% 3.76/1.00      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_400,c_31]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1677,plain,
% 3.76/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.76/1.00      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.76/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6502,plain,
% 3.76/1.00      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
% 3.76/1.00      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.76/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_6487,c_1677]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_89,plain,
% 3.76/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2160,plain,
% 3.76/1.00      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
% 3.76/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.76/1.00      | v1_relat_1(k1_xboole_0) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1866]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2161,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.76/1.00      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 3.76/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2160]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2239,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2240,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2239]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7228,plain,
% 3.76/1.00      ( r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.76/1.00      | k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_6502,c_89,c_2161,c_2240]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7229,plain,
% 3.76/1.00      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
% 3.76/1.00      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_7228]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1691,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1690,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.76/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_16,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.76/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1682,plain,
% 3.76/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.76/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3070,plain,
% 3.76/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.76/1.00      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1690,c_1682]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5925,plain,
% 3.76/1.00      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1691,c_3070]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1685,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.76/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5928,plain,
% 3.76/1.00      ( m1_subset_1(k9_relat_1(k1_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.76/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_5925,c_1685]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6136,plain,
% 3.76/1.00      ( m1_subset_1(k9_relat_1(k1_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.76/1.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X2,X1)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1690,c_5928]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6952,plain,
% 3.76/1.00      ( m1_subset_1(k9_relat_1(k1_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1691,c_6136]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6957,plain,
% 3.76/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),X1) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_6952,c_1689]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1693,plain,
% 3.76/1.00      ( X0 = X1
% 3.76/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.76/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2997,plain,
% 3.76/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1691,c_1693]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7071,plain,
% 3.76/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_6957,c_2997]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7232,plain,
% 3.76/1.00      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = X0
% 3.76/1.00      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_7229,c_7071]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7236,plain,
% 3.76/1.00      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1692,c_7232]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7237,plain,
% 3.76/1.00      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_1691,c_7232]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7257,plain,
% 3.76/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_7236,c_7237]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7432,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_5314,c_6487,c_7257]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2832,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2831]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(contradiction,plain,
% 3.76/1.00      ( $false ),
% 3.76/1.00      inference(minisat,[status(thm)],[c_7432,c_2832]) ).
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  ------                               Statistics
% 3.76/1.00  
% 3.76/1.00  ------ General
% 3.76/1.00  
% 3.76/1.00  abstr_ref_over_cycles:                  0
% 3.76/1.00  abstr_ref_under_cycles:                 0
% 3.76/1.00  gc_basic_clause_elim:                   0
% 3.76/1.00  forced_gc_time:                         0
% 3.76/1.00  parsing_time:                           0.016
% 3.76/1.00  unif_index_cands_time:                  0.
% 3.76/1.00  unif_index_add_time:                    0.
% 3.76/1.00  orderings_time:                         0.
% 3.76/1.00  out_proof_time:                         0.016
% 3.76/1.00  total_time:                             0.238
% 3.76/1.00  num_of_symbols:                         51
% 3.76/1.00  num_of_terms:                           5141
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing
% 3.76/1.00  
% 3.76/1.00  num_of_splits:                          0
% 3.76/1.00  num_of_split_atoms:                     0
% 3.76/1.00  num_of_reused_defs:                     0
% 3.76/1.00  num_eq_ax_congr_red:                    19
% 3.76/1.00  num_of_sem_filtered_clauses:            1
% 3.76/1.00  num_of_subtypes:                        0
% 3.76/1.00  monotx_restored_types:                  0
% 3.76/1.00  sat_num_of_epr_types:                   0
% 3.76/1.00  sat_num_of_non_cyclic_types:            0
% 3.76/1.00  sat_guarded_non_collapsed_types:        0
% 3.76/1.00  num_pure_diseq_elim:                    0
% 3.76/1.00  simp_replaced_by:                       0
% 3.76/1.00  res_preprocessed:                       154
% 3.76/1.00  prep_upred:                             0
% 3.76/1.00  prep_unflattend:                        46
% 3.76/1.00  smt_new_axioms:                         0
% 3.76/1.00  pred_elim_cands:                        4
% 3.76/1.00  pred_elim:                              2
% 3.76/1.00  pred_elim_cl:                           -1
% 3.76/1.00  pred_elim_cycles:                       4
% 3.76/1.00  merged_defs:                            8
% 3.76/1.00  merged_defs_ncl:                        0
% 3.76/1.00  bin_hyper_res:                          9
% 3.76/1.00  prep_cycles:                            4
% 3.76/1.00  pred_elim_time:                         0.008
% 3.76/1.00  splitting_time:                         0.
% 3.76/1.00  sem_filter_time:                        0.
% 3.76/1.00  monotx_time:                            0.
% 3.76/1.00  subtype_inf_time:                       0.
% 3.76/1.00  
% 3.76/1.00  ------ Problem properties
% 3.76/1.00  
% 3.76/1.00  clauses:                                31
% 3.76/1.00  conjectures:                            3
% 3.76/1.00  epr:                                    5
% 3.76/1.00  horn:                                   27
% 3.76/1.00  ground:                                 13
% 3.76/1.00  unary:                                  6
% 3.76/1.00  binary:                                 9
% 3.76/1.00  lits:                                   90
% 3.76/1.00  lits_eq:                                31
% 3.76/1.00  fd_pure:                                0
% 3.76/1.00  fd_pseudo:                              0
% 3.76/1.00  fd_cond:                                2
% 3.76/1.00  fd_pseudo_cond:                         1
% 3.76/1.00  ac_symbols:                             0
% 3.76/1.00  
% 3.76/1.00  ------ Propositional Solver
% 3.76/1.00  
% 3.76/1.00  prop_solver_calls:                      32
% 3.76/1.00  prop_fast_solver_calls:                 1254
% 3.76/1.00  smt_solver_calls:                       0
% 3.76/1.00  smt_fast_solver_calls:                  0
% 3.76/1.00  prop_num_of_clauses:                    2934
% 3.76/1.00  prop_preprocess_simplified:             7142
% 3.76/1.00  prop_fo_subsumed:                       41
% 3.76/1.00  prop_solver_time:                       0.
% 3.76/1.00  smt_solver_time:                        0.
% 3.76/1.00  smt_fast_solver_time:                   0.
% 3.76/1.00  prop_fast_solver_time:                  0.
% 3.76/1.00  prop_unsat_core_time:                   0.
% 3.76/1.00  
% 3.76/1.00  ------ QBF
% 3.76/1.00  
% 3.76/1.00  qbf_q_res:                              0
% 3.76/1.00  qbf_num_tautologies:                    0
% 3.76/1.00  qbf_prep_cycles:                        0
% 3.76/1.00  
% 3.76/1.00  ------ BMC1
% 3.76/1.00  
% 3.76/1.00  bmc1_current_bound:                     -1
% 3.76/1.00  bmc1_last_solved_bound:                 -1
% 3.76/1.00  bmc1_unsat_core_size:                   -1
% 3.76/1.00  bmc1_unsat_core_parents_size:           -1
% 3.76/1.00  bmc1_merge_next_fun:                    0
% 3.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation
% 3.76/1.00  
% 3.76/1.00  inst_num_of_clauses:                    872
% 3.76/1.00  inst_num_in_passive:                    70
% 3.76/1.00  inst_num_in_active:                     453
% 3.76/1.00  inst_num_in_unprocessed:                349
% 3.76/1.00  inst_num_of_loops:                      540
% 3.76/1.00  inst_num_of_learning_restarts:          0
% 3.76/1.00  inst_num_moves_active_passive:          82
% 3.76/1.00  inst_lit_activity:                      0
% 3.76/1.00  inst_lit_activity_moves:                0
% 3.76/1.00  inst_num_tautologies:                   0
% 3.76/1.00  inst_num_prop_implied:                  0
% 3.76/1.00  inst_num_existing_simplified:           0
% 3.76/1.00  inst_num_eq_res_simplified:             0
% 3.76/1.00  inst_num_child_elim:                    0
% 3.76/1.00  inst_num_of_dismatching_blockings:      221
% 3.76/1.00  inst_num_of_non_proper_insts:           1189
% 3.76/1.00  inst_num_of_duplicates:                 0
% 3.76/1.00  inst_inst_num_from_inst_to_res:         0
% 3.76/1.00  inst_dismatching_checking_time:         0.
% 3.76/1.00  
% 3.76/1.00  ------ Resolution
% 3.76/1.00  
% 3.76/1.00  res_num_of_clauses:                     0
% 3.76/1.00  res_num_in_passive:                     0
% 3.76/1.00  res_num_in_active:                      0
% 3.76/1.00  res_num_of_loops:                       158
% 3.76/1.00  res_forward_subset_subsumed:            105
% 3.76/1.00  res_backward_subset_subsumed:           0
% 3.76/1.00  res_forward_subsumed:                   0
% 3.76/1.00  res_backward_subsumed:                  0
% 3.76/1.00  res_forward_subsumption_resolution:     1
% 3.76/1.00  res_backward_subsumption_resolution:    0
% 3.76/1.00  res_clause_to_clause_subsumption:       352
% 3.76/1.00  res_orphan_elimination:                 0
% 3.76/1.00  res_tautology_del:                      129
% 3.76/1.00  res_num_eq_res_simplified:              0
% 3.76/1.00  res_num_sel_changes:                    0
% 3.76/1.00  res_moves_from_active_to_pass:          0
% 3.76/1.00  
% 3.76/1.00  ------ Superposition
% 3.76/1.00  
% 3.76/1.00  sup_time_total:                         0.
% 3.76/1.00  sup_time_generating:                    0.
% 3.76/1.00  sup_time_sim_full:                      0.
% 3.76/1.00  sup_time_sim_immed:                     0.
% 3.76/1.00  
% 3.76/1.00  sup_num_of_clauses:                     88
% 3.76/1.00  sup_num_in_active:                      38
% 3.76/1.00  sup_num_in_passive:                     50
% 3.76/1.00  sup_num_of_loops:                       106
% 3.76/1.00  sup_fw_superposition:                   59
% 3.76/1.00  sup_bw_superposition:                   79
% 3.76/1.00  sup_immediate_simplified:               39
% 3.76/1.00  sup_given_eliminated:                   2
% 3.76/1.00  comparisons_done:                       0
% 3.76/1.00  comparisons_avoided:                    28
% 3.76/1.00  
% 3.76/1.00  ------ Simplifications
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  sim_fw_subset_subsumed:                 10
% 3.76/1.00  sim_bw_subset_subsumed:                 10
% 3.76/1.00  sim_fw_subsumed:                        4
% 3.76/1.00  sim_bw_subsumed:                        6
% 3.76/1.00  sim_fw_subsumption_res:                 0
% 3.76/1.00  sim_bw_subsumption_res:                 0
% 3.76/1.00  sim_tautology_del:                      2
% 3.76/1.00  sim_eq_tautology_del:                   17
% 3.76/1.00  sim_eq_res_simp:                        3
% 3.76/1.00  sim_fw_demodulated:                     8
% 3.76/1.00  sim_bw_demodulated:                     61
% 3.76/1.00  sim_light_normalised:                   21
% 3.76/1.00  sim_joinable_taut:                      0
% 3.76/1.00  sim_joinable_simp:                      0
% 3.76/1.00  sim_ac_normalised:                      0
% 3.76/1.00  sim_smt_subsumption:                    0
% 3.76/1.00  
%------------------------------------------------------------------------------
