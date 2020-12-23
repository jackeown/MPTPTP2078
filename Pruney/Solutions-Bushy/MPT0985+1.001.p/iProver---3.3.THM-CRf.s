%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0985+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:34 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4143)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f41,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f44])).

fof(f74,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_721,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_7973,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | X3_48 != k1_relat_1(X0_48)
    | k1_relset_1(X1_48,X2_48,X0_48) = X3_48 ),
    inference(resolution,[status(thm)],[c_707,c_721])).

cnf(c_5,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_441,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_693,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_441])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_320,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_321,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_323,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_28])).

cnf(c_699,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_323])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_334,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_335,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_337,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_28])).

cnf(c_698,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1379,plain,
    ( sK1 != X0_48
    | sK1 = sK2
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1380,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1425,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1430,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k2_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1435,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k1_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(X1_48)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1440,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_703,plain,
    ( ~ v1_xboole_0(X0_48)
    | k1_xboole_0 = X0_48 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1456,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_726,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1455,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0_48 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1460,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_713,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1493,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_19,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_704,plain,
    ( r1_tarski(X0_48,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1508,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1557,plain,
    ( r1_tarski(k1_relset_1(sK1,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1381,plain,
    ( sK1 != X0_48
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0_48 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1613,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_719,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1614,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1382,plain,
    ( sK2 != X0_48
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0_48 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1616,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1617,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_701,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1235,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1221,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_1643,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_1221])).

cnf(c_1645,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1643])).

cnf(c_1764,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1762,plain,
    ( X0_48 != X1_48
    | sK3 != X1_48
    | sK3 = X0_48 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_2637,plain,
    ( X0_48 != sK3
    | sK3 = X0_48
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_2638,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_2652,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(sK1)
    | sK1 != X0_48 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_2654,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2652])).

cnf(c_2406,plain,
    ( X0_48 != X1_48
    | X0_48 = k1_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK1,sK2,sK3) != X1_48 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_3579,plain,
    ( X0_48 = k1_relset_1(sK1,sK2,sK3)
    | X0_48 != k1_relat_1(sK3)
    | k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(c_3787,plain,
    ( k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relset_1(sK1,sK2,sK3)
    | k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3579])).

cnf(c_1243,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_778,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_1340,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_714,plain,
    ( ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1492,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1496,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_3817,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK1
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1243,c_29,c_31,c_778,c_1340,c_1496])).

cnf(c_3818,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3817])).

cnf(c_3819,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3818])).

cnf(c_2385,plain,
    ( X0_48 != X1_48
    | X0_48 = k2_relset_1(sK1,sK2,sK3)
    | k2_relset_1(sK1,sK2,sK3) != X1_48 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_3560,plain,
    ( k2_relset_1(sK1,sK2,sK3) != X0_48
    | k1_relat_1(k2_funct_1(sK3)) != X0_48
    | k1_relat_1(k2_funct_1(sK3)) = k2_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2385])).

cnf(c_5070,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relset_1(sK1,sK2,sK3)
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_733,plain,
    ( ~ r1_tarski(X0_48,X1_48)
    | r1_tarski(X2_48,X1_48)
    | X2_48 != X0_48 ),
    theory(equality)).

cnf(c_1690,plain,
    ( r1_tarski(X0_48,sK1)
    | ~ r1_tarski(k1_relset_1(sK1,sK2,sK3),sK1)
    | X0_48 != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_5917,plain,
    ( ~ r1_tarski(k1_relset_1(sK1,sK2,sK3),sK1)
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | k2_relat_1(k2_funct_1(sK3)) != k1_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_1566,plain,
    ( X0_48 != X1_48
    | X0_48 = sK3
    | sK3 != X1_48 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_6429,plain,
    ( k2_funct_1(sK3) != X0_48
    | k2_funct_1(sK3) = sK3
    | sK3 != X0_48 ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_6436,plain,
    ( k2_funct_1(sK3) = sK3
    | k2_funct_1(sK3) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6429])).

cnf(c_2440,plain,
    ( X0_48 != X1_48
    | X1_48 = X0_48 ),
    inference(resolution,[status(thm)],[c_721,c_719])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_457,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_459,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_26])).

cnf(c_692,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_459])).

cnf(c_4578,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_2440,c_692])).

cnf(c_4965,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK1,sK2,sK3))
    | v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_4578,c_726])).

cnf(c_3828,plain,
    ( v1_xboole_0(k1_relset_1(sK1,sK2,sK3))
    | ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_726,c_692])).

cnf(c_2469,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_702,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1231,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_1881,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1235,c_1231])).

cnf(c_2710,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_702,c_1881])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_709,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1228,plain,
    ( v1_xboole_0(X0_48) != iProver_top
    | v1_xboole_0(k2_relat_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_2714,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2710,c_1228])).

cnf(c_2715,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2714])).

cnf(c_4032,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3828,c_1645,c_2469,c_2715])).

cnf(c_6954,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK1,sK2,sK3))
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4965,c_4032])).

cnf(c_2432,plain,
    ( X0_48 != sK1
    | k1_relset_1(sK1,sK2,sK3) = X0_48
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_721,c_692])).

cnf(c_3857,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(k1_relset_1(sK1,sK2,sK3))
    | X0_48 != sK1
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_726,c_2432])).

cnf(c_7492,plain,
    ( ~ v1_xboole_0(X0_48)
    | X0_48 != sK1
    | k1_xboole_0 = sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6954,c_3857])).

cnf(c_7495,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_7492])).

cnf(c_1237,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_2217,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1237,c_26,c_699,c_1339])).

cnf(c_15,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_708,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k1_relat_1(X0_48))
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1229,plain,
    ( v1_xboole_0(X0_48) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_48)) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_2219,plain,
    ( v1_xboole_0(k2_relat_1(sK3)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_1229])).

cnf(c_1494,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_8364,plain,
    ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_29,c_31,c_1340,c_1494])).

cnf(c_8365,plain,
    ( v1_xboole_0(k2_relat_1(sK3)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8364])).

cnf(c_8368,plain,
    ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_8365])).

cnf(c_1234,plain,
    ( k1_xboole_0 = X0_48
    | v1_xboole_0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_8489,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8368,c_1234])).

cnf(c_8518,plain,
    ( ~ v1_xboole_0(sK3)
    | k2_funct_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8489])).

cnf(c_1685,plain,
    ( r1_tarski(X0_48,sK2)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | X0_48 != k2_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_6006,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | r1_tarski(k1_relat_1(X0_48),sK2)
    | k1_relat_1(X0_48) != k2_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_10169,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
    | k1_relat_1(k2_funct_1(sK3)) != k2_relset_1(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6006])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != X1
    | sK2 != k1_xboole_0
    | sK3 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_389,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_696,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1489,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | v1_xboole_0(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1850,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_4127,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(sK2)
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_4129,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4127])).

cnf(c_8369,plain,
    ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2710,c_8365])).

cnf(c_1238,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_2421,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1238,c_26,c_698,c_1339])).

cnf(c_2423,plain,
    ( v1_xboole_0(k1_relat_1(sK3)) = iProver_top
    | v1_xboole_0(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2421,c_1228])).

cnf(c_8619,plain,
    ( v1_xboole_0(k1_relat_1(sK3)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8369,c_2423])).

cnf(c_8648,plain,
    ( v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8619])).

cnf(c_20475,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_696,c_26,c_12,c_1339,c_1456,c_1460,c_1489,c_1850,c_4129,c_8648])).

cnf(c_467,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != sK3
    | sK1 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_691,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != sK3
    | sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_20488,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_funct_1(sK3) != sK3
    | sK1 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_4143])).

cnf(c_18,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_705,plain,
    ( ~ r1_tarski(k1_relat_1(X0_48),X1_48)
    | ~ r1_tarski(k2_relat_1(X0_48),X2_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_20647,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != sK3
    | sK1 != sK2 ),
    inference(resolution,[status(thm)],[c_20488,c_705])).

cnf(c_20650,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_28,c_26,c_12,c_699,c_698,c_1339,c_1380,c_1425,c_1430,c_1435,c_1440,c_1456,c_1460,c_1493,c_1508,c_1557,c_1613,c_1614,c_1616,c_1617,c_1645,c_1764,c_2638,c_2654,c_3787,c_3819,c_5070,c_5917,c_6436,c_7495,c_8518,c_10169,c_20475,c_20647])).

cnf(c_20651,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2 ),
    inference(renaming,[status(thm)],[c_20650])).

cnf(c_42612,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK2 != k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[status(thm)],[c_7973,c_20651])).

cnf(c_1667,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),X0_48)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X1_48)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_13863,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0_48)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0_48)))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_24847,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK3)),sK2)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_13863])).

cnf(c_4581,plain,
    ( sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[status(thm)],[c_2440,c_702])).

cnf(c_4710,plain,
    ( X0_48 != k2_relset_1(sK1,sK2,sK3)
    | sK2 = X0_48 ),
    inference(resolution,[status(thm)],[c_4581,c_721])).

cnf(c_1925,plain,
    ( v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_717,c_701])).

cnf(c_1932,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1925,c_699])).

cnf(c_2436,plain,
    ( X0_48 != k2_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = X0_48 ),
    inference(resolution,[status(thm)],[c_721,c_1932])).

cnf(c_5015,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[status(thm)],[c_4710,c_2436])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42612,c_24847,c_10169,c_5917,c_5070,c_5015,c_3787,c_1557,c_1508,c_1493,c_1440,c_1435,c_1430,c_1425,c_1339,c_698,c_699,c_26,c_28])).


%------------------------------------------------------------------------------
