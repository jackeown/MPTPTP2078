%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:29 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  170 (5368 expanded)
%              Number of clauses        :  110 (1814 expanded)
%              Number of leaves         :   13 (1005 expanded)
%              Depth                    :   27
%              Number of atoms          :  517 (27858 expanded)
%              Number of equality atoms :  270 (6058 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f47])).

fof(f82,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_484,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_486,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_35])).

cnf(c_1367,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1371,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3418,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1367,c_1371])).

cnf(c_3666,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_486,c_3418])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1373,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2360,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1373])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_411,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_412,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_414,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_37])).

cnf(c_1364,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_2457,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2360,c_1364])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3936,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2457,c_1368])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1370,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2784,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1367,c_1370])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2796,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2784,c_33])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_397,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_398,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_400,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_37])).

cnf(c_1365,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_2456,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2360,c_1365])).

cnf(c_2936,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2796,c_2456])).

cnf(c_3955,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3936,c_2936])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1716,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1717,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1716])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2007,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2008,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2007])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2014,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2015,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_5039,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3955,c_38,c_40,c_1717,c_2008,c_2015])).

cnf(c_5048,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_5039,c_1371])).

cnf(c_5054,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5048,c_2936])).

cnf(c_5075,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3666,c_5054])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_670,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1
    | k2_funct_1(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_671,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_683,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_671,c_15])).

cnf(c_1352,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_2463,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2456,c_1352])).

cnf(c_2502,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(sK3) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2463,c_38,c_40,c_1717,c_2008])).

cnf(c_2503,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2502])).

cnf(c_2506,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2503,c_2457])).

cnf(c_2935,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2796,c_2506])).

cnf(c_2939,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2935])).

cnf(c_3702,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3666,c_2939])).

cnf(c_5044,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3666,c_5039])).

cnf(c_5437,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5075,c_3702,c_5044])).

cnf(c_5459,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5437,c_1367])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5464,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5459,c_2])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != X1
    | sK2 != k1_xboole_0
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_567,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_1358,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_1474,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1358,c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_113,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1973,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1974,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_1976,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2046,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2047,plain,
    ( sK3 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_2049,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_2135,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1474,c_113,c_1976,c_2049])).

cnf(c_5886,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5464,c_2135])).

cnf(c_5441,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5437,c_5039])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5536,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5441,c_3])).

cnf(c_6472,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5886,c_5536])).

cnf(c_3420,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1371])).

cnf(c_6996,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6472,c_3420])).

cnf(c_5450,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5437,c_2936])).

cnf(c_6475,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5886,c_5450])).

cnf(c_7008,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6996,c_6475])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_624,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_1355,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_1593,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1355,c_3])).

cnf(c_2102,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_38,c_40,c_1717,c_2008])).

cnf(c_2103,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2102])).

cnf(c_5452,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5437,c_2103])).

cnf(c_5501,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5452])).

cnf(c_5505,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5501,c_3])).

cnf(c_5538,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5536,c_5505])).

cnf(c_7173,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5538,c_5886])).

cnf(c_7967,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7008,c_7173])).

cnf(c_7968,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7967])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:12:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.99/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.99  
% 2.99/0.99  ------  iProver source info
% 2.99/0.99  
% 2.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.99  git: non_committed_changes: false
% 2.99/0.99  git: last_make_outside_of_git: false
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     num_symb
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       true
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  ------ Parsing...
% 2.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.99  ------ Proving...
% 2.99/0.99  ------ Problem Properties 
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  clauses                                 40
% 2.99/0.99  conjectures                             3
% 2.99/0.99  EPR                                     5
% 2.99/0.99  Horn                                    33
% 2.99/0.99  unary                                   12
% 2.99/0.99  binary                                  6
% 2.99/0.99  lits                                    107
% 2.99/0.99  lits eq                                 44
% 2.99/0.99  fd_pure                                 0
% 2.99/0.99  fd_pseudo                               0
% 2.99/0.99  fd_cond                                 3
% 2.99/0.99  fd_pseudo_cond                          1
% 2.99/0.99  AC symbols                              0
% 2.99/0.99  
% 2.99/0.99  ------ Schedule dynamic 5 is on 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  Current options:
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     none
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       false
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ Proving...
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS status Theorem for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99   Resolution empty clause
% 2.99/0.99  
% 2.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  fof(f16,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f36,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f37,plain,(
% 2.99/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(flattening,[],[f36])).
% 2.99/0.99  
% 2.99/0.99  fof(f46,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(nnf_transformation,[],[f37])).
% 2.99/0.99  
% 2.99/0.99  fof(f70,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f46])).
% 2.99/0.99  
% 2.99/0.99  fof(f19,conjecture,(
% 2.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f20,negated_conjecture,(
% 2.99/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.99/0.99    inference(negated_conjecture,[],[f19])).
% 2.99/0.99  
% 2.99/0.99  fof(f40,plain,(
% 2.99/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f20])).
% 2.99/0.99  
% 2.99/0.99  fof(f41,plain,(
% 2.99/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.99/0.99    inference(flattening,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f47,plain,(
% 2.99/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f48,plain,(
% 2.99/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f47])).
% 2.99/0.99  
% 2.99/0.99  fof(f82,plain,(
% 2.99/0.99    v1_funct_2(sK3,sK1,sK2)),
% 2.99/0.99    inference(cnf_transformation,[],[f48])).
% 2.99/0.99  
% 2.99/0.99  fof(f83,plain,(
% 2.99/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.99/0.99    inference(cnf_transformation,[],[f48])).
% 2.99/0.99  
% 2.99/0.99  fof(f13,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f32,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f13])).
% 2.99/0.99  
% 2.99/0.99  fof(f66,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f32])).
% 2.99/0.99  
% 2.99/0.99  fof(f11,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f30,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f11])).
% 2.99/0.99  
% 2.99/0.99  fof(f64,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f10,axiom,(
% 2.99/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f28,plain,(
% 2.99/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.99    inference(ennf_transformation,[],[f10])).
% 2.99/0.99  
% 2.99/0.99  fof(f29,plain,(
% 2.99/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.99    inference(flattening,[],[f28])).
% 2.99/0.99  
% 2.99/0.99  fof(f63,plain,(
% 2.99/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f29])).
% 2.99/0.99  
% 2.99/0.99  fof(f84,plain,(
% 2.99/0.99    v2_funct_1(sK3)),
% 2.99/0.99    inference(cnf_transformation,[],[f48])).
% 2.99/0.99  
% 2.99/0.99  fof(f81,plain,(
% 2.99/0.99    v1_funct_1(sK3)),
% 2.99/0.99    inference(cnf_transformation,[],[f48])).
% 2.99/0.99  
% 2.99/0.99  fof(f18,axiom,(
% 2.99/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f38,plain,(
% 2.99/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.99    inference(ennf_transformation,[],[f18])).
% 2.99/0.99  
% 2.99/0.99  fof(f39,plain,(
% 2.99/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.99    inference(flattening,[],[f38])).
% 2.99/0.99  
% 2.99/0.99  fof(f80,plain,(
% 2.99/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f39])).
% 2.99/0.99  
% 2.99/0.99  fof(f14,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f33,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f14])).
% 2.99/0.99  
% 2.99/0.99  fof(f67,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f33])).
% 2.99/0.99  
% 2.99/0.99  fof(f85,plain,(
% 2.99/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 2.99/0.99    inference(cnf_transformation,[],[f48])).
% 2.99/0.99  
% 2.99/0.99  fof(f62,plain,(
% 2.99/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f29])).
% 2.99/0.99  
% 2.99/0.99  fof(f8,axiom,(
% 2.99/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f26,plain,(
% 2.99/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.99    inference(ennf_transformation,[],[f8])).
% 2.99/0.99  
% 2.99/0.99  fof(f27,plain,(
% 2.99/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.99    inference(flattening,[],[f26])).
% 2.99/0.99  
% 2.99/0.99  fof(f58,plain,(
% 2.99/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f27])).
% 2.99/0.99  
% 2.99/0.99  fof(f57,plain,(
% 2.99/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f27])).
% 2.99/0.99  
% 2.99/0.99  fof(f79,plain,(
% 2.99/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f39])).
% 2.99/0.99  
% 2.99/0.99  fof(f86,plain,(
% 2.99/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 2.99/0.99    inference(cnf_transformation,[],[f48])).
% 2.99/0.99  
% 2.99/0.99  fof(f3,axiom,(
% 2.99/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f42,plain,(
% 2.99/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.99/0.99    inference(nnf_transformation,[],[f3])).
% 2.99/0.99  
% 2.99/0.99  fof(f43,plain,(
% 2.99/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.99/0.99    inference(flattening,[],[f42])).
% 2.99/0.99  
% 2.99/0.99  fof(f53,plain,(
% 2.99/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.99/0.99    inference(cnf_transformation,[],[f43])).
% 2.99/0.99  
% 2.99/0.99  fof(f87,plain,(
% 2.99/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.99/0.99    inference(equality_resolution,[],[f53])).
% 2.99/0.99  
% 2.99/0.99  fof(f74,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f46])).
% 2.99/0.99  
% 2.99/0.99  fof(f91,plain,(
% 2.99/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.99/0.99    inference(equality_resolution,[],[f74])).
% 2.99/0.99  
% 2.99/0.99  fof(f1,axiom,(
% 2.99/0.99    v1_xboole_0(k1_xboole_0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f49,plain,(
% 2.99/0.99    v1_xboole_0(k1_xboole_0)),
% 2.99/0.99    inference(cnf_transformation,[],[f1])).
% 2.99/0.99  
% 2.99/0.99  fof(f5,axiom,(
% 2.99/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f23,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f5])).
% 2.99/0.99  
% 2.99/0.99  fof(f55,plain,(
% 2.99/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f23])).
% 2.99/0.99  
% 2.99/0.99  fof(f2,axiom,(
% 2.99/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f22,plain,(
% 2.99/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f2])).
% 2.99/0.99  
% 2.99/0.99  fof(f50,plain,(
% 2.99/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f22])).
% 2.99/0.99  
% 2.99/0.99  fof(f52,plain,(
% 2.99/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.99/0.99    inference(cnf_transformation,[],[f43])).
% 2.99/0.99  
% 2.99/0.99  fof(f88,plain,(
% 2.99/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.99/0.99    inference(equality_resolution,[],[f52])).
% 2.99/0.99  
% 2.99/0.99  fof(f73,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f46])).
% 2.99/0.99  
% 2.99/0.99  fof(f92,plain,(
% 2.99/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.99/0.99    inference(equality_resolution,[],[f73])).
% 2.99/0.99  
% 2.99/0.99  cnf(c_26,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.99/0.99      | k1_xboole_0 = X2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_36,negated_conjecture,
% 2.99/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_483,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.99/0.99      | sK1 != X1
% 2.99/0.99      | sK2 != X2
% 2.99/0.99      | sK3 != X0
% 2.99/0.99      | k1_xboole_0 = X2 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_484,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.99/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.99/0.99      | k1_xboole_0 = sK2 ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_483]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_35,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.99/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_486,plain,
% 2.99/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_484,c_35]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1367,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_17,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1371,plain,
% 2.99/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.99/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3418,plain,
% 2.99/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1367,c_1371]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3666,plain,
% 2.99/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_486,c_3418]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_15,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1373,plain,
% 2.99/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.99/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2360,plain,
% 2.99/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1367,c_1373]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_13,plain,
% 2.99/0.99      ( ~ v2_funct_1(X0)
% 2.99/0.99      | ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_34,negated_conjecture,
% 2.99/0.99      ( v2_funct_1(sK3) ),
% 2.99/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_411,plain,
% 2.99/0.99      ( ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.99/0.99      | sK3 != X0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_412,plain,
% 2.99/0.99      ( ~ v1_relat_1(sK3)
% 2.99/0.99      | ~ v1_funct_1(sK3)
% 2.99/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_411]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_37,negated_conjecture,
% 2.99/0.99      ( v1_funct_1(sK3) ),
% 2.99/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_414,plain,
% 2.99/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_412,c_37]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1364,plain,
% 2.99/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 2.99/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2457,plain,
% 2.99/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2360,c_1364]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_29,plain,
% 2.99/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.99/0.99      | ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1368,plain,
% 2.99/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.99/0.99      | v1_relat_1(X0) != iProver_top
% 2.99/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3936,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 2.99/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2457,c_1368]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_18,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1370,plain,
% 2.99/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.99/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2784,plain,
% 2.99/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1367,c_1370]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_33,negated_conjecture,
% 2.99/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2796,plain,
% 2.99/0.99      ( k2_relat_1(sK3) = sK2 ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2784,c_33]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_14,plain,
% 2.99/0.99      ( ~ v2_funct_1(X0)
% 2.99/0.99      | ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_397,plain,
% 2.99/0.99      ( ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.99/0.99      | sK3 != X0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_398,plain,
% 2.99/0.99      ( ~ v1_relat_1(sK3)
% 2.99/0.99      | ~ v1_funct_1(sK3)
% 2.99/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_397]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_400,plain,
% 2.99/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_398,c_37]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1365,plain,
% 2.99/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 2.99/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2456,plain,
% 2.99/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2360,c_1365]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2936,plain,
% 2.99/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_2796,c_2456]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3955,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 2.99/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_3936,c_2936]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_38,plain,
% 2.99/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_40,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1716,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.99/0.99      | v1_relat_1(sK3) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1717,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.99/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1716]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8,plain,
% 2.99/0.99      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2007,plain,
% 2.99/0.99      ( ~ v1_relat_1(sK3) | v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2008,plain,
% 2.99/0.99      ( v1_relat_1(sK3) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.99/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_2007]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_9,plain,
% 2.99/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2014,plain,
% 2.99/0.99      ( v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) | ~ v1_funct_1(sK3) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2015,plain,
% 2.99/0.99      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 2.99/0.99      | v1_relat_1(sK3) != iProver_top
% 2.99/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5039,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3955,c_38,c_40,c_1717,c_2008,c_2015]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5048,plain,
% 2.99/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_5039,c_1371]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5054,plain,
% 2.99/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_5048,c_2936]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5075,plain,
% 2.99/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_3666,c_5054]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_30,plain,
% 2.99/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.99/0.99      | ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_32,negated_conjecture,
% 2.99/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 2.99/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.99/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_670,plain,
% 2.99/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.99/0.99      | ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.99/0.99      | k1_relat_1(X0) != sK2
% 2.99/0.99      | k2_relat_1(X0) != sK1
% 2.99/0.99      | k2_funct_1(sK3) != X0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_671,plain,
% 2.99/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.99/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 2.99/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.99/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.99/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_670]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_683,plain,
% 2.99/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.99/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.99/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.99/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.99/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_671,c_15]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1352,plain,
% 2.99/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.99/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2463,plain,
% 2.99/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.99/0.99      | k2_relat_1(sK3) != sK2
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_2456,c_1352]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2502,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.99/0.99      | k2_relat_1(sK3) != sK2
% 2.99/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_2463,c_38,c_40,c_1717,c_2008]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2503,plain,
% 2.99/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.99/0.99      | k2_relat_1(sK3) != sK2
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_2502]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2506,plain,
% 2.99/0.99      ( k1_relat_1(sK3) != sK1
% 2.99/0.99      | k2_relat_1(sK3) != sK2
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2503,c_2457]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2935,plain,
% 2.99/0.99      ( k1_relat_1(sK3) != sK1
% 2.99/0.99      | sK2 != sK2
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_2796,c_2506]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2939,plain,
% 2.99/0.99      ( k1_relat_1(sK3) != sK1
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_2935]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3702,plain,
% 2.99/0.99      ( sK2 = k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_3666,c_2939]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5044,plain,
% 2.99/0.99      ( sK2 = k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_3666,c_5039]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5437,plain,
% 2.99/0.99      ( sK2 = k1_xboole_0 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_5075,c_3702,c_5044]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5459,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5437,c_1367]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2,plain,
% 2.99/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5464,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5459,c_2]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_22,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.99/0.99      | k1_xboole_0 = X1
% 2.99/0.99      | k1_xboole_0 = X0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_566,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.99/0.99      | sK1 != X1
% 2.99/0.99      | sK2 != k1_xboole_0
% 2.99/0.99      | sK3 != X0
% 2.99/0.99      | k1_xboole_0 = X0
% 2.99/0.99      | k1_xboole_0 = X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_567,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.99/0.99      | sK2 != k1_xboole_0
% 2.99/0.99      | k1_xboole_0 = sK1
% 2.99/0.99      | k1_xboole_0 = sK3 ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_566]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1358,plain,
% 2.99/0.99      ( sK2 != k1_xboole_0
% 2.99/0.99      | k1_xboole_0 = sK1
% 2.99/0.99      | k1_xboole_0 = sK3
% 2.99/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1474,plain,
% 2.99/0.99      ( sK1 = k1_xboole_0
% 2.99/0.99      | sK2 != k1_xboole_0
% 2.99/0.99      | sK3 = k1_xboole_0
% 2.99/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1358,c_2]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_0,plain,
% 2.99/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_113,plain,
% 2.99/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.99/0.99      | ~ v1_xboole_0(X1)
% 2.99/0.99      | v1_xboole_0(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1973,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 2.99/0.99      | ~ v1_xboole_0(X0)
% 2.99/0.99      | v1_xboole_0(sK3) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1974,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 2.99/0.99      | v1_xboole_0(X0) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1976,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK3) = iProver_top
% 2.99/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2046,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2047,plain,
% 2.99/0.99      ( sK3 = X0
% 2.99/0.99      | v1_xboole_0(X0) != iProver_top
% 2.99/0.99      | v1_xboole_0(sK3) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_2046]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2049,plain,
% 2.99/0.99      ( sK3 = k1_xboole_0
% 2.99/0.99      | v1_xboole_0(sK3) != iProver_top
% 2.99/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_2047]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2135,plain,
% 2.99/0.99      ( sK3 = k1_xboole_0
% 2.99/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_1474,c_113,c_1976,c_2049]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5886,plain,
% 2.99/0.99      ( sK3 = k1_xboole_0 ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_5464,c_2135]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5441,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5437,c_5039]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3,plain,
% 2.99/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5536,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5441,c_3]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6472,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5886,c_5536]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3420,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.99/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_3,c_1371]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6996,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_6472,c_3420]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5450,plain,
% 2.99/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5437,c_2936]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6475,plain,
% 2.99/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5886,c_5450]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7008,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_6996,c_6475]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_23,plain,
% 2.99/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.99/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_623,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.99/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.99/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.99/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.99/0.99      | k2_funct_1(sK3) != X0
% 2.99/0.99      | sK1 != X1
% 2.99/0.99      | sK2 != k1_xboole_0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_624,plain,
% 2.99/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.99/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.99/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.99/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.99/0.99      | sK2 != k1_xboole_0 ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_623]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1355,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.99/0.99      | sK2 != k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1593,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.99/0.99      | sK2 != k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1355,c_3]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2102,plain,
% 2.99/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.99/0.99      | sK2 != k1_xboole_0
% 2.99/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_1593,c_38,c_40,c_1717,c_2008]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2103,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.99/0.99      | sK2 != k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_2102]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5452,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.99/0.99      | k1_xboole_0 != k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5437,c_2103]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5501,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_5452]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5505,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_5501,c_3]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5538,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 2.99/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_5536,c_5505]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7173,plain,
% 2.99/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_5538,c_5886]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7967,plain,
% 2.99/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_7008,c_7173]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7968,plain,
% 2.99/0.99      ( $false ),
% 2.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_7967]) ).
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  ------                               Statistics
% 2.99/0.99  
% 2.99/0.99  ------ General
% 2.99/0.99  
% 2.99/0.99  abstr_ref_over_cycles:                  0
% 2.99/0.99  abstr_ref_under_cycles:                 0
% 2.99/0.99  gc_basic_clause_elim:                   0
% 2.99/0.99  forced_gc_time:                         0
% 2.99/0.99  parsing_time:                           0.039
% 2.99/0.99  unif_index_cands_time:                  0.
% 2.99/0.99  unif_index_add_time:                    0.
% 2.99/0.99  orderings_time:                         0.
% 2.99/0.99  out_proof_time:                         0.01
% 2.99/0.99  total_time:                             0.241
% 2.99/0.99  num_of_symbols:                         51
% 2.99/0.99  num_of_terms:                           5809
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing
% 2.99/0.99  
% 2.99/0.99  num_of_splits:                          0
% 2.99/0.99  num_of_split_atoms:                     0
% 2.99/0.99  num_of_reused_defs:                     0
% 2.99/0.99  num_eq_ax_congr_red:                    4
% 2.99/0.99  num_of_sem_filtered_clauses:            1
% 2.99/0.99  num_of_subtypes:                        0
% 2.99/0.99  monotx_restored_types:                  0
% 2.99/0.99  sat_num_of_epr_types:                   0
% 2.99/0.99  sat_num_of_non_cyclic_types:            0
% 2.99/0.99  sat_guarded_non_collapsed_types:        0
% 2.99/0.99  num_pure_diseq_elim:                    0
% 2.99/0.99  simp_replaced_by:                       0
% 2.99/0.99  res_preprocessed:                       145
% 2.99/0.99  prep_upred:                             0
% 2.99/0.99  prep_unflattend:                        58
% 2.99/0.99  smt_new_axioms:                         0
% 2.99/0.99  pred_elim_cands:                        7
% 2.99/0.99  pred_elim:                              3
% 2.99/0.99  pred_elim_cl:                           -4
% 2.99/0.99  pred_elim_cycles:                       4
% 2.99/0.99  merged_defs:                            0
% 2.99/0.99  merged_defs_ncl:                        0
% 2.99/0.99  bin_hyper_res:                          0
% 2.99/0.99  prep_cycles:                            3
% 2.99/0.99  pred_elim_time:                         0.01
% 2.99/0.99  splitting_time:                         0.
% 2.99/0.99  sem_filter_time:                        0.
% 2.99/0.99  monotx_time:                            0.
% 2.99/0.99  subtype_inf_time:                       0.
% 2.99/0.99  
% 2.99/0.99  ------ Problem properties
% 2.99/0.99  
% 2.99/0.99  clauses:                                40
% 2.99/0.99  conjectures:                            3
% 2.99/0.99  epr:                                    5
% 2.99/0.99  horn:                                   33
% 2.99/0.99  ground:                                 19
% 2.99/0.99  unary:                                  12
% 2.99/0.99  binary:                                 6
% 2.99/0.99  lits:                                   107
% 2.99/0.99  lits_eq:                                44
% 2.99/0.99  fd_pure:                                0
% 2.99/0.99  fd_pseudo:                              0
% 2.99/0.99  fd_cond:                                3
% 2.99/0.99  fd_pseudo_cond:                         1
% 2.99/0.99  ac_symbols:                             0
% 2.99/0.99  
% 2.99/0.99  ------ Propositional Solver
% 2.99/0.99  
% 2.99/0.99  prop_solver_calls:                      25
% 2.99/0.99  prop_fast_solver_calls:                 1115
% 2.99/0.99  smt_solver_calls:                       0
% 2.99/0.99  smt_fast_solver_calls:                  0
% 2.99/0.99  prop_num_of_clauses:                    3063
% 2.99/0.99  prop_preprocess_simplified:             7986
% 2.99/0.99  prop_fo_subsumed:                       32
% 2.99/0.99  prop_solver_time:                       0.
% 2.99/0.99  smt_solver_time:                        0.
% 2.99/0.99  smt_fast_solver_time:                   0.
% 2.99/0.99  prop_fast_solver_time:                  0.
% 2.99/0.99  prop_unsat_core_time:                   0.
% 2.99/0.99  
% 2.99/0.99  ------ QBF
% 2.99/0.99  
% 2.99/0.99  qbf_q_res:                              0
% 2.99/0.99  qbf_num_tautologies:                    0
% 2.99/0.99  qbf_prep_cycles:                        0
% 2.99/0.99  
% 2.99/0.99  ------ BMC1
% 2.99/0.99  
% 2.99/0.99  bmc1_current_bound:                     -1
% 2.99/0.99  bmc1_last_solved_bound:                 -1
% 2.99/0.99  bmc1_unsat_core_size:                   -1
% 2.99/0.99  bmc1_unsat_core_parents_size:           -1
% 2.99/0.99  bmc1_merge_next_fun:                    0
% 2.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation
% 2.99/0.99  
% 2.99/0.99  inst_num_of_clauses:                    1147
% 2.99/0.99  inst_num_in_passive:                    448
% 2.99/0.99  inst_num_in_active:                     470
% 2.99/0.99  inst_num_in_unprocessed:                229
% 2.99/0.99  inst_num_of_loops:                      550
% 2.99/0.99  inst_num_of_learning_restarts:          0
% 2.99/0.99  inst_num_moves_active_passive:          77
% 2.99/0.99  inst_lit_activity:                      0
% 2.99/0.99  inst_lit_activity_moves:                0
% 2.99/0.99  inst_num_tautologies:                   0
% 2.99/0.99  inst_num_prop_implied:                  0
% 2.99/0.99  inst_num_existing_simplified:           0
% 2.99/0.99  inst_num_eq_res_simplified:             0
% 2.99/0.99  inst_num_child_elim:                    0
% 2.99/0.99  inst_num_of_dismatching_blockings:      420
% 2.99/0.99  inst_num_of_non_proper_insts:           1029
% 2.99/0.99  inst_num_of_duplicates:                 0
% 2.99/0.99  inst_inst_num_from_inst_to_res:         0
% 2.99/0.99  inst_dismatching_checking_time:         0.
% 2.99/0.99  
% 2.99/0.99  ------ Resolution
% 2.99/0.99  
% 2.99/0.99  res_num_of_clauses:                     0
% 2.99/0.99  res_num_in_passive:                     0
% 2.99/0.99  res_num_in_active:                      0
% 2.99/0.99  res_num_of_loops:                       148
% 2.99/0.99  res_forward_subset_subsumed:            41
% 2.99/0.99  res_backward_subset_subsumed:           0
% 2.99/0.99  res_forward_subsumed:                   0
% 2.99/0.99  res_backward_subsumed:                  0
% 2.99/0.99  res_forward_subsumption_resolution:     4
% 2.99/0.99  res_backward_subsumption_resolution:    0
% 2.99/0.99  res_clause_to_clause_subsumption:       279
% 2.99/0.99  res_orphan_elimination:                 0
% 2.99/0.99  res_tautology_del:                      110
% 2.99/0.99  res_num_eq_res_simplified:              0
% 2.99/0.99  res_num_sel_changes:                    0
% 2.99/0.99  res_moves_from_active_to_pass:          0
% 2.99/0.99  
% 2.99/0.99  ------ Superposition
% 2.99/0.99  
% 2.99/0.99  sup_time_total:                         0.
% 2.99/0.99  sup_time_generating:                    0.
% 2.99/0.99  sup_time_sim_full:                      0.
% 2.99/0.99  sup_time_sim_immed:                     0.
% 2.99/0.99  
% 2.99/0.99  sup_num_of_clauses:                     104
% 2.99/0.99  sup_num_in_active:                      62
% 2.99/0.99  sup_num_in_passive:                     42
% 2.99/0.99  sup_num_of_loops:                       108
% 2.99/0.99  sup_fw_superposition:                   83
% 2.99/0.99  sup_bw_superposition:                   60
% 2.99/0.99  sup_immediate_simplified:               71
% 2.99/0.99  sup_given_eliminated:                   4
% 2.99/0.99  comparisons_done:                       0
% 2.99/0.99  comparisons_avoided:                    13
% 2.99/0.99  
% 2.99/0.99  ------ Simplifications
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  sim_fw_subset_subsumed:                 19
% 2.99/0.99  sim_bw_subset_subsumed:                 8
% 2.99/0.99  sim_fw_subsumed:                        17
% 2.99/0.99  sim_bw_subsumed:                        3
% 2.99/0.99  sim_fw_subsumption_res:                 1
% 2.99/0.99  sim_bw_subsumption_res:                 4
% 2.99/0.99  sim_tautology_del:                      2
% 2.99/0.99  sim_eq_tautology_del:                   8
% 2.99/0.99  sim_eq_res_simp:                        2
% 2.99/0.99  sim_fw_demodulated:                     22
% 2.99/0.99  sim_bw_demodulated:                     47
% 2.99/0.99  sim_light_normalised:                   49
% 2.99/0.99  sim_joinable_taut:                      0
% 2.99/0.99  sim_joinable_simp:                      0
% 2.99/0.99  sim_ac_normalised:                      0
% 2.99/0.99  sim_smt_subsumption:                    0
% 2.99/0.99  
%------------------------------------------------------------------------------
