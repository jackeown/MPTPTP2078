%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:45 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  188 (5585 expanded)
%              Number of clauses        :  119 (1714 expanded)
%              Number of leaves         :   15 (1091 expanded)
%              Depth                    :   25
%              Number of atoms          :  561 (30518 expanded)
%              Number of equality atoms :  290 (6123 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f27])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f31])).

fof(f41,plain,
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

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f41])).

fof(f75,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f12,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK0(X0,X1),X0,X1)
        & v1_funct_1(sK0(X0,X1))
        & v1_relat_1(sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK0(X0,X1),X0,X1)
      & v1_funct_1(sK0(X0,X1))
      & v1_relat_1(sK0(X0,X1))
      & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f39])).

fof(f70,plain,(
    ! [X0,X1] : v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X0,X1] : m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_649,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_651,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_34])).

cnf(c_1471,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1477,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3666,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1471,c_1477])).

cnf(c_3768,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_651,c_3666])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1476,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2957,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1471,c_1476])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2973,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2957,c_32])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_672,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_673,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_685,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_673,c_15])).

cnf(c_1459,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_674,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1757,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1758,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1765,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1766,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_1773,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1774,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1773])).

cnf(c_1868,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1459,c_37,c_39,c_674,c_1758,c_1766,c_1774])).

cnf(c_1869,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1868])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_439,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_440,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_442,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_36])).

cnf(c_1468,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1777,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1468,c_36,c_34,c_440,c_1773])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_425,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_426,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_428,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_36])).

cnf(c_1469,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1781,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1469,c_36,c_34,c_426,c_1773])).

cnf(c_1872,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1869,c_1777,c_1781])).

cnf(c_3005,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2973,c_1872])).

cnf(c_3009,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3005])).

cnf(c_4021,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3768,c_3009])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2586,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_1472])).

cnf(c_2597,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2586,c_1781])).

cnf(c_2748,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2597,c_37,c_39,c_1758,c_1766,c_1774])).

cnf(c_3003,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2973,c_2748])).

cnf(c_3943,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3768,c_3003])).

cnf(c_4085,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4021,c_3943])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1482,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3023,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2973,c_1482])).

cnf(c_3037,plain,
    ( ~ v1_relat_1(sK3)
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3023])).

cnf(c_3314,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3023,c_34,c_1773,c_3037])).

cnf(c_3315,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3314])).

cnf(c_4094,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4085,c_3315])).

cnf(c_4184,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4094])).

cnf(c_4095,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4085,c_3003])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4171,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4095,c_5])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_566,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_1464,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_1655,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1464,c_5])).

cnf(c_2042,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1655,c_37,c_39,c_1758,c_1774])).

cnf(c_2043,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2042])).

cnf(c_4104,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4085,c_2043])).

cnf(c_4142,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4104])).

cnf(c_4146,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4142,c_5])).

cnf(c_4174,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4171,c_4146])).

cnf(c_4187,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4184,c_4174])).

cnf(c_3006,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2973,c_1781])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1481,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3109,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3006,c_1481])).

cnf(c_4648,plain,
    ( k2_funct_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3109,c_37,c_39,c_1766,c_1774,c_3943,c_4021])).

cnf(c_4961,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4184,c_4648])).

cnf(c_5408,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4187,c_4961])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_24,plain,
    ( v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | X2 != X1
    | sK0(X2,X3) != X0
    | k1_xboole_0 != X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_494,plain,
    ( ~ m1_subset_1(sK0(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_27,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_504,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_494,c_27])).

cnf(c_1473,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2318,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_504,c_1473])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2327,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2318,c_4])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_114,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_116,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_2617,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2327,c_111,c_116])).

cnf(c_3670,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1477])).

cnf(c_4409,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2617,c_3670])).

cnf(c_4652,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4648,c_1777])).

cnf(c_4100,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4085,c_2973])).

cnf(c_4194,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4184,c_4100])).

cnf(c_4654,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4652,c_4194])).

cnf(c_4967,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4654,c_4184])).

cnf(c_5297,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4409,c_4967])).

cnf(c_5409,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5408,c_5297])).

cnf(c_5410,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5409])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.35/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.03  
% 3.35/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/1.03  
% 3.35/1.03  ------  iProver source info
% 3.35/1.03  
% 3.35/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.35/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/1.03  git: non_committed_changes: false
% 3.35/1.03  git: last_make_outside_of_git: false
% 3.35/1.03  
% 3.35/1.03  ------ 
% 3.35/1.03  
% 3.35/1.03  ------ Input Options
% 3.35/1.03  
% 3.35/1.03  --out_options                           all
% 3.35/1.03  --tptp_safe_out                         true
% 3.35/1.03  --problem_path                          ""
% 3.35/1.03  --include_path                          ""
% 3.35/1.03  --clausifier                            res/vclausify_rel
% 3.35/1.03  --clausifier_options                    --mode clausify
% 3.35/1.03  --stdin                                 false
% 3.35/1.03  --stats_out                             all
% 3.35/1.03  
% 3.35/1.03  ------ General Options
% 3.35/1.03  
% 3.35/1.03  --fof                                   false
% 3.35/1.03  --time_out_real                         305.
% 3.35/1.03  --time_out_virtual                      -1.
% 3.35/1.03  --symbol_type_check                     false
% 3.35/1.03  --clausify_out                          false
% 3.35/1.03  --sig_cnt_out                           false
% 3.35/1.03  --trig_cnt_out                          false
% 3.35/1.03  --trig_cnt_out_tolerance                1.
% 3.35/1.03  --trig_cnt_out_sk_spl                   false
% 3.35/1.03  --abstr_cl_out                          false
% 3.35/1.03  
% 3.35/1.03  ------ Global Options
% 3.35/1.03  
% 3.35/1.03  --schedule                              default
% 3.35/1.03  --add_important_lit                     false
% 3.35/1.03  --prop_solver_per_cl                    1000
% 3.35/1.03  --min_unsat_core                        false
% 3.35/1.03  --soft_assumptions                      false
% 3.35/1.03  --soft_lemma_size                       3
% 3.35/1.03  --prop_impl_unit_size                   0
% 3.35/1.03  --prop_impl_unit                        []
% 3.35/1.03  --share_sel_clauses                     true
% 3.35/1.03  --reset_solvers                         false
% 3.35/1.03  --bc_imp_inh                            [conj_cone]
% 3.35/1.03  --conj_cone_tolerance                   3.
% 3.35/1.03  --extra_neg_conj                        none
% 3.35/1.03  --large_theory_mode                     true
% 3.35/1.03  --prolific_symb_bound                   200
% 3.35/1.03  --lt_threshold                          2000
% 3.35/1.03  --clause_weak_htbl                      true
% 3.35/1.03  --gc_record_bc_elim                     false
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing Options
% 3.35/1.03  
% 3.35/1.03  --preprocessing_flag                    true
% 3.35/1.03  --time_out_prep_mult                    0.1
% 3.35/1.03  --splitting_mode                        input
% 3.35/1.03  --splitting_grd                         true
% 3.35/1.03  --splitting_cvd                         false
% 3.35/1.03  --splitting_cvd_svl                     false
% 3.35/1.03  --splitting_nvd                         32
% 3.35/1.03  --sub_typing                            true
% 3.35/1.03  --prep_gs_sim                           true
% 3.35/1.03  --prep_unflatten                        true
% 3.35/1.03  --prep_res_sim                          true
% 3.35/1.03  --prep_upred                            true
% 3.35/1.03  --prep_sem_filter                       exhaustive
% 3.35/1.03  --prep_sem_filter_out                   false
% 3.35/1.03  --pred_elim                             true
% 3.35/1.03  --res_sim_input                         true
% 3.35/1.03  --eq_ax_congr_red                       true
% 3.35/1.03  --pure_diseq_elim                       true
% 3.35/1.03  --brand_transform                       false
% 3.35/1.03  --non_eq_to_eq                          false
% 3.35/1.03  --prep_def_merge                        true
% 3.35/1.03  --prep_def_merge_prop_impl              false
% 3.35/1.03  --prep_def_merge_mbd                    true
% 3.35/1.03  --prep_def_merge_tr_red                 false
% 3.35/1.03  --prep_def_merge_tr_cl                  false
% 3.35/1.03  --smt_preprocessing                     true
% 3.35/1.03  --smt_ac_axioms                         fast
% 3.35/1.03  --preprocessed_out                      false
% 3.35/1.03  --preprocessed_stats                    false
% 3.35/1.03  
% 3.35/1.03  ------ Abstraction refinement Options
% 3.35/1.03  
% 3.35/1.03  --abstr_ref                             []
% 3.35/1.03  --abstr_ref_prep                        false
% 3.35/1.03  --abstr_ref_until_sat                   false
% 3.35/1.03  --abstr_ref_sig_restrict                funpre
% 3.35/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/1.03  --abstr_ref_under                       []
% 3.35/1.03  
% 3.35/1.03  ------ SAT Options
% 3.35/1.03  
% 3.35/1.03  --sat_mode                              false
% 3.35/1.03  --sat_fm_restart_options                ""
% 3.35/1.03  --sat_gr_def                            false
% 3.35/1.03  --sat_epr_types                         true
% 3.35/1.03  --sat_non_cyclic_types                  false
% 3.35/1.03  --sat_finite_models                     false
% 3.35/1.03  --sat_fm_lemmas                         false
% 3.35/1.03  --sat_fm_prep                           false
% 3.35/1.03  --sat_fm_uc_incr                        true
% 3.35/1.03  --sat_out_model                         small
% 3.35/1.03  --sat_out_clauses                       false
% 3.35/1.03  
% 3.35/1.03  ------ QBF Options
% 3.35/1.03  
% 3.35/1.03  --qbf_mode                              false
% 3.35/1.03  --qbf_elim_univ                         false
% 3.35/1.03  --qbf_dom_inst                          none
% 3.35/1.03  --qbf_dom_pre_inst                      false
% 3.35/1.03  --qbf_sk_in                             false
% 3.35/1.03  --qbf_pred_elim                         true
% 3.35/1.03  --qbf_split                             512
% 3.35/1.03  
% 3.35/1.03  ------ BMC1 Options
% 3.35/1.03  
% 3.35/1.03  --bmc1_incremental                      false
% 3.35/1.03  --bmc1_axioms                           reachable_all
% 3.35/1.03  --bmc1_min_bound                        0
% 3.35/1.03  --bmc1_max_bound                        -1
% 3.35/1.03  --bmc1_max_bound_default                -1
% 3.35/1.03  --bmc1_symbol_reachability              true
% 3.35/1.03  --bmc1_property_lemmas                  false
% 3.35/1.03  --bmc1_k_induction                      false
% 3.35/1.03  --bmc1_non_equiv_states                 false
% 3.35/1.03  --bmc1_deadlock                         false
% 3.35/1.03  --bmc1_ucm                              false
% 3.35/1.03  --bmc1_add_unsat_core                   none
% 3.35/1.03  --bmc1_unsat_core_children              false
% 3.35/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/1.03  --bmc1_out_stat                         full
% 3.35/1.03  --bmc1_ground_init                      false
% 3.35/1.03  --bmc1_pre_inst_next_state              false
% 3.35/1.03  --bmc1_pre_inst_state                   false
% 3.35/1.03  --bmc1_pre_inst_reach_state             false
% 3.35/1.03  --bmc1_out_unsat_core                   false
% 3.35/1.03  --bmc1_aig_witness_out                  false
% 3.35/1.03  --bmc1_verbose                          false
% 3.35/1.03  --bmc1_dump_clauses_tptp                false
% 3.35/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.35/1.03  --bmc1_dump_file                        -
% 3.35/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.35/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.35/1.03  --bmc1_ucm_extend_mode                  1
% 3.35/1.03  --bmc1_ucm_init_mode                    2
% 3.35/1.03  --bmc1_ucm_cone_mode                    none
% 3.35/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.35/1.03  --bmc1_ucm_relax_model                  4
% 3.35/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.35/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/1.03  --bmc1_ucm_layered_model                none
% 3.35/1.03  --bmc1_ucm_max_lemma_size               10
% 3.35/1.03  
% 3.35/1.03  ------ AIG Options
% 3.35/1.03  
% 3.35/1.03  --aig_mode                              false
% 3.35/1.03  
% 3.35/1.03  ------ Instantiation Options
% 3.35/1.03  
% 3.35/1.03  --instantiation_flag                    true
% 3.35/1.03  --inst_sos_flag                         false
% 3.35/1.03  --inst_sos_phase                        true
% 3.35/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/1.03  --inst_lit_sel_side                     num_symb
% 3.35/1.03  --inst_solver_per_active                1400
% 3.35/1.03  --inst_solver_calls_frac                1.
% 3.35/1.03  --inst_passive_queue_type               priority_queues
% 3.35/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/1.03  --inst_passive_queues_freq              [25;2]
% 3.35/1.03  --inst_dismatching                      true
% 3.35/1.03  --inst_eager_unprocessed_to_passive     true
% 3.35/1.03  --inst_prop_sim_given                   true
% 3.35/1.03  --inst_prop_sim_new                     false
% 3.35/1.03  --inst_subs_new                         false
% 3.35/1.03  --inst_eq_res_simp                      false
% 3.35/1.03  --inst_subs_given                       false
% 3.35/1.03  --inst_orphan_elimination               true
% 3.35/1.03  --inst_learning_loop_flag               true
% 3.35/1.03  --inst_learning_start                   3000
% 3.35/1.03  --inst_learning_factor                  2
% 3.35/1.03  --inst_start_prop_sim_after_learn       3
% 3.35/1.03  --inst_sel_renew                        solver
% 3.35/1.03  --inst_lit_activity_flag                true
% 3.35/1.03  --inst_restr_to_given                   false
% 3.35/1.03  --inst_activity_threshold               500
% 3.35/1.03  --inst_out_proof                        true
% 3.35/1.03  
% 3.35/1.03  ------ Resolution Options
% 3.35/1.03  
% 3.35/1.03  --resolution_flag                       true
% 3.35/1.03  --res_lit_sel                           adaptive
% 3.35/1.03  --res_lit_sel_side                      none
% 3.35/1.03  --res_ordering                          kbo
% 3.35/1.03  --res_to_prop_solver                    active
% 3.35/1.03  --res_prop_simpl_new                    false
% 3.35/1.03  --res_prop_simpl_given                  true
% 3.35/1.03  --res_passive_queue_type                priority_queues
% 3.35/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/1.03  --res_passive_queues_freq               [15;5]
% 3.35/1.03  --res_forward_subs                      full
% 3.35/1.03  --res_backward_subs                     full
% 3.35/1.03  --res_forward_subs_resolution           true
% 3.35/1.03  --res_backward_subs_resolution          true
% 3.35/1.03  --res_orphan_elimination                true
% 3.35/1.03  --res_time_limit                        2.
% 3.35/1.03  --res_out_proof                         true
% 3.35/1.03  
% 3.35/1.03  ------ Superposition Options
% 3.35/1.03  
% 3.35/1.03  --superposition_flag                    true
% 3.35/1.03  --sup_passive_queue_type                priority_queues
% 3.35/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.35/1.03  --demod_completeness_check              fast
% 3.35/1.03  --demod_use_ground                      true
% 3.35/1.03  --sup_to_prop_solver                    passive
% 3.35/1.03  --sup_prop_simpl_new                    true
% 3.35/1.03  --sup_prop_simpl_given                  true
% 3.35/1.03  --sup_fun_splitting                     false
% 3.35/1.03  --sup_smt_interval                      50000
% 3.35/1.03  
% 3.35/1.03  ------ Superposition Simplification Setup
% 3.35/1.03  
% 3.35/1.03  --sup_indices_passive                   []
% 3.35/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.03  --sup_full_bw                           [BwDemod]
% 3.35/1.03  --sup_immed_triv                        [TrivRules]
% 3.35/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.03  --sup_immed_bw_main                     []
% 3.35/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.03  
% 3.35/1.03  ------ Combination Options
% 3.35/1.03  
% 3.35/1.03  --comb_res_mult                         3
% 3.35/1.03  --comb_sup_mult                         2
% 3.35/1.03  --comb_inst_mult                        10
% 3.35/1.03  
% 3.35/1.03  ------ Debug Options
% 3.35/1.03  
% 3.35/1.03  --dbg_backtrace                         false
% 3.35/1.03  --dbg_dump_prop_clauses                 false
% 3.35/1.03  --dbg_dump_prop_clauses_file            -
% 3.35/1.03  --dbg_out_stat                          false
% 3.35/1.03  ------ Parsing...
% 3.35/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  ------ Proving...
% 3.35/1.03  ------ Problem Properties 
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  clauses                                 38
% 3.35/1.03  conjectures                             3
% 3.35/1.03  EPR                                     4
% 3.35/1.03  Horn                                    32
% 3.35/1.03  unary                                   11
% 3.35/1.03  binary                                  10
% 3.35/1.03  lits                                    93
% 3.35/1.03  lits eq                                 43
% 3.35/1.03  fd_pure                                 0
% 3.35/1.03  fd_pseudo                               0
% 3.35/1.03  fd_cond                                 4
% 3.35/1.03  fd_pseudo_cond                          1
% 3.35/1.03  AC symbols                              0
% 3.35/1.03  
% 3.35/1.03  ------ Schedule dynamic 5 is on 
% 3.35/1.03  
% 3.35/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ 
% 3.35/1.03  Current options:
% 3.35/1.03  ------ 
% 3.35/1.03  
% 3.35/1.03  ------ Input Options
% 3.35/1.03  
% 3.35/1.03  --out_options                           all
% 3.35/1.03  --tptp_safe_out                         true
% 3.35/1.03  --problem_path                          ""
% 3.35/1.03  --include_path                          ""
% 3.35/1.03  --clausifier                            res/vclausify_rel
% 3.35/1.03  --clausifier_options                    --mode clausify
% 3.35/1.03  --stdin                                 false
% 3.35/1.03  --stats_out                             all
% 3.35/1.03  
% 3.35/1.03  ------ General Options
% 3.35/1.03  
% 3.35/1.03  --fof                                   false
% 3.35/1.03  --time_out_real                         305.
% 3.35/1.03  --time_out_virtual                      -1.
% 3.35/1.03  --symbol_type_check                     false
% 3.35/1.03  --clausify_out                          false
% 3.35/1.03  --sig_cnt_out                           false
% 3.35/1.03  --trig_cnt_out                          false
% 3.35/1.03  --trig_cnt_out_tolerance                1.
% 3.35/1.03  --trig_cnt_out_sk_spl                   false
% 3.35/1.03  --abstr_cl_out                          false
% 3.35/1.03  
% 3.35/1.03  ------ Global Options
% 3.35/1.03  
% 3.35/1.03  --schedule                              default
% 3.35/1.03  --add_important_lit                     false
% 3.35/1.03  --prop_solver_per_cl                    1000
% 3.35/1.03  --min_unsat_core                        false
% 3.35/1.03  --soft_assumptions                      false
% 3.35/1.03  --soft_lemma_size                       3
% 3.35/1.03  --prop_impl_unit_size                   0
% 3.35/1.03  --prop_impl_unit                        []
% 3.35/1.03  --share_sel_clauses                     true
% 3.35/1.03  --reset_solvers                         false
% 3.35/1.03  --bc_imp_inh                            [conj_cone]
% 3.35/1.03  --conj_cone_tolerance                   3.
% 3.35/1.03  --extra_neg_conj                        none
% 3.35/1.03  --large_theory_mode                     true
% 3.35/1.03  --prolific_symb_bound                   200
% 3.35/1.03  --lt_threshold                          2000
% 3.35/1.03  --clause_weak_htbl                      true
% 3.35/1.03  --gc_record_bc_elim                     false
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing Options
% 3.35/1.03  
% 3.35/1.03  --preprocessing_flag                    true
% 3.35/1.03  --time_out_prep_mult                    0.1
% 3.35/1.03  --splitting_mode                        input
% 3.35/1.03  --splitting_grd                         true
% 3.35/1.03  --splitting_cvd                         false
% 3.35/1.03  --splitting_cvd_svl                     false
% 3.35/1.03  --splitting_nvd                         32
% 3.35/1.03  --sub_typing                            true
% 3.35/1.03  --prep_gs_sim                           true
% 3.35/1.03  --prep_unflatten                        true
% 3.35/1.03  --prep_res_sim                          true
% 3.35/1.03  --prep_upred                            true
% 3.35/1.03  --prep_sem_filter                       exhaustive
% 3.35/1.03  --prep_sem_filter_out                   false
% 3.35/1.03  --pred_elim                             true
% 3.35/1.03  --res_sim_input                         true
% 3.35/1.03  --eq_ax_congr_red                       true
% 3.35/1.03  --pure_diseq_elim                       true
% 3.35/1.03  --brand_transform                       false
% 3.35/1.03  --non_eq_to_eq                          false
% 3.35/1.03  --prep_def_merge                        true
% 3.35/1.03  --prep_def_merge_prop_impl              false
% 3.35/1.03  --prep_def_merge_mbd                    true
% 3.35/1.03  --prep_def_merge_tr_red                 false
% 3.35/1.03  --prep_def_merge_tr_cl                  false
% 3.35/1.03  --smt_preprocessing                     true
% 3.35/1.03  --smt_ac_axioms                         fast
% 3.35/1.03  --preprocessed_out                      false
% 3.35/1.03  --preprocessed_stats                    false
% 3.35/1.03  
% 3.35/1.03  ------ Abstraction refinement Options
% 3.35/1.03  
% 3.35/1.03  --abstr_ref                             []
% 3.35/1.03  --abstr_ref_prep                        false
% 3.35/1.03  --abstr_ref_until_sat                   false
% 3.35/1.03  --abstr_ref_sig_restrict                funpre
% 3.35/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/1.03  --abstr_ref_under                       []
% 3.35/1.03  
% 3.35/1.03  ------ SAT Options
% 3.35/1.03  
% 3.35/1.03  --sat_mode                              false
% 3.35/1.03  --sat_fm_restart_options                ""
% 3.35/1.03  --sat_gr_def                            false
% 3.35/1.03  --sat_epr_types                         true
% 3.35/1.03  --sat_non_cyclic_types                  false
% 3.35/1.03  --sat_finite_models                     false
% 3.35/1.03  --sat_fm_lemmas                         false
% 3.35/1.03  --sat_fm_prep                           false
% 3.35/1.03  --sat_fm_uc_incr                        true
% 3.35/1.03  --sat_out_model                         small
% 3.35/1.03  --sat_out_clauses                       false
% 3.35/1.03  
% 3.35/1.03  ------ QBF Options
% 3.35/1.03  
% 3.35/1.03  --qbf_mode                              false
% 3.35/1.03  --qbf_elim_univ                         false
% 3.35/1.03  --qbf_dom_inst                          none
% 3.35/1.03  --qbf_dom_pre_inst                      false
% 3.35/1.03  --qbf_sk_in                             false
% 3.35/1.03  --qbf_pred_elim                         true
% 3.35/1.03  --qbf_split                             512
% 3.35/1.03  
% 3.35/1.03  ------ BMC1 Options
% 3.35/1.03  
% 3.35/1.03  --bmc1_incremental                      false
% 3.35/1.03  --bmc1_axioms                           reachable_all
% 3.35/1.03  --bmc1_min_bound                        0
% 3.35/1.03  --bmc1_max_bound                        -1
% 3.35/1.03  --bmc1_max_bound_default                -1
% 3.35/1.03  --bmc1_symbol_reachability              true
% 3.35/1.03  --bmc1_property_lemmas                  false
% 3.35/1.03  --bmc1_k_induction                      false
% 3.35/1.03  --bmc1_non_equiv_states                 false
% 3.35/1.03  --bmc1_deadlock                         false
% 3.35/1.03  --bmc1_ucm                              false
% 3.35/1.03  --bmc1_add_unsat_core                   none
% 3.35/1.03  --bmc1_unsat_core_children              false
% 3.35/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/1.03  --bmc1_out_stat                         full
% 3.35/1.03  --bmc1_ground_init                      false
% 3.35/1.03  --bmc1_pre_inst_next_state              false
% 3.35/1.03  --bmc1_pre_inst_state                   false
% 3.35/1.03  --bmc1_pre_inst_reach_state             false
% 3.35/1.03  --bmc1_out_unsat_core                   false
% 3.35/1.03  --bmc1_aig_witness_out                  false
% 3.35/1.03  --bmc1_verbose                          false
% 3.35/1.03  --bmc1_dump_clauses_tptp                false
% 3.35/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.35/1.03  --bmc1_dump_file                        -
% 3.35/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.35/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.35/1.03  --bmc1_ucm_extend_mode                  1
% 3.35/1.03  --bmc1_ucm_init_mode                    2
% 3.35/1.03  --bmc1_ucm_cone_mode                    none
% 3.35/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.35/1.03  --bmc1_ucm_relax_model                  4
% 3.35/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.35/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/1.03  --bmc1_ucm_layered_model                none
% 3.35/1.03  --bmc1_ucm_max_lemma_size               10
% 3.35/1.03  
% 3.35/1.03  ------ AIG Options
% 3.35/1.03  
% 3.35/1.03  --aig_mode                              false
% 3.35/1.03  
% 3.35/1.03  ------ Instantiation Options
% 3.35/1.03  
% 3.35/1.03  --instantiation_flag                    true
% 3.35/1.03  --inst_sos_flag                         false
% 3.35/1.03  --inst_sos_phase                        true
% 3.35/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/1.03  --inst_lit_sel_side                     none
% 3.35/1.03  --inst_solver_per_active                1400
% 3.35/1.03  --inst_solver_calls_frac                1.
% 3.35/1.03  --inst_passive_queue_type               priority_queues
% 3.35/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/1.03  --inst_passive_queues_freq              [25;2]
% 3.35/1.03  --inst_dismatching                      true
% 3.35/1.03  --inst_eager_unprocessed_to_passive     true
% 3.35/1.03  --inst_prop_sim_given                   true
% 3.35/1.03  --inst_prop_sim_new                     false
% 3.35/1.03  --inst_subs_new                         false
% 3.35/1.03  --inst_eq_res_simp                      false
% 3.35/1.03  --inst_subs_given                       false
% 3.35/1.03  --inst_orphan_elimination               true
% 3.35/1.03  --inst_learning_loop_flag               true
% 3.35/1.03  --inst_learning_start                   3000
% 3.35/1.03  --inst_learning_factor                  2
% 3.35/1.03  --inst_start_prop_sim_after_learn       3
% 3.35/1.03  --inst_sel_renew                        solver
% 3.35/1.03  --inst_lit_activity_flag                true
% 3.35/1.03  --inst_restr_to_given                   false
% 3.35/1.03  --inst_activity_threshold               500
% 3.35/1.03  --inst_out_proof                        true
% 3.35/1.03  
% 3.35/1.03  ------ Resolution Options
% 3.35/1.03  
% 3.35/1.03  --resolution_flag                       false
% 3.35/1.03  --res_lit_sel                           adaptive
% 3.35/1.03  --res_lit_sel_side                      none
% 3.35/1.03  --res_ordering                          kbo
% 3.35/1.03  --res_to_prop_solver                    active
% 3.35/1.03  --res_prop_simpl_new                    false
% 3.35/1.03  --res_prop_simpl_given                  true
% 3.35/1.03  --res_passive_queue_type                priority_queues
% 3.35/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/1.03  --res_passive_queues_freq               [15;5]
% 3.35/1.03  --res_forward_subs                      full
% 3.35/1.03  --res_backward_subs                     full
% 3.35/1.03  --res_forward_subs_resolution           true
% 3.35/1.03  --res_backward_subs_resolution          true
% 3.35/1.03  --res_orphan_elimination                true
% 3.35/1.03  --res_time_limit                        2.
% 3.35/1.03  --res_out_proof                         true
% 3.35/1.03  
% 3.35/1.03  ------ Superposition Options
% 3.35/1.03  
% 3.35/1.03  --superposition_flag                    true
% 3.35/1.03  --sup_passive_queue_type                priority_queues
% 3.35/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.35/1.03  --demod_completeness_check              fast
% 3.35/1.03  --demod_use_ground                      true
% 3.35/1.03  --sup_to_prop_solver                    passive
% 3.35/1.03  --sup_prop_simpl_new                    true
% 3.35/1.03  --sup_prop_simpl_given                  true
% 3.35/1.03  --sup_fun_splitting                     false
% 3.35/1.03  --sup_smt_interval                      50000
% 3.35/1.03  
% 3.35/1.03  ------ Superposition Simplification Setup
% 3.35/1.03  
% 3.35/1.03  --sup_indices_passive                   []
% 3.35/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.03  --sup_full_bw                           [BwDemod]
% 3.35/1.03  --sup_immed_triv                        [TrivRules]
% 3.35/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.03  --sup_immed_bw_main                     []
% 3.35/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/1.03  
% 3.35/1.03  ------ Combination Options
% 3.35/1.03  
% 3.35/1.03  --comb_res_mult                         3
% 3.35/1.03  --comb_sup_mult                         2
% 3.35/1.03  --comb_inst_mult                        10
% 3.35/1.03  
% 3.35/1.03  ------ Debug Options
% 3.35/1.03  
% 3.35/1.03  --dbg_backtrace                         false
% 3.35/1.03  --dbg_dump_prop_clauses                 false
% 3.35/1.03  --dbg_dump_prop_clauses_file            -
% 3.35/1.03  --dbg_out_stat                          false
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  % SZS status Theorem for theBenchmark.p
% 3.35/1.03  
% 3.35/1.03   Resolution empty clause
% 3.35/1.03  
% 3.35/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/1.03  
% 3.35/1.03  fof(f11,axiom,(
% 3.35/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f27,plain,(
% 3.35/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(ennf_transformation,[],[f11])).
% 3.35/1.03  
% 3.35/1.03  fof(f28,plain,(
% 3.35/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(flattening,[],[f27])).
% 3.35/1.03  
% 3.35/1.03  fof(f38,plain,(
% 3.35/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(nnf_transformation,[],[f28])).
% 3.35/1.03  
% 3.35/1.03  fof(f61,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f38])).
% 3.35/1.03  
% 3.35/1.03  fof(f14,conjecture,(
% 3.35/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f15,negated_conjecture,(
% 3.35/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.35/1.03    inference(negated_conjecture,[],[f14])).
% 3.35/1.03  
% 3.35/1.03  fof(f31,plain,(
% 3.35/1.03    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.35/1.03    inference(ennf_transformation,[],[f15])).
% 3.35/1.03  
% 3.35/1.03  fof(f32,plain,(
% 3.35/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.35/1.03    inference(flattening,[],[f31])).
% 3.35/1.03  
% 3.35/1.03  fof(f41,plain,(
% 3.35/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.35/1.03    introduced(choice_axiom,[])).
% 3.35/1.03  
% 3.35/1.03  fof(f42,plain,(
% 3.35/1.03    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.35/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f41])).
% 3.35/1.03  
% 3.35/1.03  fof(f75,plain,(
% 3.35/1.03    v1_funct_2(sK3,sK1,sK2)),
% 3.35/1.03    inference(cnf_transformation,[],[f42])).
% 3.35/1.03  
% 3.35/1.03  fof(f76,plain,(
% 3.35/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.35/1.03    inference(cnf_transformation,[],[f42])).
% 3.35/1.03  
% 3.35/1.03  fof(f9,axiom,(
% 3.35/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f25,plain,(
% 3.35/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(ennf_transformation,[],[f9])).
% 3.35/1.03  
% 3.35/1.03  fof(f59,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f25])).
% 3.35/1.03  
% 3.35/1.03  fof(f10,axiom,(
% 3.35/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f26,plain,(
% 3.35/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(ennf_transformation,[],[f10])).
% 3.35/1.03  
% 3.35/1.03  fof(f60,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f26])).
% 3.35/1.03  
% 3.35/1.03  fof(f78,plain,(
% 3.35/1.03    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.35/1.03    inference(cnf_transformation,[],[f42])).
% 3.35/1.03  
% 3.35/1.03  fof(f13,axiom,(
% 3.35/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f29,plain,(
% 3.35/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/1.03    inference(ennf_transformation,[],[f13])).
% 3.35/1.03  
% 3.35/1.03  fof(f30,plain,(
% 3.35/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/1.03    inference(flattening,[],[f29])).
% 3.35/1.03  
% 3.35/1.03  fof(f72,plain,(
% 3.35/1.03    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f30])).
% 3.35/1.03  
% 3.35/1.03  fof(f79,plain,(
% 3.35/1.03    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.35/1.03    inference(cnf_transformation,[],[f42])).
% 3.35/1.03  
% 3.35/1.03  fof(f8,axiom,(
% 3.35/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f24,plain,(
% 3.35/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(ennf_transformation,[],[f8])).
% 3.35/1.03  
% 3.35/1.03  fof(f58,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f24])).
% 3.35/1.03  
% 3.35/1.03  fof(f74,plain,(
% 3.35/1.03    v1_funct_1(sK3)),
% 3.35/1.03    inference(cnf_transformation,[],[f42])).
% 3.35/1.03  
% 3.35/1.03  fof(f6,axiom,(
% 3.35/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f20,plain,(
% 3.35/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/1.03    inference(ennf_transformation,[],[f6])).
% 3.35/1.03  
% 3.35/1.03  fof(f21,plain,(
% 3.35/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/1.03    inference(flattening,[],[f20])).
% 3.35/1.03  
% 3.35/1.03  fof(f55,plain,(
% 3.35/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f21])).
% 3.35/1.03  
% 3.35/1.03  fof(f54,plain,(
% 3.35/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f21])).
% 3.35/1.03  
% 3.35/1.03  fof(f7,axiom,(
% 3.35/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f22,plain,(
% 3.35/1.03    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.35/1.03    inference(ennf_transformation,[],[f7])).
% 3.35/1.03  
% 3.35/1.03  fof(f23,plain,(
% 3.35/1.03    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.35/1.03    inference(flattening,[],[f22])).
% 3.35/1.03  
% 3.35/1.03  fof(f57,plain,(
% 3.35/1.03    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f23])).
% 3.35/1.03  
% 3.35/1.03  fof(f77,plain,(
% 3.35/1.03    v2_funct_1(sK3)),
% 3.35/1.03    inference(cnf_transformation,[],[f42])).
% 3.35/1.03  
% 3.35/1.03  fof(f56,plain,(
% 3.35/1.03    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f23])).
% 3.35/1.03  
% 3.35/1.03  fof(f73,plain,(
% 3.35/1.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f30])).
% 3.35/1.03  
% 3.35/1.03  fof(f5,axiom,(
% 3.35/1.03    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f18,plain,(
% 3.35/1.03    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.35/1.03    inference(ennf_transformation,[],[f5])).
% 3.35/1.03  
% 3.35/1.03  fof(f19,plain,(
% 3.35/1.03    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.35/1.03    inference(flattening,[],[f18])).
% 3.35/1.03  
% 3.35/1.03  fof(f53,plain,(
% 3.35/1.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f19])).
% 3.35/1.03  
% 3.35/1.03  fof(f3,axiom,(
% 3.35/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f35,plain,(
% 3.35/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/1.03    inference(nnf_transformation,[],[f3])).
% 3.35/1.03  
% 3.35/1.03  fof(f36,plain,(
% 3.35/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/1.03    inference(flattening,[],[f35])).
% 3.35/1.03  
% 3.35/1.03  fof(f48,plain,(
% 3.35/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.35/1.03    inference(cnf_transformation,[],[f36])).
% 3.35/1.03  
% 3.35/1.03  fof(f83,plain,(
% 3.35/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.35/1.03    inference(equality_resolution,[],[f48])).
% 3.35/1.03  
% 3.35/1.03  fof(f64,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f38])).
% 3.35/1.03  
% 3.35/1.03  fof(f87,plain,(
% 3.35/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.35/1.03    inference(equality_resolution,[],[f64])).
% 3.35/1.03  
% 3.35/1.03  fof(f52,plain,(
% 3.35/1.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f19])).
% 3.35/1.03  
% 3.35/1.03  fof(f65,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f38])).
% 3.35/1.03  
% 3.35/1.03  fof(f86,plain,(
% 3.35/1.03    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.35/1.03    inference(equality_resolution,[],[f65])).
% 3.35/1.03  
% 3.35/1.03  fof(f12,axiom,(
% 3.35/1.03    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f16,plain,(
% 3.35/1.03    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(pure_predicate_removal,[],[f12])).
% 3.35/1.03  
% 3.35/1.03  fof(f17,plain,(
% 3.35/1.03    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(pure_predicate_removal,[],[f16])).
% 3.35/1.03  
% 3.35/1.03  fof(f39,plain,(
% 3.35/1.03    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.35/1.03    introduced(choice_axiom,[])).
% 3.35/1.03  
% 3.35/1.03  fof(f40,plain,(
% 3.35/1.03    ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f39])).
% 3.35/1.03  
% 3.35/1.03  fof(f70,plain,(
% 3.35/1.03    ( ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f40])).
% 3.35/1.03  
% 3.35/1.03  fof(f67,plain,(
% 3.35/1.03    ( ! [X0,X1] : (m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f40])).
% 3.35/1.03  
% 3.35/1.03  fof(f49,plain,(
% 3.35/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.35/1.03    inference(cnf_transformation,[],[f36])).
% 3.35/1.03  
% 3.35/1.03  fof(f82,plain,(
% 3.35/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.35/1.03    inference(equality_resolution,[],[f49])).
% 3.35/1.03  
% 3.35/1.03  fof(f4,axiom,(
% 3.35/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f37,plain,(
% 3.35/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.35/1.03    inference(nnf_transformation,[],[f4])).
% 3.35/1.03  
% 3.35/1.03  fof(f51,plain,(
% 3.35/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f37])).
% 3.35/1.03  
% 3.35/1.03  fof(f2,axiom,(
% 3.35/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f46,plain,(
% 3.35/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f2])).
% 3.35/1.03  
% 3.35/1.03  cnf(c_23,plain,
% 3.35/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.35/1.03      | k1_xboole_0 = X2 ),
% 3.35/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_35,negated_conjecture,
% 3.35/1.03      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.35/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_648,plain,
% 3.35/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.35/1.03      | sK1 != X1
% 3.35/1.03      | sK2 != X2
% 3.35/1.03      | sK3 != X0
% 3.35/1.03      | k1_xboole_0 = X2 ),
% 3.35/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_649,plain,
% 3.35/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.35/1.03      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.35/1.03      | k1_xboole_0 = sK2 ),
% 3.35/1.03      inference(unflattening,[status(thm)],[c_648]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_34,negated_conjecture,
% 3.35/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.35/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_651,plain,
% 3.35/1.03      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.35/1.03      inference(global_propositional_subsumption,[status(thm)],[c_649,c_34]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1471,plain,
% 3.35/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_16,plain,
% 3.35/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1477,plain,
% 3.35/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.35/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3666,plain,
% 3.35/1.03      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_1471,c_1477]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3768,plain,
% 3.35/1.03      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_651,c_3666]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_17,plain,
% 3.35/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1476,plain,
% 3.35/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.35/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2957,plain,
% 3.35/1.03      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_1471,c_1476]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_32,negated_conjecture,
% 3.35/1.03      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.35/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2973,plain,
% 3.35/1.03      ( k2_relat_1(sK3) = sK2 ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_2957,c_32]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_29,plain,
% 3.35/1.03      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.35/1.03      | ~ v1_funct_1(X0)
% 3.35/1.03      | ~ v1_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_31,negated_conjecture,
% 3.35/1.03      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.35/1.03      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.35/1.03      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.35/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_672,plain,
% 3.35/1.03      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.35/1.03      | ~ v1_funct_1(X0)
% 3.35/1.03      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.35/1.03      | ~ v1_relat_1(X0)
% 3.35/1.03      | k2_funct_1(sK3) != X0
% 3.35/1.03      | k1_relat_1(X0) != sK2
% 3.35/1.03      | k2_relat_1(X0) != sK1 ),
% 3.35/1.03      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_673,plain,
% 3.35/1.03      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.35/1.03      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.35/1.03      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.35/1.03      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.35/1.03      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.35/1.03      inference(unflattening,[status(thm)],[c_672]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_15,plain,
% 3.35/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_685,plain,
% 3.35/1.03      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.35/1.03      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.35/1.03      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.35/1.03      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.35/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_673,c_15]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1459,plain,
% 3.35/1.03      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.35/1.03      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.35/1.03      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_36,negated_conjecture,
% 3.35/1.03      ( v1_funct_1(sK3) ),
% 3.35/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_37,plain,
% 3.35/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_39,plain,
% 3.35/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_674,plain,
% 3.35/1.03      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.35/1.03      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.35/1.03      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.35/1.03      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_11,plain,
% 3.35/1.03      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1757,plain,
% 3.35/1.03      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.35/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1758,plain,
% 3.35/1.03      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.35/1.03      | v1_funct_1(sK3) != iProver_top
% 3.35/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_12,plain,
% 3.35/1.03      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.35/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1765,plain,
% 3.35/1.03      ( ~ v1_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.35/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1766,plain,
% 3.35/1.03      ( v1_funct_1(sK3) != iProver_top
% 3.35/1.03      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.35/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1773,plain,
% 3.35/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.35/1.03      | v1_relat_1(sK3) ),
% 3.35/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1774,plain,
% 3.35/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.35/1.03      | v1_relat_1(sK3) = iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_1773]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1868,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.35/1.03      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.35/1.03      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_1459,c_37,c_39,c_674,c_1758,c_1766,c_1774]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1869,plain,
% 3.35/1.03      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.35/1.03      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.35/1.03      inference(renaming,[status(thm)],[c_1868]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_13,plain,
% 3.35/1.03      ( ~ v2_funct_1(X0)
% 3.35/1.03      | ~ v1_funct_1(X0)
% 3.35/1.03      | ~ v1_relat_1(X0)
% 3.35/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_33,negated_conjecture,
% 3.35/1.03      ( v2_funct_1(sK3) ),
% 3.35/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_439,plain,
% 3.35/1.03      ( ~ v1_funct_1(X0)
% 3.35/1.03      | ~ v1_relat_1(X0)
% 3.35/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.35/1.03      | sK3 != X0 ),
% 3.35/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_33]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_440,plain,
% 3.35/1.03      ( ~ v1_funct_1(sK3)
% 3.35/1.03      | ~ v1_relat_1(sK3)
% 3.35/1.03      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.35/1.03      inference(unflattening,[status(thm)],[c_439]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_442,plain,
% 3.35/1.03      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.35/1.03      inference(global_propositional_subsumption,[status(thm)],[c_440,c_36]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1468,plain,
% 3.35/1.03      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.35/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1777,plain,
% 3.35/1.03      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_1468,c_36,c_34,c_440,c_1773]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_14,plain,
% 3.35/1.03      ( ~ v2_funct_1(X0)
% 3.35/1.03      | ~ v1_funct_1(X0)
% 3.35/1.03      | ~ v1_relat_1(X0)
% 3.35/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_425,plain,
% 3.35/1.03      ( ~ v1_funct_1(X0)
% 3.35/1.03      | ~ v1_relat_1(X0)
% 3.35/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.35/1.03      | sK3 != X0 ),
% 3.35/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_33]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_426,plain,
% 3.35/1.03      ( ~ v1_funct_1(sK3)
% 3.35/1.03      | ~ v1_relat_1(sK3)
% 3.35/1.03      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.35/1.03      inference(unflattening,[status(thm)],[c_425]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_428,plain,
% 3.35/1.03      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.35/1.03      inference(global_propositional_subsumption,[status(thm)],[c_426,c_36]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1469,plain,
% 3.35/1.03      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.35/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1781,plain,
% 3.35/1.03      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_1469,c_36,c_34,c_426,c_1773]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1872,plain,
% 3.35/1.03      ( k1_relat_1(sK3) != sK1
% 3.35/1.03      | k2_relat_1(sK3) != sK2
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_1869,c_1777,c_1781]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3005,plain,
% 3.35/1.03      ( k1_relat_1(sK3) != sK1
% 3.35/1.03      | sK2 != sK2
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_2973,c_1872]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3009,plain,
% 3.35/1.03      ( k1_relat_1(sK3) != sK1
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.35/1.03      inference(equality_resolution_simp,[status(thm)],[c_3005]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4021,plain,
% 3.35/1.03      ( sK2 = k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_3768,c_3009]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_28,plain,
% 3.35/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.35/1.03      | ~ v1_funct_1(X0)
% 3.35/1.03      | ~ v1_relat_1(X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1472,plain,
% 3.35/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.35/1.03      | v1_funct_1(X0) != iProver_top
% 3.35/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2586,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.35/1.03      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.35/1.03      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_1777,c_1472]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2597,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
% 3.35/1.03      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.35/1.03      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_2586,c_1781]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2748,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_2597,c_37,c_39,c_1758,c_1766,c_1774]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3003,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_2973,c_2748]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3943,plain,
% 3.35/1.03      ( sK2 = k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_3768,c_3003]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4085,plain,
% 3.35/1.03      ( sK2 = k1_xboole_0 ),
% 3.35/1.03      inference(global_propositional_subsumption,[status(thm)],[c_4021,c_3943]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_9,plain,
% 3.35/1.03      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.35/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1482,plain,
% 3.35/1.03      ( k2_relat_1(X0) != k1_xboole_0
% 3.35/1.03      | k1_xboole_0 = X0
% 3.35/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3023,plain,
% 3.35/1.03      ( sK2 != k1_xboole_0
% 3.35/1.03      | sK3 = k1_xboole_0
% 3.35/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_2973,c_1482]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3037,plain,
% 3.35/1.03      ( ~ v1_relat_1(sK3) | sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.35/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3023]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3314,plain,
% 3.35/1.03      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_3023,c_34,c_1773,c_3037]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3315,plain,
% 3.35/1.03      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.35/1.03      inference(renaming,[status(thm)],[c_3314]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4094,plain,
% 3.35/1.03      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4085,c_3315]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4184,plain,
% 3.35/1.03      ( sK3 = k1_xboole_0 ),
% 3.35/1.03      inference(equality_resolution_simp,[status(thm)],[c_4094]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4095,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4085,c_3003]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_5,plain,
% 3.35/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.35/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4171,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4095,c_5]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_20,plain,
% 3.35/1.03      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.35/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.35/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.35/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_565,plain,
% 3.35/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.35/1.03      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.35/1.03      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.35/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.35/1.03      | k2_funct_1(sK3) != X0
% 3.35/1.03      | sK1 != X1
% 3.35/1.03      | sK2 != k1_xboole_0 ),
% 3.35/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_566,plain,
% 3.35/1.03      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.35/1.03      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.35/1.03      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.35/1.03      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.35/1.03      | sK2 != k1_xboole_0 ),
% 3.35/1.03      inference(unflattening,[status(thm)],[c_565]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1464,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.35/1.03      | sK2 != k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.35/1.03      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1655,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.35/1.03      | sK2 != k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.35/1.03      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_1464,c_5]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2042,plain,
% 3.35/1.03      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.35/1.03      | sK2 != k1_xboole_0
% 3.35/1.03      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_1655,c_37,c_39,c_1758,c_1774]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2043,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.35/1.03      | sK2 != k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.35/1.03      inference(renaming,[status(thm)],[c_2042]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4104,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.35/1.03      | k1_xboole_0 != k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4085,c_2043]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4142,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.35/1.03      inference(equality_resolution_simp,[status(thm)],[c_4104]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4146,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.35/1.03      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4142,c_5]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4174,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.35/1.03      inference(backward_subsumption_resolution,[status(thm)],[c_4171,c_4146]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4187,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4184,c_4174]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3006,plain,
% 3.35/1.03      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_2973,c_1781]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_10,plain,
% 3.35/1.03      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.35/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1481,plain,
% 3.35/1.03      ( k1_relat_1(X0) != k1_xboole_0
% 3.35/1.03      | k1_xboole_0 = X0
% 3.35/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3109,plain,
% 3.35/1.03      ( k2_funct_1(sK3) = k1_xboole_0
% 3.35/1.03      | sK2 != k1_xboole_0
% 3.35/1.03      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_3006,c_1481]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4648,plain,
% 3.35/1.03      ( k2_funct_1(sK3) = k1_xboole_0 ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_3109,c_37,c_39,c_1766,c_1774,c_3943,c_4021]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4961,plain,
% 3.35/1.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4184,c_4648]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_5408,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_4187,c_4961]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_19,plain,
% 3.35/1.03      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.35/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.35/1.03      | k1_xboole_0 = X1
% 3.35/1.03      | k1_xboole_0 = X0 ),
% 3.35/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_24,plain,
% 3.35/1.03      ( v1_funct_2(sK0(X0,X1),X0,X1) ),
% 3.35/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_493,plain,
% 3.35/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.35/1.03      | X2 != X1
% 3.35/1.03      | sK0(X2,X3) != X0
% 3.35/1.03      | k1_xboole_0 != X3
% 3.35/1.03      | k1_xboole_0 = X1
% 3.35/1.03      | k1_xboole_0 = X0 ),
% 3.35/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_494,plain,
% 3.35/1.03      ( ~ m1_subset_1(sK0(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.35/1.03      | k1_xboole_0 = X0
% 3.35/1.03      | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
% 3.35/1.03      inference(unflattening,[status(thm)],[c_493]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_27,plain,
% 3.35/1.03      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.35/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_504,plain,
% 3.35/1.03      ( k1_xboole_0 = X0 | k1_xboole_0 = sK0(X0,k1_xboole_0) ),
% 3.35/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_494,c_27]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_1473,plain,
% 3.35/1.03      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2318,plain,
% 3.35/1.03      ( k1_xboole_0 = X0
% 3.35/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_504,c_1473]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4,plain,
% 3.35/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2327,plain,
% 3.35/1.03      ( k1_xboole_0 = X0
% 3.35/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_2318,c_4]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_7,plain,
% 3.35/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.35/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_109,plain,
% 3.35/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.35/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_111,plain,
% 3.35/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.35/1.03      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.35/1.03      inference(instantiation,[status(thm)],[c_109]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3,plain,
% 3.35/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.35/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_114,plain,
% 3.35/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.35/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_116,plain,
% 3.35/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.35/1.03      inference(instantiation,[status(thm)],[c_114]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_2617,plain,
% 3.35/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.35/1.03      inference(global_propositional_subsumption,
% 3.35/1.03                [status(thm)],
% 3.35/1.03                [c_2327,c_111,c_116]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_3670,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.35/1.03      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_5,c_1477]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4409,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.35/1.03      inference(superposition,[status(thm)],[c_2617,c_3670]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4652,plain,
% 3.35/1.03      ( k1_relat_1(sK3) = k2_relat_1(k1_xboole_0) ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4648,c_1777]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4100,plain,
% 3.35/1.03      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4085,c_2973]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4194,plain,
% 3.35/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_4184,c_4100]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4654,plain,
% 3.35/1.03      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_4652,c_4194]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_4967,plain,
% 3.35/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_4654,c_4184]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_5297,plain,
% 3.35/1.03      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.03      inference(light_normalisation,[status(thm)],[c_4409,c_4967]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_5409,plain,
% 3.35/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 3.35/1.03      inference(demodulation,[status(thm)],[c_5408,c_5297]) ).
% 3.35/1.03  
% 3.35/1.03  cnf(c_5410,plain,
% 3.35/1.03      ( $false ),
% 3.35/1.03      inference(equality_resolution_simp,[status(thm)],[c_5409]) ).
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/1.03  
% 3.35/1.03  ------                               Statistics
% 3.35/1.03  
% 3.35/1.03  ------ General
% 3.35/1.03  
% 3.35/1.03  abstr_ref_over_cycles:                  0
% 3.35/1.03  abstr_ref_under_cycles:                 0
% 3.35/1.03  gc_basic_clause_elim:                   0
% 3.35/1.03  forced_gc_time:                         0
% 3.35/1.03  parsing_time:                           0.009
% 3.35/1.03  unif_index_cands_time:                  0.
% 3.35/1.03  unif_index_add_time:                    0.
% 3.35/1.03  orderings_time:                         0.
% 3.35/1.03  out_proof_time:                         0.015
% 3.35/1.03  total_time:                             0.204
% 3.35/1.03  num_of_symbols:                         49
% 3.35/1.03  num_of_terms:                           3802
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing
% 3.35/1.03  
% 3.35/1.03  num_of_splits:                          0
% 3.35/1.03  num_of_split_atoms:                     0
% 3.35/1.03  num_of_reused_defs:                     0
% 3.35/1.03  num_eq_ax_congr_red:                    6
% 3.35/1.03  num_of_sem_filtered_clauses:            1
% 3.35/1.03  num_of_subtypes:                        0
% 3.35/1.03  monotx_restored_types:                  0
% 3.35/1.03  sat_num_of_epr_types:                   0
% 3.35/1.03  sat_num_of_non_cyclic_types:            0
% 3.35/1.03  sat_guarded_non_collapsed_types:        0
% 3.35/1.03  num_pure_diseq_elim:                    0
% 3.35/1.03  simp_replaced_by:                       0
% 3.35/1.03  res_preprocessed:                       140
% 3.35/1.03  prep_upred:                             0
% 3.35/1.03  prep_unflattend:                        54
% 3.35/1.03  smt_new_axioms:                         0
% 3.35/1.03  pred_elim_cands:                        6
% 3.35/1.03  pred_elim:                              2
% 3.35/1.03  pred_elim_cl:                           -3
% 3.35/1.03  pred_elim_cycles:                       3
% 3.35/1.03  merged_defs:                            6
% 3.35/1.03  merged_defs_ncl:                        0
% 3.35/1.03  bin_hyper_res:                          6
% 3.35/1.03  prep_cycles:                            3
% 3.35/1.03  pred_elim_time:                         0.008
% 3.35/1.03  splitting_time:                         0.
% 3.35/1.03  sem_filter_time:                        0.
% 3.35/1.03  monotx_time:                            0.
% 3.35/1.03  subtype_inf_time:                       0.
% 3.35/1.03  
% 3.35/1.03  ------ Problem properties
% 3.35/1.03  
% 3.35/1.03  clauses:                                38
% 3.35/1.03  conjectures:                            3
% 3.35/1.03  epr:                                    4
% 3.35/1.03  horn:                                   32
% 3.35/1.03  ground:                                 14
% 3.35/1.03  unary:                                  11
% 3.35/1.03  binary:                                 10
% 3.35/1.03  lits:                                   93
% 3.35/1.03  lits_eq:                                43
% 3.35/1.03  fd_pure:                                0
% 3.35/1.03  fd_pseudo:                              0
% 3.35/1.03  fd_cond:                                4
% 3.35/1.03  fd_pseudo_cond:                         1
% 3.35/1.03  ac_symbols:                             0
% 3.35/1.03  
% 3.35/1.03  ------ Propositional Solver
% 3.35/1.03  
% 3.35/1.03  prop_solver_calls:                      24
% 3.35/1.03  prop_fast_solver_calls:                 994
% 3.35/1.03  smt_solver_calls:                       0
% 3.35/1.03  smt_fast_solver_calls:                  0
% 3.35/1.03  prop_num_of_clauses:                    1844
% 3.35/1.03  prop_preprocess_simplified:             5750
% 3.35/1.03  prop_fo_subsumed:                       35
% 3.35/1.03  prop_solver_time:                       0.
% 3.35/1.03  smt_solver_time:                        0.
% 3.35/1.03  smt_fast_solver_time:                   0.
% 3.35/1.03  prop_fast_solver_time:                  0.
% 3.35/1.03  prop_unsat_core_time:                   0.
% 3.35/1.03  
% 3.35/1.03  ------ QBF
% 3.35/1.03  
% 3.35/1.03  qbf_q_res:                              0
% 3.35/1.03  qbf_num_tautologies:                    0
% 3.35/1.03  qbf_prep_cycles:                        0
% 3.35/1.03  
% 3.35/1.03  ------ BMC1
% 3.35/1.03  
% 3.35/1.03  bmc1_current_bound:                     -1
% 3.35/1.03  bmc1_last_solved_bound:                 -1
% 3.35/1.04  bmc1_unsat_core_size:                   -1
% 3.35/1.04  bmc1_unsat_core_parents_size:           -1
% 3.35/1.04  bmc1_merge_next_fun:                    0
% 3.35/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.35/1.04  
% 3.35/1.04  ------ Instantiation
% 3.35/1.04  
% 3.35/1.04  inst_num_of_clauses:                    638
% 3.35/1.04  inst_num_in_passive:                    126
% 3.35/1.04  inst_num_in_active:                     304
% 3.35/1.04  inst_num_in_unprocessed:                208
% 3.35/1.04  inst_num_of_loops:                      460
% 3.35/1.04  inst_num_of_learning_restarts:          0
% 3.35/1.04  inst_num_moves_active_passive:          153
% 3.35/1.04  inst_lit_activity:                      0
% 3.35/1.04  inst_lit_activity_moves:                0
% 3.35/1.04  inst_num_tautologies:                   0
% 3.35/1.04  inst_num_prop_implied:                  0
% 3.35/1.04  inst_num_existing_simplified:           0
% 3.35/1.04  inst_num_eq_res_simplified:             0
% 3.35/1.04  inst_num_child_elim:                    0
% 3.35/1.04  inst_num_of_dismatching_blockings:      154
% 3.35/1.04  inst_num_of_non_proper_insts:           620
% 3.35/1.04  inst_num_of_duplicates:                 0
% 3.35/1.04  inst_inst_num_from_inst_to_res:         0
% 3.35/1.04  inst_dismatching_checking_time:         0.
% 3.35/1.04  
% 3.35/1.04  ------ Resolution
% 3.35/1.04  
% 3.35/1.04  res_num_of_clauses:                     0
% 3.35/1.04  res_num_in_passive:                     0
% 3.35/1.04  res_num_in_active:                      0
% 3.35/1.04  res_num_of_loops:                       143
% 3.35/1.04  res_forward_subset_subsumed:            22
% 3.35/1.04  res_backward_subset_subsumed:           0
% 3.35/1.04  res_forward_subsumed:                   0
% 3.35/1.04  res_backward_subsumed:                  0
% 3.35/1.04  res_forward_subsumption_resolution:     4
% 3.35/1.04  res_backward_subsumption_resolution:    0
% 3.35/1.04  res_clause_to_clause_subsumption:       301
% 3.35/1.04  res_orphan_elimination:                 0
% 3.35/1.04  res_tautology_del:                      67
% 3.35/1.04  res_num_eq_res_simplified:              0
% 3.35/1.04  res_num_sel_changes:                    0
% 3.35/1.04  res_moves_from_active_to_pass:          0
% 3.35/1.04  
% 3.35/1.04  ------ Superposition
% 3.35/1.04  
% 3.35/1.04  sup_time_total:                         0.
% 3.35/1.04  sup_time_generating:                    0.
% 3.35/1.04  sup_time_sim_full:                      0.
% 3.35/1.04  sup_time_sim_immed:                     0.
% 3.35/1.04  
% 3.35/1.04  sup_num_of_clauses:                     90
% 3.35/1.04  sup_num_in_active:                      52
% 3.35/1.04  sup_num_in_passive:                     38
% 3.35/1.04  sup_num_of_loops:                       90
% 3.35/1.04  sup_fw_superposition:                   90
% 3.35/1.04  sup_bw_superposition:                   42
% 3.35/1.04  sup_immediate_simplified:               67
% 3.35/1.04  sup_given_eliminated:                   0
% 3.35/1.04  comparisons_done:                       0
% 3.35/1.04  comparisons_avoided:                    7
% 3.35/1.04  
% 3.35/1.04  ------ Simplifications
% 3.35/1.04  
% 3.35/1.04  
% 3.35/1.04  sim_fw_subset_subsumed:                 9
% 3.35/1.04  sim_bw_subset_subsumed:                 9
% 3.35/1.04  sim_fw_subsumed:                        10
% 3.35/1.04  sim_bw_subsumed:                        2
% 3.35/1.04  sim_fw_subsumption_res:                 2
% 3.35/1.04  sim_bw_subsumption_res:                 3
% 3.35/1.04  sim_tautology_del:                      4
% 3.35/1.04  sim_eq_tautology_del:                   11
% 3.35/1.04  sim_eq_res_simp:                        4
% 3.35/1.04  sim_fw_demodulated:                     19
% 3.35/1.04  sim_bw_demodulated:                     52
% 3.35/1.04  sim_light_normalised:                   33
% 3.35/1.04  sim_joinable_taut:                      0
% 3.35/1.04  sim_joinable_simp:                      0
% 3.35/1.04  sim_ac_normalised:                      0
% 3.35/1.04  sim_smt_subsumption:                    0
% 3.35/1.04  
%------------------------------------------------------------------------------
