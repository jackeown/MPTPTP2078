%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:35 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  252 (35041 expanded)
%              Number of clauses        :  180 (11922 expanded)
%              Number of leaves         :   21 (6587 expanded)
%              Depth                    :   33
%              Number of atoms          :  741 (182360 expanded)
%              Number of equality atoms :  453 (43227 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f44])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f85,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f84])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1222,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3685,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1234])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_117,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1514,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_712,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2162,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_2163,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_2165,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1227,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2380,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1222,c_1227])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2395,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2380,c_31])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1233,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2421,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_1233])).

cnf(c_2435,plain,
    ( ~ v1_relat_1(sK3)
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2421])).

cnf(c_2455,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2421,c_33,c_1514,c_2435])).

cnf(c_2456,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2455])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_597,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_33])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1228,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2950,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1222,c_1228])).

cnf(c_3071,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_597,c_2950])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1232,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3075,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3071,c_1232])).

cnf(c_3092,plain,
    ( ~ v1_relat_1(sK3)
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3075])).

cnf(c_1229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2140,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1229])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_388,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_389,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_391,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_35])).

cnf(c_1218,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_2209,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2140,c_1218])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2603,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2209,c_1223])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_374,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_375,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_35])).

cnf(c_1219,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_2208,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2140,c_1219])).

cnf(c_2413,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2395,c_2208])).

cnf(c_2607,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2603,c_2413])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1497,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1498,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1497])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1505,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1506,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

cnf(c_1515,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_3169,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2607,c_36,c_38,c_1498,c_1506,c_1515])).

cnf(c_3174,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3071,c_3169])).

cnf(c_3175,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_3169,c_1228])).

cnf(c_3184,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3175,c_2413])).

cnf(c_3329,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3071,c_3184])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_579,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_1211,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_580,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_1700,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK1
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1211,c_36,c_38,c_580,c_1498,c_1515])).

cnf(c_1701,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1700])).

cnf(c_3338,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3329,c_1701])).

cnf(c_3915,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3685,c_33,c_117,c_1514,c_2165,c_2456,c_3092,c_3174,c_3338])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1235,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3920,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3915,c_1235])).

cnf(c_2438,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_1232])).

cnf(c_2738,plain,
    ( sK2 != k1_xboole_0
    | k2_funct_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_36,c_38,c_1506,c_1515])).

cnf(c_2739,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2738])).

cnf(c_3930,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3920,c_2739])).

cnf(c_3928,plain,
    ( k1_relat_1(k1_xboole_0) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3920,c_3071])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0
    | k2_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_489,c_14])).

cnf(c_1215,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1383,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1215,c_4])).

cnf(c_4455,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3928,c_1383])).

cnf(c_3936,plain,
    ( k2_relat_1(k1_xboole_0) = sK2 ),
    inference(demodulation,[status(thm)],[c_3920,c_2395])).

cnf(c_4468,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4455,c_3936])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_531,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1213,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_1331,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1213,c_4])).

cnf(c_3940,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3920,c_1331])).

cnf(c_4039,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3940])).

cnf(c_4594,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3338,c_3174])).

cnf(c_4595,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4594])).

cnf(c_4761,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4468,c_106,c_112,c_4039,c_4595])).

cnf(c_359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_360,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_1220,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_2951,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1220,c_1228])).

cnf(c_4763,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4761,c_2951])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_110,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_711,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1573,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1712,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_710,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1713,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_369,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_360,c_17])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_369,c_30])).

cnf(c_417,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_1217,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_418,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1767,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_funct_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1217,c_36,c_38,c_418,c_1498,c_1515])).

cnf(c_1768,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1767])).

cnf(c_1660,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1832,plain,
    ( k1_relat_1(sK3) != k1_relat_1(X0)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_1834,plain,
    ( k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_718,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1833,plain,
    ( k1_relat_1(sK3) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1835,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_2499,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_2500,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_2602,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2209,c_1233])).

cnf(c_4766,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4763,c_36,c_33,c_38,c_109,c_110,c_1506,c_1514,c_1515,c_1712,c_1713,c_1768,c_1834,c_1835,c_2456,c_2500,c_2602,c_3092,c_3174,c_3338,c_4595])).

cnf(c_5252,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3930,c_36,c_33,c_38,c_109,c_110,c_1506,c_1514,c_1515,c_1712,c_1713,c_1768,c_1834,c_1835,c_2456,c_2500,c_2602,c_3092,c_3174,c_3338,c_4595,c_4763])).

cnf(c_3942,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(k1_xboole_0)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3920,c_1701])).

cnf(c_4769,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4766,c_3942])).

cnf(c_4802,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4769,c_4])).

cnf(c_93,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_95,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_96,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_98,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_1517,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1519,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1517])).

cnf(c_1518,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_1521,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_720,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1536,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1537,plain,
    ( X0 != sK3
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_1539,plain,
    ( k1_xboole_0 != sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_1677,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1678,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1677])).

cnf(c_637,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != sK3
    | sK1 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_1208,plain,
    ( k2_funct_1(sK3) != sK3
    | sK1 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_638,plain,
    ( k2_funct_1(sK3) != sK3
    | sK1 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_1557,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != sK2
    | k2_funct_1(sK3) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1208,c_36,c_38,c_638,c_1498,c_1515])).

cnf(c_1558,plain,
    ( k2_funct_1(sK3) != sK3
    | sK1 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1557])).

cnf(c_3943,plain,
    ( k2_funct_1(k1_xboole_0) != k1_xboole_0
    | sK1 != sK2
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3920,c_1558])).

cnf(c_4770,plain,
    ( k2_funct_1(k1_xboole_0) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4766,c_3943])).

cnf(c_4795,plain,
    ( k2_funct_1(k1_xboole_0) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4770,c_4])).

cnf(c_3935,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3920,c_2413])).

cnf(c_4774,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4766,c_3935])).

cnf(c_4990,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) = iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4774,c_1223])).

cnf(c_4994,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4990,c_4])).

cnf(c_5218,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4802,c_36,c_33,c_38,c_95,c_98,c_109,c_110,c_1506,c_1514,c_1515,c_1519,c_1521,c_1539,c_1678,c_1712,c_1713,c_1768,c_1834,c_1835,c_2456,c_2500,c_2602,c_3092,c_3174,c_3338,c_3930,c_4595,c_4763,c_4795,c_4994])).

cnf(c_5256,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5252,c_5218])).

cnf(c_5274,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5256,c_2951])).

cnf(c_5261,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5252,c_4774])).

cnf(c_5276,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5274,c_5261])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:55:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.97/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.98  
% 2.97/0.98  ------  iProver source info
% 2.97/0.98  
% 2.97/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.98  git: non_committed_changes: false
% 2.97/0.98  git: last_make_outside_of_git: false
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     num_symb
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       true
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  ------ Parsing...
% 2.97/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.98  ------ Proving...
% 2.97/0.98  ------ Problem Properties 
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  clauses                                 37
% 2.97/0.98  conjectures                             3
% 2.97/0.98  EPR                                     3
% 2.97/0.98  Horn                                    31
% 2.97/0.98  unary                                   11
% 2.97/0.98  binary                                  9
% 2.97/0.98  lits                                    90
% 2.97/0.98  lits eq                                 43
% 2.97/0.98  fd_pure                                 0
% 2.97/0.98  fd_pseudo                               0
% 2.97/0.98  fd_cond                                 5
% 2.97/0.98  fd_pseudo_cond                          0
% 2.97/0.98  AC symbols                              0
% 2.97/0.98  
% 2.97/0.98  ------ Schedule dynamic 5 is on 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  Current options:
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     none
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       false
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ Proving...
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  % SZS status Theorem for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98   Resolution empty clause
% 2.97/0.98  
% 2.97/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  fof(f16,conjecture,(
% 2.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f17,negated_conjecture,(
% 2.97/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.97/0.98    inference(negated_conjecture,[],[f16])).
% 2.97/0.98  
% 2.97/0.98  fof(f37,plain,(
% 2.97/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.97/0.98    inference(ennf_transformation,[],[f17])).
% 2.97/0.98  
% 2.97/0.98  fof(f38,plain,(
% 2.97/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.97/0.98    inference(flattening,[],[f37])).
% 2.97/0.98  
% 2.97/0.98  fof(f44,plain,(
% 2.97/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f45,plain,(
% 2.97/0.98    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f44])).
% 2.97/0.98  
% 2.97/0.98  fof(f78,plain,(
% 2.97/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f5,axiom,(
% 2.97/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f22,plain,(
% 2.97/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.97/0.98    inference(ennf_transformation,[],[f5])).
% 2.97/0.98  
% 2.97/0.98  fof(f52,plain,(
% 2.97/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f22])).
% 2.97/0.98  
% 2.97/0.98  fof(f1,axiom,(
% 2.97/0.98    v1_xboole_0(k1_xboole_0)),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f46,plain,(
% 2.97/0.98    v1_xboole_0(k1_xboole_0)),
% 2.97/0.98    inference(cnf_transformation,[],[f1])).
% 2.97/0.98  
% 2.97/0.98  fof(f10,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f30,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f10])).
% 2.97/0.98  
% 2.97/0.98  fof(f60,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f30])).
% 2.97/0.98  
% 2.97/0.98  fof(f12,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f32,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f12])).
% 2.97/0.98  
% 2.97/0.98  fof(f62,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f32])).
% 2.97/0.98  
% 2.97/0.98  fof(f80,plain,(
% 2.97/0.98    k2_relset_1(sK1,sK2,sK3) = sK2),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f7,axiom,(
% 2.97/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f24,plain,(
% 2.97/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.97/0.98    inference(ennf_transformation,[],[f7])).
% 2.97/0.98  
% 2.97/0.98  fof(f25,plain,(
% 2.97/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.97/0.98    inference(flattening,[],[f24])).
% 2.97/0.98  
% 2.97/0.98  fof(f55,plain,(
% 2.97/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f25])).
% 2.97/0.98  
% 2.97/0.98  fof(f13,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f33,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f13])).
% 2.97/0.98  
% 2.97/0.98  fof(f34,plain,(
% 2.97/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(flattening,[],[f33])).
% 2.97/0.98  
% 2.97/0.98  fof(f41,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(nnf_transformation,[],[f34])).
% 2.97/0.98  
% 2.97/0.98  fof(f63,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f41])).
% 2.97/0.98  
% 2.97/0.98  fof(f77,plain,(
% 2.97/0.98    v1_funct_2(sK3,sK1,sK2)),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f11,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f31,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f11])).
% 2.97/0.98  
% 2.97/0.98  fof(f61,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f31])).
% 2.97/0.98  
% 2.97/0.98  fof(f54,plain,(
% 2.97/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f25])).
% 2.97/0.98  
% 2.97/0.98  fof(f9,axiom,(
% 2.97/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f28,plain,(
% 2.97/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.97/0.98    inference(ennf_transformation,[],[f9])).
% 2.97/0.98  
% 2.97/0.98  fof(f29,plain,(
% 2.97/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.97/0.98    inference(flattening,[],[f28])).
% 2.97/0.98  
% 2.97/0.98  fof(f59,plain,(
% 2.97/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f29])).
% 2.97/0.98  
% 2.97/0.98  fof(f79,plain,(
% 2.97/0.98    v2_funct_1(sK3)),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f76,plain,(
% 2.97/0.98    v1_funct_1(sK3)),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f15,axiom,(
% 2.97/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f35,plain,(
% 2.97/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.97/0.98    inference(ennf_transformation,[],[f15])).
% 2.97/0.98  
% 2.97/0.98  fof(f36,plain,(
% 2.97/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.97/0.98    inference(flattening,[],[f35])).
% 2.97/0.98  
% 2.97/0.98  fof(f75,plain,(
% 2.97/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f36])).
% 2.97/0.98  
% 2.97/0.98  fof(f58,plain,(
% 2.97/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f29])).
% 2.97/0.98  
% 2.97/0.98  fof(f8,axiom,(
% 2.97/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f26,plain,(
% 2.97/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.97/0.98    inference(ennf_transformation,[],[f8])).
% 2.97/0.98  
% 2.97/0.98  fof(f27,plain,(
% 2.97/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.97/0.98    inference(flattening,[],[f26])).
% 2.97/0.98  
% 2.97/0.98  fof(f57,plain,(
% 2.97/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f27])).
% 2.97/0.98  
% 2.97/0.98  fof(f56,plain,(
% 2.97/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f27])).
% 2.97/0.98  
% 2.97/0.98  fof(f65,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f41])).
% 2.97/0.98  
% 2.97/0.98  fof(f81,plain,(
% 2.97/0.98    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f2,axiom,(
% 2.97/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f21,plain,(
% 2.97/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.97/0.98    inference(ennf_transformation,[],[f2])).
% 2.97/0.98  
% 2.97/0.98  fof(f47,plain,(
% 2.97/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f21])).
% 2.97/0.98  
% 2.97/0.98  fof(f64,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f41])).
% 2.97/0.98  
% 2.97/0.98  fof(f88,plain,(
% 2.97/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.97/0.98    inference(equality_resolution,[],[f64])).
% 2.97/0.98  
% 2.97/0.98  fof(f74,plain,(
% 2.97/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f36])).
% 2.97/0.98  
% 2.97/0.98  fof(f4,axiom,(
% 2.97/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f39,plain,(
% 2.97/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.97/0.98    inference(nnf_transformation,[],[f4])).
% 2.97/0.98  
% 2.97/0.98  fof(f40,plain,(
% 2.97/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.97/0.98    inference(flattening,[],[f39])).
% 2.97/0.98  
% 2.97/0.98  fof(f50,plain,(
% 2.97/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.97/0.98    inference(cnf_transformation,[],[f40])).
% 2.97/0.98  
% 2.97/0.98  fof(f83,plain,(
% 2.97/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.97/0.98    inference(equality_resolution,[],[f50])).
% 2.97/0.98  
% 2.97/0.98  fof(f6,axiom,(
% 2.97/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f18,plain,(
% 2.97/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.97/0.98    inference(unused_predicate_definition_removal,[],[f6])).
% 2.97/0.98  
% 2.97/0.98  fof(f23,plain,(
% 2.97/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.97/0.98    inference(ennf_transformation,[],[f18])).
% 2.97/0.98  
% 2.97/0.98  fof(f53,plain,(
% 2.97/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f23])).
% 2.97/0.98  
% 2.97/0.98  fof(f3,axiom,(
% 2.97/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f48,plain,(
% 2.97/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f3])).
% 2.97/0.98  
% 2.97/0.98  fof(f49,plain,(
% 2.97/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f40])).
% 2.97/0.98  
% 2.97/0.98  fof(f68,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f41])).
% 2.97/0.98  
% 2.97/0.98  fof(f84,plain,(
% 2.97/0.98    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(equality_resolution,[],[f68])).
% 2.97/0.98  
% 2.97/0.98  fof(f85,plain,(
% 2.97/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.97/0.98    inference(equality_resolution,[],[f84])).
% 2.97/0.98  
% 2.97/0.98  cnf(c_33,negated_conjecture,
% 2.97/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.97/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1222,plain,
% 2.97/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_6,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.98      | ~ v1_xboole_0(X1)
% 2.97/0.98      | v1_xboole_0(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1234,plain,
% 2.97/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.97/0.98      | v1_xboole_0(X1) != iProver_top
% 2.97/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3685,plain,
% 2.97/0.98      ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.97/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1222,c_1234]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_0,plain,
% 2.97/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_117,plain,
% 2.97/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_14,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1514,plain,
% 2.97/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.97/0.98      | v1_relat_1(sK3) ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_712,plain,
% 2.97/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.97/0.98      theory(equality) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2162,plain,
% 2.97/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_712]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2163,plain,
% 2.97/0.98      ( sK3 != X0
% 2.97/0.98      | v1_xboole_0(X0) != iProver_top
% 2.97/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2165,plain,
% 2.97/0.98      ( sK3 != k1_xboole_0
% 2.97/0.98      | v1_xboole_0(sK3) = iProver_top
% 2.97/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_2163]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_16,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1227,plain,
% 2.97/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.97/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2380,plain,
% 2.97/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1222,c_1227]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_31,negated_conjecture,
% 2.97/0.98      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.97/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2395,plain,
% 2.97/0.98      ( k2_relat_1(sK3) = sK2 ),
% 2.97/0.98      inference(light_normalisation,[status(thm)],[c_2380,c_31]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_8,plain,
% 2.97/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.97/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1233,plain,
% 2.97/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 2.97/0.98      | k1_xboole_0 = X0
% 2.97/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2421,plain,
% 2.97/0.98      ( sK2 != k1_xboole_0
% 2.97/0.98      | sK3 = k1_xboole_0
% 2.97/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_2395,c_1233]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2435,plain,
% 2.97/0.98      ( ~ v1_relat_1(sK3) | sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.97/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2421]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2455,plain,
% 2.97/0.99      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2421,c_33,c_1514,c_2435]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2456,plain,
% 2.97/0.99      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_2455]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_22,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.97/0.99      | k1_xboole_0 = X2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_34,negated_conjecture,
% 2.97/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.97/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_594,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.97/0.99      | sK1 != X1
% 2.97/0.99      | sK2 != X2
% 2.97/0.99      | sK3 != X0
% 2.97/0.99      | k1_xboole_0 = X2 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_595,plain,
% 2.97/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.97/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.97/0.99      | k1_xboole_0 = sK2 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_594]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_597,plain,
% 2.97/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.97/0.99      inference(global_propositional_subsumption,[status(thm)],[c_595,c_33]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_15,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1228,plain,
% 2.97/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.97/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2950,plain,
% 2.97/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1222,c_1228]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3071,plain,
% 2.97/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_597,c_2950]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_9,plain,
% 2.97/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1232,plain,
% 2.97/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = X0
% 2.97/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3075,plain,
% 2.97/0.99      ( sK1 != k1_xboole_0
% 2.97/0.99      | sK2 = k1_xboole_0
% 2.97/0.99      | sK3 = k1_xboole_0
% 2.97/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3071,c_1232]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3092,plain,
% 2.97/0.99      ( ~ v1_relat_1(sK3)
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | sK2 = k1_xboole_0
% 2.97/0.99      | sK3 = k1_xboole_0 ),
% 2.97/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3075]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1229,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2140,plain,
% 2.97/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1222,c_1229]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12,plain,
% 2.97/0.99      ( ~ v2_funct_1(X0)
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_32,negated_conjecture,
% 2.97/0.99      ( v2_funct_1(sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_388,plain,
% 2.97/0.99      ( ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.97/0.99      | sK3 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_389,plain,
% 2.97/0.99      ( ~ v1_funct_1(sK3)
% 2.97/0.99      | ~ v1_relat_1(sK3)
% 2.97/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_388]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_35,negated_conjecture,
% 2.97/0.99      ( v1_funct_1(sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_391,plain,
% 2.97/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.97/0.99      inference(global_propositional_subsumption,[status(thm)],[c_389,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1218,plain,
% 2.97/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 2.97/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2209,plain,
% 2.97/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2140,c_1218]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_27,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1223,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.97/0.99      | v1_funct_1(X0) != iProver_top
% 2.97/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2603,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2209,c_1223]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_13,plain,
% 2.97/0.99      ( ~ v2_funct_1(X0)
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_374,plain,
% 2.97/0.99      ( ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.97/0.99      | sK3 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_375,plain,
% 2.97/0.99      ( ~ v1_funct_1(sK3)
% 2.97/0.99      | ~ v1_relat_1(sK3)
% 2.97/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_377,plain,
% 2.97/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.97/0.99      inference(global_propositional_subsumption,[status(thm)],[c_375,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1219,plain,
% 2.97/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 2.97/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2208,plain,
% 2.97/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2140,c_1219]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2413,plain,
% 2.97/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_2395,c_2208]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2607,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_2603,c_2413]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_36,plain,
% 2.97/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_38,plain,
% 2.97/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_10,plain,
% 2.97/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1497,plain,
% 2.97/0.99      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1498,plain,
% 2.97/0.99      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.97/0.99      | v1_funct_1(sK3) != iProver_top
% 2.97/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1497]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11,plain,
% 2.97/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1505,plain,
% 2.97/0.99      ( ~ v1_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1506,plain,
% 2.97/0.99      ( v1_funct_1(sK3) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 2.97/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1505]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1515,plain,
% 2.97/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.97/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3169,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2607,c_36,c_38,c_1498,c_1506,c_1515]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3174,plain,
% 2.97/0.99      ( sK2 = k1_xboole_0
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3071,c_3169]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3175,plain,
% 2.97/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3169,c_1228]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3184,plain,
% 2.97/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_3175,c_2413]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3329,plain,
% 2.97/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3071,c_3184]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_20,plain,
% 2.97/0.99      ( v1_funct_2(X0,X1,X2)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.97/0.99      | k1_xboole_0 = X2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_30,negated_conjecture,
% 2.97/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 2.97/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.97/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_578,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.97/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.97/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.97/0.99      | k2_funct_1(sK3) != X0
% 2.97/0.99      | sK1 != X2
% 2.97/0.99      | sK2 != X1
% 2.97/0.99      | k1_xboole_0 = X2 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_579,plain,
% 2.97/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.97/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.97/0.99      | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 2.97/0.99      | k1_xboole_0 = sK1 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_578]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1211,plain,
% 2.97/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 2.97/0.99      | k1_xboole_0 = sK1
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_580,plain,
% 2.97/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 2.97/0.99      | k1_xboole_0 = sK1
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1700,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | k1_xboole_0 = sK1
% 2.97/0.99      | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_1211,c_36,c_38,c_580,c_1498,c_1515]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1701,plain,
% 2.97/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 2.97/0.99      | k1_xboole_0 = sK1
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_1700]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3338,plain,
% 2.97/0.99      ( sK1 = k1_xboole_0
% 2.97/0.99      | sK2 = k1_xboole_0
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3329,c_1701]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3915,plain,
% 2.97/0.99      ( v1_xboole_0(sK3) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_3685,c_33,c_117,c_1514,c_2165,c_2456,c_3092,c_3174,c_3338]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1,plain,
% 2.97/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1235,plain,
% 2.97/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3920,plain,
% 2.97/0.99      ( sK3 = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3915,c_1235]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2438,plain,
% 2.97/0.99      ( k2_funct_1(sK3) = k1_xboole_0
% 2.97/0.99      | sK2 != k1_xboole_0
% 2.97/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2413,c_1232]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2738,plain,
% 2.97/0.99      ( sK2 != k1_xboole_0 | k2_funct_1(sK3) = k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2438,c_36,c_38,c_1506,c_1515]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2739,plain,
% 2.97/0.99      ( k2_funct_1(sK3) = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_2738]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3930,plain,
% 2.97/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3920,c_2739]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3928,plain,
% 2.97/0.99      ( k1_relat_1(k1_xboole_0) = sK1 | sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3920,c_3071]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_21,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.97/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_28,plain,
% 2.97/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_488,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.97/0.99      | ~ v1_funct_1(X2)
% 2.97/0.99      | ~ v1_relat_1(X2)
% 2.97/0.99      | X2 != X0
% 2.97/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.97/0.99      | k1_relat_1(X2) != k1_xboole_0
% 2.97/0.99      | k2_relat_1(X2) != X1 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_489,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.97/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_488]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_503,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.97/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.97/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_489,c_14]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1215,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.97/0.99      | k1_relat_1(X0) != k1_xboole_0
% 2.97/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
% 2.97/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4,plain,
% 2.97/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1383,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.97/0.99      | k1_relat_1(X0) != k1_xboole_0
% 2.97/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.97/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_1215,c_4]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4455,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | sK2 = k1_xboole_0
% 2.97/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.97/0.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3928,c_1383]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3936,plain,
% 2.97/0.99      ( k2_relat_1(k1_xboole_0) = sK2 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3920,c_2395]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4468,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | sK2 = k1_xboole_0
% 2.97/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.97/0.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_4455,c_3936]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_106,plain,
% 2.97/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.97/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2,plain,
% 2.97/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_112,plain,
% 2.97/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_530,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.97/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | sK2 != X1
% 2.97/0.99      | sK3 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_531,plain,
% 2.97/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.97/0.99      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_530]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1213,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1331,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_1213,c_4]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3940,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3920,c_1331]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4039,plain,
% 2.97/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.97/0.99      | k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0 ),
% 2.97/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3940]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4594,plain,
% 2.97/0.99      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3338,c_3174]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4595,plain,
% 2.97/0.99      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_4594]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4761,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0
% 2.97/0.99      | sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_4468,c_106,c_112,c_4039,c_4595]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_359,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | X1 != X2 | k1_xboole_0 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_360,plain,
% 2.97/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1220,plain,
% 2.97/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2951,plain,
% 2.97/0.99      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1220,c_1228]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4763,plain,
% 2.97/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4761,c_2951]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5,plain,
% 2.97/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = X0
% 2.97/0.99      | k1_xboole_0 = X1 ),
% 2.97/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_109,plain,
% 2.97/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_110,plain,
% 2.97/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_711,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1573,plain,
% 2.97/0.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_711]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1712,plain,
% 2.97/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_710,plain,( X0 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1713,plain,
% 2.97/0.99      ( sK2 = sK2 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_710]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_17,plain,
% 2.97/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.97/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.97/0.99      | k1_xboole_0 = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_369,plain,
% 2.97/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.97/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_360,c_17]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_416,plain,
% 2.97/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.97/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.97/0.99      | k2_funct_1(sK3) != k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | sK2 != X0
% 2.97/0.99      | k1_xboole_0 = X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_369,c_30]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_417,plain,
% 2.97/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.97/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.97/0.99      | k2_funct_1(sK3) != k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = sK2 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1217,plain,
% 2.97/0.99      ( k2_funct_1(sK3) != k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = sK2
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_418,plain,
% 2.97/0.99      ( k2_funct_1(sK3) != k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = sK2
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1767,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | k1_xboole_0 = sK2
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | k2_funct_1(sK3) != k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_1217,c_36,c_38,c_418,c_1498,c_1515]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1768,plain,
% 2.97/0.99      ( k2_funct_1(sK3) != k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = sK2
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_1767]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1660,plain,
% 2.97/0.99      ( k1_relat_1(sK3) != X0
% 2.97/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 2.97/0.99      | k1_xboole_0 != X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_711]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1832,plain,
% 2.97/0.99      ( k1_relat_1(sK3) != k1_relat_1(X0)
% 2.97/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 2.97/0.99      | k1_xboole_0 != k1_relat_1(X0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1660]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1834,plain,
% 2.97/0.99      ( k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
% 2.97/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 2.97/0.99      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1832]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_718,plain,
% 2.97/0.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.97/0.99      theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1833,plain,
% 2.97/0.99      ( k1_relat_1(sK3) = k1_relat_1(X0) | sK3 != X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_718]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1835,plain,
% 2.97/0.99      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1833]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2499,plain,
% 2.97/0.99      ( k1_relat_1(X0) != X1
% 2.97/0.99      | k1_xboole_0 != X1
% 2.97/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_711]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2500,plain,
% 2.97/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.97/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2499]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2602,plain,
% 2.97/0.99      ( k2_funct_1(sK3) = k1_xboole_0
% 2.97/0.99      | k1_relat_1(sK3) != k1_xboole_0
% 2.97/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2209,c_1233]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4766,plain,
% 2.97/0.99      ( sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_4763,c_36,c_33,c_38,c_109,c_110,c_1506,c_1514,c_1515,
% 2.97/0.99                 c_1712,c_1713,c_1768,c_1834,c_1835,c_2456,c_2500,c_2602,
% 2.97/0.99                 c_3092,c_3174,c_3338,c_4595]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5252,plain,
% 2.97/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_3930,c_36,c_33,c_38,c_109,c_110,c_1506,c_1514,c_1515,
% 2.97/0.99                 c_1712,c_1713,c_1768,c_1834,c_1835,c_2456,c_2500,c_2602,
% 2.97/0.99                 c_3092,c_3174,c_3338,c_4595,c_4763]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3942,plain,
% 2.97/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(k1_xboole_0)) != sK2
% 2.97/0.99      | sK1 = k1_xboole_0
% 2.97/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3920,c_1701]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4769,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 2.97/0.99      | sK1 = k1_xboole_0
% 2.97/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4766,c_3942]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4802,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 2.97/0.99      | sK1 = k1_xboole_0
% 2.97/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4769,c_4]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_93,plain,
% 2.97/0.99      ( v1_funct_1(X0) != iProver_top
% 2.97/0.99      | v1_relat_1(X0) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_95,plain,
% 2.97/0.99      ( v1_funct_1(k1_xboole_0) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.97/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_93]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_96,plain,
% 2.97/0.99      ( v1_funct_1(X0) != iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 2.97/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_98,plain,
% 2.97/0.99      ( v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.97/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.97/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_96]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1517,plain,
% 2.97/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.99      | v1_relat_1(k1_xboole_0) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1519,plain,
% 2.97/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.97/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1517]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1518,plain,
% 2.97/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_360]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1521,plain,
% 2.97/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_720,plain,
% 2.97/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.97/0.99      theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1536,plain,
% 2.97/0.99      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_720]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1537,plain,
% 2.97/0.99      ( X0 != sK3
% 2.97/0.99      | v1_funct_1(X0) = iProver_top
% 2.97/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1539,plain,
% 2.97/0.99      ( k1_xboole_0 != sK3
% 2.97/0.99      | v1_funct_1(sK3) != iProver_top
% 2.97/0.99      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1537]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1677,plain,
% 2.97/0.99      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_711]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1678,plain,
% 2.97/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1677]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_637,plain,
% 2.97/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.97/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.97/0.99      | k2_funct_1(sK3) != sK3
% 2.97/0.99      | sK1 != sK2 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1208,plain,
% 2.97/0.99      ( k2_funct_1(sK3) != sK3
% 2.97/0.99      | sK1 != sK2
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_638,plain,
% 2.97/0.99      ( k2_funct_1(sK3) != sK3
% 2.97/0.99      | sK1 != sK2
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1557,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.97/0.99      | sK1 != sK2
% 2.97/0.99      | k2_funct_1(sK3) != sK3 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_1208,c_36,c_38,c_638,c_1498,c_1515]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1558,plain,
% 2.97/0.99      ( k2_funct_1(sK3) != sK3
% 2.97/0.99      | sK1 != sK2
% 2.97/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_1557]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3943,plain,
% 2.97/0.99      ( k2_funct_1(k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | sK1 != sK2
% 2.97/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3920,c_1558]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4770,plain,
% 2.97/0.99      ( k2_funct_1(k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4766,c_3943]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4795,plain,
% 2.97/0.99      ( k2_funct_1(k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | sK1 != k1_xboole_0
% 2.97/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4770,c_4]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3935,plain,
% 2.97/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK2 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3920,c_2413]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4774,plain,
% 2.97/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4766,c_3935]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4990,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) = iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_4774,c_1223]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4994,plain,
% 2.97/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.97/0.99      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4990,c_4]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5218,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_4802,c_36,c_33,c_38,c_95,c_98,c_109,c_110,c_1506,c_1514,
% 2.97/0.99                 c_1515,c_1519,c_1521,c_1539,c_1678,c_1712,c_1713,c_1768,
% 2.97/0.99                 c_1834,c_1835,c_2456,c_2500,c_2602,c_3092,c_3174,c_3338,
% 2.97/0.99                 c_3930,c_4595,c_4763,c_4795,c_4994]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5256,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_5252,c_5218]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5274,plain,
% 2.97/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_5256,c_2951]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5261,plain,
% 2.97/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_5252,c_4774]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5276,plain,
% 2.97/0.99      ( $false ),
% 2.97/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_5274,c_5261]) ).
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  ------                               Statistics
% 2.97/0.99  
% 2.97/0.99  ------ General
% 2.97/0.99  
% 2.97/0.99  abstr_ref_over_cycles:                  0
% 2.97/0.99  abstr_ref_under_cycles:                 0
% 2.97/0.99  gc_basic_clause_elim:                   0
% 2.97/0.99  forced_gc_time:                         0
% 2.97/0.99  parsing_time:                           0.009
% 2.97/0.99  unif_index_cands_time:                  0.
% 2.97/0.99  unif_index_add_time:                    0.
% 2.97/0.99  orderings_time:                         0.
% 2.97/0.99  out_proof_time:                         0.011
% 2.97/0.99  total_time:                             0.189
% 2.97/0.99  num_of_symbols:                         50
% 2.97/0.99  num_of_terms:                           3641
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing
% 2.97/0.99  
% 2.97/0.99  num_of_splits:                          0
% 2.97/0.99  num_of_split_atoms:                     0
% 2.97/0.99  num_of_reused_defs:                     0
% 2.97/0.99  num_eq_ax_congr_red:                    5
% 2.97/0.99  num_of_sem_filtered_clauses:            1
% 2.97/0.99  num_of_subtypes:                        0
% 2.97/0.99  monotx_restored_types:                  0
% 2.97/0.99  sat_num_of_epr_types:                   0
% 2.97/0.99  sat_num_of_non_cyclic_types:            0
% 2.97/0.99  sat_guarded_non_collapsed_types:        0
% 2.97/0.99  num_pure_diseq_elim:                    0
% 2.97/0.99  simp_replaced_by:                       0
% 2.97/0.99  res_preprocessed:                       138
% 2.97/0.99  prep_upred:                             0
% 2.97/0.99  prep_unflattend:                        56
% 2.97/0.99  smt_new_axioms:                         0
% 2.97/0.99  pred_elim_cands:                        7
% 2.97/0.99  pred_elim:                              3
% 2.97/0.99  pred_elim_cl:                           -2
% 2.97/0.99  pred_elim_cycles:                       4
% 2.97/0.99  merged_defs:                            0
% 2.97/0.99  merged_defs_ncl:                        0
% 2.97/0.99  bin_hyper_res:                          0
% 2.97/0.99  prep_cycles:                            3
% 2.97/0.99  pred_elim_time:                         0.013
% 2.97/0.99  splitting_time:                         0.
% 2.97/0.99  sem_filter_time:                        0.
% 2.97/0.99  monotx_time:                            0.
% 2.97/0.99  subtype_inf_time:                       0.
% 2.97/0.99  
% 2.97/0.99  ------ Problem properties
% 2.97/0.99  
% 2.97/0.99  clauses:                                37
% 2.97/0.99  conjectures:                            3
% 2.97/0.99  epr:                                    3
% 2.97/0.99  horn:                                   31
% 2.97/0.99  ground:                                 15
% 2.97/0.99  unary:                                  11
% 2.97/0.99  binary:                                 9
% 2.97/0.99  lits:                                   90
% 2.97/0.99  lits_eq:                                43
% 2.97/0.99  fd_pure:                                0
% 2.97/0.99  fd_pseudo:                              0
% 2.97/0.99  fd_cond:                                5
% 2.97/0.99  fd_pseudo_cond:                         0
% 2.97/0.99  ac_symbols:                             0
% 2.97/0.99  
% 2.97/0.99  ------ Propositional Solver
% 2.97/0.99  
% 2.97/0.99  prop_solver_calls:                      24
% 2.97/0.99  prop_fast_solver_calls:                 1014
% 2.97/0.99  smt_solver_calls:                       0
% 2.97/0.99  smt_fast_solver_calls:                  0
% 2.97/0.99  prop_num_of_clauses:                    1780
% 2.97/0.99  prop_preprocess_simplified:             5249
% 2.97/0.99  prop_fo_subsumed:                       42
% 2.97/0.99  prop_solver_time:                       0.
% 2.97/0.99  smt_solver_time:                        0.
% 2.97/0.99  smt_fast_solver_time:                   0.
% 2.97/0.99  prop_fast_solver_time:                  0.
% 2.97/0.99  prop_unsat_core_time:                   0.
% 2.97/0.99  
% 2.97/0.99  ------ QBF
% 2.97/0.99  
% 2.97/0.99  qbf_q_res:                              0
% 2.97/0.99  qbf_num_tautologies:                    0
% 2.97/0.99  qbf_prep_cycles:                        0
% 2.97/0.99  
% 2.97/0.99  ------ BMC1
% 2.97/0.99  
% 2.97/0.99  bmc1_current_bound:                     -1
% 2.97/0.99  bmc1_last_solved_bound:                 -1
% 2.97/0.99  bmc1_unsat_core_size:                   -1
% 2.97/0.99  bmc1_unsat_core_parents_size:           -1
% 2.97/0.99  bmc1_merge_next_fun:                    0
% 2.97/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation
% 2.97/0.99  
% 2.97/0.99  inst_num_of_clauses:                    668
% 2.97/0.99  inst_num_in_passive:                    94
% 2.97/0.99  inst_num_in_active:                     355
% 2.97/0.99  inst_num_in_unprocessed:                223
% 2.97/0.99  inst_num_of_loops:                      460
% 2.97/0.99  inst_num_of_learning_restarts:          0
% 2.97/0.99  inst_num_moves_active_passive:          102
% 2.97/0.99  inst_lit_activity:                      0
% 2.97/0.99  inst_lit_activity_moves:                0
% 2.97/0.99  inst_num_tautologies:                   0
% 2.97/0.99  inst_num_prop_implied:                  0
% 2.97/0.99  inst_num_existing_simplified:           0
% 2.97/0.99  inst_num_eq_res_simplified:             0
% 2.97/0.99  inst_num_child_elim:                    0
% 2.97/0.99  inst_num_of_dismatching_blockings:      173
% 2.97/0.99  inst_num_of_non_proper_insts:           459
% 2.97/0.99  inst_num_of_duplicates:                 0
% 2.97/0.99  inst_inst_num_from_inst_to_res:         0
% 2.97/0.99  inst_dismatching_checking_time:         0.
% 2.97/0.99  
% 2.97/0.99  ------ Resolution
% 2.97/0.99  
% 2.97/0.99  res_num_of_clauses:                     0
% 2.97/0.99  res_num_in_passive:                     0
% 2.97/0.99  res_num_in_active:                      0
% 2.97/0.99  res_num_of_loops:                       141
% 2.97/0.99  res_forward_subset_subsumed:            29
% 2.97/0.99  res_backward_subset_subsumed:           8
% 2.97/0.99  res_forward_subsumed:                   0
% 2.97/0.99  res_backward_subsumed:                  0
% 2.97/0.99  res_forward_subsumption_resolution:     4
% 2.97/0.99  res_backward_subsumption_resolution:    1
% 2.97/0.99  res_clause_to_clause_subsumption:       237
% 2.97/0.99  res_orphan_elimination:                 0
% 2.97/0.99  res_tautology_del:                      93
% 2.97/0.99  res_num_eq_res_simplified:              0
% 2.97/0.99  res_num_sel_changes:                    0
% 2.97/0.99  res_moves_from_active_to_pass:          0
% 2.97/0.99  
% 2.97/0.99  ------ Superposition
% 2.97/0.99  
% 2.97/0.99  sup_time_total:                         0.
% 2.97/0.99  sup_time_generating:                    0.
% 2.97/0.99  sup_time_sim_full:                      0.
% 2.97/0.99  sup_time_sim_immed:                     0.
% 2.97/0.99  
% 2.97/0.99  sup_num_of_clauses:                     88
% 2.97/0.99  sup_num_in_active:                      40
% 2.97/0.99  sup_num_in_passive:                     48
% 2.97/0.99  sup_num_of_loops:                       91
% 2.97/0.99  sup_fw_superposition:                   68
% 2.97/0.99  sup_bw_superposition:                   57
% 2.97/0.99  sup_immediate_simplified:               48
% 2.97/0.99  sup_given_eliminated:                   0
% 2.97/0.99  comparisons_done:                       0
% 2.97/0.99  comparisons_avoided:                    19
% 2.97/0.99  
% 2.97/0.99  ------ Simplifications
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  sim_fw_subset_subsumed:                 13
% 2.97/0.99  sim_bw_subset_subsumed:                 9
% 2.97/0.99  sim_fw_subsumed:                        20
% 2.97/0.99  sim_bw_subsumed:                        1
% 2.97/0.99  sim_fw_subsumption_res:                 0
% 2.97/0.99  sim_bw_subsumption_res:                 2
% 2.97/0.99  sim_tautology_del:                      1
% 2.97/0.99  sim_eq_tautology_del:                   10
% 2.97/0.99  sim_eq_res_simp:                        0
% 2.97/0.99  sim_fw_demodulated:                     17
% 2.97/0.99  sim_bw_demodulated:                     48
% 2.97/0.99  sim_light_normalised:                   32
% 2.97/0.99  sim_joinable_taut:                      0
% 2.97/0.99  sim_joinable_simp:                      0
% 2.97/0.99  sim_ac_normalised:                      0
% 2.97/0.99  sim_smt_subsumption:                    0
% 2.97/0.99  
%------------------------------------------------------------------------------
