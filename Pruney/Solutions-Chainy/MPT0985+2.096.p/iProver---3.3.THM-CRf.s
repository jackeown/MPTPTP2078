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
% DateTime   : Thu Dec  3 12:02:39 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  178 (28773 expanded)
%              Number of clauses        :  123 (8695 expanded)
%              Number of leaves         :   10 (5649 expanded)
%              Depth                    :   30
%              Number of atoms          :  570 (158464 expanded)
%              Number of equality atoms :  329 (31314 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f40,plain,
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

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f40])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_586,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_588,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_586,c_30])).

cnf(c_1175,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1181,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2385,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1175,c_1181])).

cnf(c_2461,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_588,c_2385])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1180,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2158,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1175,c_1180])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2173,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2158,c_28])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_341,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_342,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_344,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_342,c_32])).

cnf(c_1172,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1477,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1172,c_32,c_30,c_342,c_1451])).

cnf(c_2282,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2173,c_1477])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2457,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK3))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_1176])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_355,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_356,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_358,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_32])).

cnf(c_1171,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_1473,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1171,c_32,c_30,c_356,c_1451])).

cnf(c_2458,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2457,c_1473])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1439,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1440,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1439])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1447,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1448,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_1452,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_3136,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2458,c_33,c_35,c_1440,c_1448,c_1452])).

cnf(c_3143,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_3136,c_1181])).

cnf(c_3152,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3143,c_2282])).

cnf(c_3204,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2461,c_3152])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_609,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1
    | k2_funct_1(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_610,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_622,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_610,c_11])).

cnf(c_1161,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_611,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_1577,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_33,c_35,c_611,c_1440,c_1448,c_1452])).

cnf(c_1578,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1577])).

cnf(c_1581,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1578,c_1473,c_1477])).

cnf(c_2281,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2173,c_1581])).

cnf(c_2285,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2281])).

cnf(c_2758,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_2285])).

cnf(c_3141,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_3136])).

cnf(c_3352,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3204,c_2758,c_3141])).

cnf(c_3364,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3352,c_2173])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_422,c_11])).

cnf(c_1169,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1336,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1169,c_1])).

cnf(c_3719,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3364,c_1336])).

cnf(c_3373,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3352,c_1175])).

cnf(c_3378,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3373,c_1])).

cnf(c_4076,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3719,c_33,c_3378])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0
    | k2_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_480,c_11])).

cnf(c_1167,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1319,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1167,c_2])).

cnf(c_4081,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK3),sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4076,c_1319])).

cnf(c_4099,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4081,c_3364])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != X1
    | sK2 != k1_xboole_0
    | sK3 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_448,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_1168,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_1266,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1168,c_1])).

cnf(c_3365,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3352,c_1266])).

cnf(c_3412,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3365])).

cnf(c_3416,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3412,c_3378])).

cnf(c_3357,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3352,c_3136])).

cnf(c_3437,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3357,c_2])).

cnf(c_3358,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3352,c_2285])).

cnf(c_3433,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3358,c_2])).

cnf(c_3441,plain,
    ( k1_relat_1(sK3) != sK1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3437,c_3433])).

cnf(c_4083,plain,
    ( sK1 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4076,c_3441])).

cnf(c_4302,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4099,c_3416,c_4083])).

cnf(c_4314,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4302,c_3437])).

cnf(c_2388,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1181])).

cnf(c_5003,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4314,c_2388])).

cnf(c_3363,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3352,c_2282])).

cnf(c_4312,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4302,c_3363])).

cnf(c_5015,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5003,c_4312])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_503,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_1166,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_1357,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1166,c_2])).

cnf(c_1733,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1357,c_33,c_35,c_1440,c_1452])).

cnf(c_1734,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1733])).

cnf(c_3366,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3352,c_1734])).

cnf(c_3405,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3366])).

cnf(c_3409,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3405,c_2])).

cnf(c_3440,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3437,c_3409])).

cnf(c_5180,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3440,c_4302])).

cnf(c_5898,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5015,c_5180])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5898,c_104,c_103])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.93/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/0.98  
% 2.93/0.98  ------  iProver source info
% 2.93/0.98  
% 2.93/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.93/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/0.98  git: non_committed_changes: false
% 2.93/0.98  git: last_make_outside_of_git: false
% 2.93/0.98  
% 2.93/0.98  ------ 
% 2.93/0.98  
% 2.93/0.98  ------ Input Options
% 2.93/0.98  
% 2.93/0.98  --out_options                           all
% 2.93/0.98  --tptp_safe_out                         true
% 2.93/0.98  --problem_path                          ""
% 2.93/0.98  --include_path                          ""
% 2.93/0.98  --clausifier                            res/vclausify_rel
% 2.93/0.98  --clausifier_options                    --mode clausify
% 2.93/0.98  --stdin                                 false
% 2.93/0.98  --stats_out                             all
% 2.93/0.98  
% 2.93/0.98  ------ General Options
% 2.93/0.98  
% 2.93/0.98  --fof                                   false
% 2.93/0.98  --time_out_real                         305.
% 2.93/0.98  --time_out_virtual                      -1.
% 2.93/0.98  --symbol_type_check                     false
% 2.93/0.98  --clausify_out                          false
% 2.93/0.98  --sig_cnt_out                           false
% 2.93/0.98  --trig_cnt_out                          false
% 2.93/0.98  --trig_cnt_out_tolerance                1.
% 2.93/0.98  --trig_cnt_out_sk_spl                   false
% 2.93/0.98  --abstr_cl_out                          false
% 2.93/0.98  
% 2.93/0.98  ------ Global Options
% 2.93/0.98  
% 2.93/0.98  --schedule                              default
% 2.93/0.98  --add_important_lit                     false
% 2.93/0.98  --prop_solver_per_cl                    1000
% 2.93/0.98  --min_unsat_core                        false
% 2.93/0.98  --soft_assumptions                      false
% 2.93/0.98  --soft_lemma_size                       3
% 2.93/0.98  --prop_impl_unit_size                   0
% 2.93/0.98  --prop_impl_unit                        []
% 2.93/0.98  --share_sel_clauses                     true
% 2.93/0.98  --reset_solvers                         false
% 2.93/0.98  --bc_imp_inh                            [conj_cone]
% 2.93/0.98  --conj_cone_tolerance                   3.
% 2.93/0.98  --extra_neg_conj                        none
% 2.93/0.98  --large_theory_mode                     true
% 2.93/0.98  --prolific_symb_bound                   200
% 2.93/0.98  --lt_threshold                          2000
% 2.93/0.98  --clause_weak_htbl                      true
% 2.93/0.98  --gc_record_bc_elim                     false
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing Options
% 2.93/0.98  
% 2.93/0.98  --preprocessing_flag                    true
% 2.93/0.98  --time_out_prep_mult                    0.1
% 2.93/0.98  --splitting_mode                        input
% 2.93/0.98  --splitting_grd                         true
% 2.93/0.98  --splitting_cvd                         false
% 2.93/0.98  --splitting_cvd_svl                     false
% 2.93/0.98  --splitting_nvd                         32
% 2.93/0.98  --sub_typing                            true
% 2.93/0.98  --prep_gs_sim                           true
% 2.93/0.98  --prep_unflatten                        true
% 2.93/0.98  --prep_res_sim                          true
% 2.93/0.98  --prep_upred                            true
% 2.93/0.98  --prep_sem_filter                       exhaustive
% 2.93/0.98  --prep_sem_filter_out                   false
% 2.93/0.98  --pred_elim                             true
% 2.93/0.98  --res_sim_input                         true
% 2.93/0.98  --eq_ax_congr_red                       true
% 2.93/0.98  --pure_diseq_elim                       true
% 2.93/0.98  --brand_transform                       false
% 2.93/0.98  --non_eq_to_eq                          false
% 2.93/0.98  --prep_def_merge                        true
% 2.93/0.98  --prep_def_merge_prop_impl              false
% 2.93/0.98  --prep_def_merge_mbd                    true
% 2.93/0.98  --prep_def_merge_tr_red                 false
% 2.93/0.98  --prep_def_merge_tr_cl                  false
% 2.93/0.98  --smt_preprocessing                     true
% 2.93/0.98  --smt_ac_axioms                         fast
% 2.93/0.98  --preprocessed_out                      false
% 2.93/0.98  --preprocessed_stats                    false
% 2.93/0.98  
% 2.93/0.98  ------ Abstraction refinement Options
% 2.93/0.98  
% 2.93/0.98  --abstr_ref                             []
% 2.93/0.98  --abstr_ref_prep                        false
% 2.93/0.98  --abstr_ref_until_sat                   false
% 2.93/0.98  --abstr_ref_sig_restrict                funpre
% 2.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.98  --abstr_ref_under                       []
% 2.93/0.98  
% 2.93/0.98  ------ SAT Options
% 2.93/0.98  
% 2.93/0.98  --sat_mode                              false
% 2.93/0.98  --sat_fm_restart_options                ""
% 2.93/0.98  --sat_gr_def                            false
% 2.93/0.98  --sat_epr_types                         true
% 2.93/0.98  --sat_non_cyclic_types                  false
% 2.93/0.98  --sat_finite_models                     false
% 2.93/0.98  --sat_fm_lemmas                         false
% 2.93/0.98  --sat_fm_prep                           false
% 2.93/0.98  --sat_fm_uc_incr                        true
% 2.93/0.98  --sat_out_model                         small
% 2.93/0.98  --sat_out_clauses                       false
% 2.93/0.98  
% 2.93/0.98  ------ QBF Options
% 2.93/0.98  
% 2.93/0.98  --qbf_mode                              false
% 2.93/0.98  --qbf_elim_univ                         false
% 2.93/0.98  --qbf_dom_inst                          none
% 2.93/0.98  --qbf_dom_pre_inst                      false
% 2.93/0.98  --qbf_sk_in                             false
% 2.93/0.98  --qbf_pred_elim                         true
% 2.93/0.98  --qbf_split                             512
% 2.93/0.98  
% 2.93/0.98  ------ BMC1 Options
% 2.93/0.98  
% 2.93/0.98  --bmc1_incremental                      false
% 2.93/0.98  --bmc1_axioms                           reachable_all
% 2.93/0.98  --bmc1_min_bound                        0
% 2.93/0.98  --bmc1_max_bound                        -1
% 2.93/0.98  --bmc1_max_bound_default                -1
% 2.93/0.98  --bmc1_symbol_reachability              true
% 2.93/0.98  --bmc1_property_lemmas                  false
% 2.93/0.98  --bmc1_k_induction                      false
% 2.93/0.98  --bmc1_non_equiv_states                 false
% 2.93/0.98  --bmc1_deadlock                         false
% 2.93/0.98  --bmc1_ucm                              false
% 2.93/0.98  --bmc1_add_unsat_core                   none
% 2.93/0.98  --bmc1_unsat_core_children              false
% 2.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.98  --bmc1_out_stat                         full
% 2.93/0.98  --bmc1_ground_init                      false
% 2.93/0.98  --bmc1_pre_inst_next_state              false
% 2.93/0.98  --bmc1_pre_inst_state                   false
% 2.93/0.98  --bmc1_pre_inst_reach_state             false
% 2.93/0.98  --bmc1_out_unsat_core                   false
% 2.93/0.98  --bmc1_aig_witness_out                  false
% 2.93/0.98  --bmc1_verbose                          false
% 2.93/0.98  --bmc1_dump_clauses_tptp                false
% 2.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.98  --bmc1_dump_file                        -
% 2.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.98  --bmc1_ucm_extend_mode                  1
% 2.93/0.98  --bmc1_ucm_init_mode                    2
% 2.93/0.98  --bmc1_ucm_cone_mode                    none
% 2.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.98  --bmc1_ucm_relax_model                  4
% 2.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.98  --bmc1_ucm_layered_model                none
% 2.93/0.98  --bmc1_ucm_max_lemma_size               10
% 2.93/0.98  
% 2.93/0.98  ------ AIG Options
% 2.93/0.98  
% 2.93/0.98  --aig_mode                              false
% 2.93/0.98  
% 2.93/0.98  ------ Instantiation Options
% 2.93/0.98  
% 2.93/0.98  --instantiation_flag                    true
% 2.93/0.98  --inst_sos_flag                         false
% 2.93/0.98  --inst_sos_phase                        true
% 2.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel_side                     num_symb
% 2.93/0.98  --inst_solver_per_active                1400
% 2.93/0.98  --inst_solver_calls_frac                1.
% 2.93/0.98  --inst_passive_queue_type               priority_queues
% 2.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.98  --inst_passive_queues_freq              [25;2]
% 2.93/0.98  --inst_dismatching                      true
% 2.93/0.98  --inst_eager_unprocessed_to_passive     true
% 2.93/0.98  --inst_prop_sim_given                   true
% 2.93/0.98  --inst_prop_sim_new                     false
% 2.93/0.98  --inst_subs_new                         false
% 2.93/0.98  --inst_eq_res_simp                      false
% 2.93/0.98  --inst_subs_given                       false
% 2.93/0.98  --inst_orphan_elimination               true
% 2.93/0.98  --inst_learning_loop_flag               true
% 2.93/0.98  --inst_learning_start                   3000
% 2.93/0.98  --inst_learning_factor                  2
% 2.93/0.98  --inst_start_prop_sim_after_learn       3
% 2.93/0.98  --inst_sel_renew                        solver
% 2.93/0.98  --inst_lit_activity_flag                true
% 2.93/0.98  --inst_restr_to_given                   false
% 2.93/0.98  --inst_activity_threshold               500
% 2.93/0.98  --inst_out_proof                        true
% 2.93/0.98  
% 2.93/0.98  ------ Resolution Options
% 2.93/0.98  
% 2.93/0.98  --resolution_flag                       true
% 2.93/0.98  --res_lit_sel                           adaptive
% 2.93/0.98  --res_lit_sel_side                      none
% 2.93/0.98  --res_ordering                          kbo
% 2.93/0.98  --res_to_prop_solver                    active
% 2.93/0.98  --res_prop_simpl_new                    false
% 2.93/0.98  --res_prop_simpl_given                  true
% 2.93/0.98  --res_passive_queue_type                priority_queues
% 2.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.98  --res_passive_queues_freq               [15;5]
% 2.93/0.98  --res_forward_subs                      full
% 2.93/0.98  --res_backward_subs                     full
% 2.93/0.98  --res_forward_subs_resolution           true
% 2.93/0.98  --res_backward_subs_resolution          true
% 2.93/0.98  --res_orphan_elimination                true
% 2.93/0.98  --res_time_limit                        2.
% 2.93/0.98  --res_out_proof                         true
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Options
% 2.93/0.98  
% 2.93/0.98  --superposition_flag                    true
% 2.93/0.98  --sup_passive_queue_type                priority_queues
% 2.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.98  --demod_completeness_check              fast
% 2.93/0.98  --demod_use_ground                      true
% 2.93/0.98  --sup_to_prop_solver                    passive
% 2.93/0.98  --sup_prop_simpl_new                    true
% 2.93/0.98  --sup_prop_simpl_given                  true
% 2.93/0.98  --sup_fun_splitting                     false
% 2.93/0.98  --sup_smt_interval                      50000
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Simplification Setup
% 2.93/0.98  
% 2.93/0.98  --sup_indices_passive                   []
% 2.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_full_bw                           [BwDemod]
% 2.93/0.98  --sup_immed_triv                        [TrivRules]
% 2.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_immed_bw_main                     []
% 2.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  
% 2.93/0.98  ------ Combination Options
% 2.93/0.98  
% 2.93/0.98  --comb_res_mult                         3
% 2.93/0.98  --comb_sup_mult                         2
% 2.93/0.98  --comb_inst_mult                        10
% 2.93/0.98  
% 2.93/0.98  ------ Debug Options
% 2.93/0.98  
% 2.93/0.98  --dbg_backtrace                         false
% 2.93/0.98  --dbg_dump_prop_clauses                 false
% 2.93/0.98  --dbg_dump_prop_clauses_file            -
% 2.93/0.98  --dbg_out_stat                          false
% 2.93/0.98  ------ Parsing...
% 2.93/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/0.98  ------ Proving...
% 2.93/0.98  ------ Problem Properties 
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  clauses                                 35
% 2.93/0.98  conjectures                             3
% 2.93/0.98  EPR                                     1
% 2.93/0.98  Horn                                    28
% 2.93/0.98  unary                                   11
% 2.93/0.98  binary                                  8
% 2.93/0.98  lits                                    88
% 2.93/0.98  lits eq                                 41
% 2.93/0.98  fd_pure                                 0
% 2.93/0.98  fd_pseudo                               0
% 2.93/0.98  fd_cond                                 3
% 2.93/0.98  fd_pseudo_cond                          0
% 2.93/0.98  AC symbols                              0
% 2.93/0.98  
% 2.93/0.98  ------ Schedule dynamic 5 is on 
% 2.93/0.98  
% 2.93/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  ------ 
% 2.93/0.98  Current options:
% 2.93/0.98  ------ 
% 2.93/0.98  
% 2.93/0.98  ------ Input Options
% 2.93/0.98  
% 2.93/0.98  --out_options                           all
% 2.93/0.98  --tptp_safe_out                         true
% 2.93/0.98  --problem_path                          ""
% 2.93/0.98  --include_path                          ""
% 2.93/0.98  --clausifier                            res/vclausify_rel
% 2.93/0.98  --clausifier_options                    --mode clausify
% 2.93/0.98  --stdin                                 false
% 2.93/0.98  --stats_out                             all
% 2.93/0.98  
% 2.93/0.98  ------ General Options
% 2.93/0.98  
% 2.93/0.98  --fof                                   false
% 2.93/0.98  --time_out_real                         305.
% 2.93/0.98  --time_out_virtual                      -1.
% 2.93/0.98  --symbol_type_check                     false
% 2.93/0.98  --clausify_out                          false
% 2.93/0.98  --sig_cnt_out                           false
% 2.93/0.98  --trig_cnt_out                          false
% 2.93/0.98  --trig_cnt_out_tolerance                1.
% 2.93/0.98  --trig_cnt_out_sk_spl                   false
% 2.93/0.98  --abstr_cl_out                          false
% 2.93/0.98  
% 2.93/0.98  ------ Global Options
% 2.93/0.98  
% 2.93/0.98  --schedule                              default
% 2.93/0.98  --add_important_lit                     false
% 2.93/0.98  --prop_solver_per_cl                    1000
% 2.93/0.98  --min_unsat_core                        false
% 2.93/0.98  --soft_assumptions                      false
% 2.93/0.98  --soft_lemma_size                       3
% 2.93/0.98  --prop_impl_unit_size                   0
% 2.93/0.98  --prop_impl_unit                        []
% 2.93/0.98  --share_sel_clauses                     true
% 2.93/0.98  --reset_solvers                         false
% 2.93/0.98  --bc_imp_inh                            [conj_cone]
% 2.93/0.98  --conj_cone_tolerance                   3.
% 2.93/0.98  --extra_neg_conj                        none
% 2.93/0.98  --large_theory_mode                     true
% 2.93/0.98  --prolific_symb_bound                   200
% 2.93/0.98  --lt_threshold                          2000
% 2.93/0.98  --clause_weak_htbl                      true
% 2.93/0.98  --gc_record_bc_elim                     false
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing Options
% 2.93/0.98  
% 2.93/0.98  --preprocessing_flag                    true
% 2.93/0.98  --time_out_prep_mult                    0.1
% 2.93/0.98  --splitting_mode                        input
% 2.93/0.98  --splitting_grd                         true
% 2.93/0.98  --splitting_cvd                         false
% 2.93/0.98  --splitting_cvd_svl                     false
% 2.93/0.98  --splitting_nvd                         32
% 2.93/0.98  --sub_typing                            true
% 2.93/0.98  --prep_gs_sim                           true
% 2.93/0.98  --prep_unflatten                        true
% 2.93/0.98  --prep_res_sim                          true
% 2.93/0.98  --prep_upred                            true
% 2.93/0.98  --prep_sem_filter                       exhaustive
% 2.93/0.98  --prep_sem_filter_out                   false
% 2.93/0.98  --pred_elim                             true
% 2.93/0.98  --res_sim_input                         true
% 2.93/0.98  --eq_ax_congr_red                       true
% 2.93/0.98  --pure_diseq_elim                       true
% 2.93/0.98  --brand_transform                       false
% 2.93/0.98  --non_eq_to_eq                          false
% 2.93/0.98  --prep_def_merge                        true
% 2.93/0.98  --prep_def_merge_prop_impl              false
% 2.93/0.98  --prep_def_merge_mbd                    true
% 2.93/0.98  --prep_def_merge_tr_red                 false
% 2.93/0.98  --prep_def_merge_tr_cl                  false
% 2.93/0.98  --smt_preprocessing                     true
% 2.93/0.98  --smt_ac_axioms                         fast
% 2.93/0.98  --preprocessed_out                      false
% 2.93/0.98  --preprocessed_stats                    false
% 2.93/0.98  
% 2.93/0.98  ------ Abstraction refinement Options
% 2.93/0.98  
% 2.93/0.98  --abstr_ref                             []
% 2.93/0.98  --abstr_ref_prep                        false
% 2.93/0.98  --abstr_ref_until_sat                   false
% 2.93/0.98  --abstr_ref_sig_restrict                funpre
% 2.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.98  --abstr_ref_under                       []
% 2.93/0.98  
% 2.93/0.98  ------ SAT Options
% 2.93/0.98  
% 2.93/0.98  --sat_mode                              false
% 2.93/0.98  --sat_fm_restart_options                ""
% 2.93/0.98  --sat_gr_def                            false
% 2.93/0.98  --sat_epr_types                         true
% 2.93/0.98  --sat_non_cyclic_types                  false
% 2.93/0.98  --sat_finite_models                     false
% 2.93/0.98  --sat_fm_lemmas                         false
% 2.93/0.98  --sat_fm_prep                           false
% 2.93/0.98  --sat_fm_uc_incr                        true
% 2.93/0.98  --sat_out_model                         small
% 2.93/0.98  --sat_out_clauses                       false
% 2.93/0.98  
% 2.93/0.98  ------ QBF Options
% 2.93/0.98  
% 2.93/0.98  --qbf_mode                              false
% 2.93/0.98  --qbf_elim_univ                         false
% 2.93/0.98  --qbf_dom_inst                          none
% 2.93/0.98  --qbf_dom_pre_inst                      false
% 2.93/0.98  --qbf_sk_in                             false
% 2.93/0.98  --qbf_pred_elim                         true
% 2.93/0.98  --qbf_split                             512
% 2.93/0.98  
% 2.93/0.98  ------ BMC1 Options
% 2.93/0.98  
% 2.93/0.98  --bmc1_incremental                      false
% 2.93/0.98  --bmc1_axioms                           reachable_all
% 2.93/0.98  --bmc1_min_bound                        0
% 2.93/0.98  --bmc1_max_bound                        -1
% 2.93/0.98  --bmc1_max_bound_default                -1
% 2.93/0.98  --bmc1_symbol_reachability              true
% 2.93/0.98  --bmc1_property_lemmas                  false
% 2.93/0.98  --bmc1_k_induction                      false
% 2.93/0.98  --bmc1_non_equiv_states                 false
% 2.93/0.98  --bmc1_deadlock                         false
% 2.93/0.98  --bmc1_ucm                              false
% 2.93/0.98  --bmc1_add_unsat_core                   none
% 2.93/0.98  --bmc1_unsat_core_children              false
% 2.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.98  --bmc1_out_stat                         full
% 2.93/0.98  --bmc1_ground_init                      false
% 2.93/0.98  --bmc1_pre_inst_next_state              false
% 2.93/0.98  --bmc1_pre_inst_state                   false
% 2.93/0.98  --bmc1_pre_inst_reach_state             false
% 2.93/0.98  --bmc1_out_unsat_core                   false
% 2.93/0.98  --bmc1_aig_witness_out                  false
% 2.93/0.98  --bmc1_verbose                          false
% 2.93/0.98  --bmc1_dump_clauses_tptp                false
% 2.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.98  --bmc1_dump_file                        -
% 2.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.98  --bmc1_ucm_extend_mode                  1
% 2.93/0.98  --bmc1_ucm_init_mode                    2
% 2.93/0.98  --bmc1_ucm_cone_mode                    none
% 2.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.98  --bmc1_ucm_relax_model                  4
% 2.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.98  --bmc1_ucm_layered_model                none
% 2.93/0.98  --bmc1_ucm_max_lemma_size               10
% 2.93/0.98  
% 2.93/0.98  ------ AIG Options
% 2.93/0.98  
% 2.93/0.98  --aig_mode                              false
% 2.93/0.98  
% 2.93/0.98  ------ Instantiation Options
% 2.93/0.98  
% 2.93/0.98  --instantiation_flag                    true
% 2.93/0.98  --inst_sos_flag                         false
% 2.93/0.98  --inst_sos_phase                        true
% 2.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel_side                     none
% 2.93/0.98  --inst_solver_per_active                1400
% 2.93/0.98  --inst_solver_calls_frac                1.
% 2.93/0.98  --inst_passive_queue_type               priority_queues
% 2.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.98  --inst_passive_queues_freq              [25;2]
% 2.93/0.98  --inst_dismatching                      true
% 2.93/0.98  --inst_eager_unprocessed_to_passive     true
% 2.93/0.98  --inst_prop_sim_given                   true
% 2.93/0.98  --inst_prop_sim_new                     false
% 2.93/0.98  --inst_subs_new                         false
% 2.93/0.98  --inst_eq_res_simp                      false
% 2.93/0.98  --inst_subs_given                       false
% 2.93/0.98  --inst_orphan_elimination               true
% 2.93/0.98  --inst_learning_loop_flag               true
% 2.93/0.98  --inst_learning_start                   3000
% 2.93/0.98  --inst_learning_factor                  2
% 2.93/0.98  --inst_start_prop_sim_after_learn       3
% 2.93/0.98  --inst_sel_renew                        solver
% 2.93/0.98  --inst_lit_activity_flag                true
% 2.93/0.98  --inst_restr_to_given                   false
% 2.93/0.98  --inst_activity_threshold               500
% 2.93/0.98  --inst_out_proof                        true
% 2.93/0.98  
% 2.93/0.98  ------ Resolution Options
% 2.93/0.98  
% 2.93/0.98  --resolution_flag                       false
% 2.93/0.98  --res_lit_sel                           adaptive
% 2.93/0.98  --res_lit_sel_side                      none
% 2.93/0.98  --res_ordering                          kbo
% 2.93/0.98  --res_to_prop_solver                    active
% 2.93/0.98  --res_prop_simpl_new                    false
% 2.93/0.98  --res_prop_simpl_given                  true
% 2.93/0.98  --res_passive_queue_type                priority_queues
% 2.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.98  --res_passive_queues_freq               [15;5]
% 2.93/0.98  --res_forward_subs                      full
% 2.93/0.98  --res_backward_subs                     full
% 2.93/0.98  --res_forward_subs_resolution           true
% 2.93/0.98  --res_backward_subs_resolution          true
% 2.93/0.98  --res_orphan_elimination                true
% 2.93/0.98  --res_time_limit                        2.
% 2.93/0.98  --res_out_proof                         true
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Options
% 2.93/0.98  
% 2.93/0.98  --superposition_flag                    true
% 2.93/0.98  --sup_passive_queue_type                priority_queues
% 2.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.98  --demod_completeness_check              fast
% 2.93/0.98  --demod_use_ground                      true
% 2.93/0.98  --sup_to_prop_solver                    passive
% 2.93/0.98  --sup_prop_simpl_new                    true
% 2.93/0.98  --sup_prop_simpl_given                  true
% 2.93/0.98  --sup_fun_splitting                     false
% 2.93/0.98  --sup_smt_interval                      50000
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Simplification Setup
% 2.93/0.98  
% 2.93/0.98  --sup_indices_passive                   []
% 2.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_full_bw                           [BwDemod]
% 2.93/0.98  --sup_immed_triv                        [TrivRules]
% 2.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_immed_bw_main                     []
% 2.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  
% 2.93/0.98  ------ Combination Options
% 2.93/0.98  
% 2.93/0.98  --comb_res_mult                         3
% 2.93/0.98  --comb_sup_mult                         2
% 2.93/0.98  --comb_inst_mult                        10
% 2.93/0.98  
% 2.93/0.98  ------ Debug Options
% 2.93/0.98  
% 2.93/0.98  --dbg_backtrace                         false
% 2.93/0.98  --dbg_dump_prop_clauses                 false
% 2.93/0.98  --dbg_dump_prop_clauses_file            -
% 2.93/0.98  --dbg_out_stat                          false
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  ------ Proving...
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  % SZS status Theorem for theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  fof(f11,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f29,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(ennf_transformation,[],[f11])).
% 2.93/0.98  
% 2.93/0.98  fof(f30,plain,(
% 2.93/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(flattening,[],[f29])).
% 2.93/0.98  
% 2.93/0.98  fof(f37,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(nnf_transformation,[],[f30])).
% 2.93/0.98  
% 2.93/0.98  fof(f56,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f37])).
% 2.93/0.98  
% 2.93/0.98  fof(f14,conjecture,(
% 2.93/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f15,negated_conjecture,(
% 2.93/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.93/0.98    inference(negated_conjecture,[],[f14])).
% 2.93/0.98  
% 2.93/0.98  fof(f33,plain,(
% 2.93/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.93/0.98    inference(ennf_transformation,[],[f15])).
% 2.93/0.98  
% 2.93/0.98  fof(f34,plain,(
% 2.93/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.93/0.98    inference(flattening,[],[f33])).
% 2.93/0.98  
% 2.93/0.98  fof(f40,plain,(
% 2.93/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.93/0.98    introduced(choice_axiom,[])).
% 2.93/0.98  
% 2.93/0.98  fof(f41,plain,(
% 2.93/0.98    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.93/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f40])).
% 2.93/0.98  
% 2.93/0.98  fof(f70,plain,(
% 2.93/0.98    v1_funct_2(sK3,sK1,sK2)),
% 2.93/0.98    inference(cnf_transformation,[],[f41])).
% 2.93/0.98  
% 2.93/0.98  fof(f71,plain,(
% 2.93/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.93/0.98    inference(cnf_transformation,[],[f41])).
% 2.93/0.98  
% 2.93/0.98  fof(f9,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f27,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(ennf_transformation,[],[f9])).
% 2.93/0.98  
% 2.93/0.98  fof(f54,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f27])).
% 2.93/0.98  
% 2.93/0.98  fof(f10,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f28,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(ennf_transformation,[],[f10])).
% 2.93/0.98  
% 2.93/0.98  fof(f55,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f28])).
% 2.93/0.98  
% 2.93/0.98  fof(f73,plain,(
% 2.93/0.98    k2_relset_1(sK1,sK2,sK3) = sK2),
% 2.93/0.98    inference(cnf_transformation,[],[f41])).
% 2.93/0.98  
% 2.93/0.98  fof(f7,axiom,(
% 2.93/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f24,plain,(
% 2.93/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.93/0.98    inference(ennf_transformation,[],[f7])).
% 2.93/0.98  
% 2.93/0.98  fof(f25,plain,(
% 2.93/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/0.98    inference(flattening,[],[f24])).
% 2.93/0.98  
% 2.93/0.98  fof(f51,plain,(
% 2.93/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f25])).
% 2.93/0.98  
% 2.93/0.98  fof(f72,plain,(
% 2.93/0.98    v2_funct_1(sK3)),
% 2.93/0.98    inference(cnf_transformation,[],[f41])).
% 2.93/0.98  
% 2.93/0.98  fof(f69,plain,(
% 2.93/0.98    v1_funct_1(sK3)),
% 2.93/0.98    inference(cnf_transformation,[],[f41])).
% 2.93/0.98  
% 2.93/0.98  fof(f8,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f26,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(ennf_transformation,[],[f8])).
% 2.93/0.98  
% 2.93/0.98  fof(f53,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f26])).
% 2.93/0.98  
% 2.93/0.98  fof(f13,axiom,(
% 2.93/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f31,plain,(
% 2.93/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.93/0.98    inference(ennf_transformation,[],[f13])).
% 2.93/0.98  
% 2.93/0.98  fof(f32,plain,(
% 2.93/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/0.98    inference(flattening,[],[f31])).
% 2.93/0.98  
% 2.93/0.98  fof(f68,plain,(
% 2.93/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f32])).
% 2.93/0.98  
% 2.93/0.98  fof(f52,plain,(
% 2.93/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f25])).
% 2.93/0.98  
% 2.93/0.98  fof(f6,axiom,(
% 2.93/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f22,plain,(
% 2.93/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.93/0.98    inference(ennf_transformation,[],[f6])).
% 2.93/0.98  
% 2.93/0.98  fof(f23,plain,(
% 2.93/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/0.98    inference(flattening,[],[f22])).
% 2.93/0.98  
% 2.93/0.98  fof(f50,plain,(
% 2.93/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f23])).
% 2.93/0.98  
% 2.93/0.98  fof(f49,plain,(
% 2.93/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f23])).
% 2.93/0.98  
% 2.93/0.98  fof(f67,plain,(
% 2.93/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f32])).
% 2.93/0.98  
% 2.93/0.98  fof(f74,plain,(
% 2.93/0.98    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 2.93/0.98    inference(cnf_transformation,[],[f41])).
% 2.93/0.98  
% 2.93/0.98  fof(f60,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f37])).
% 2.93/0.98  
% 2.93/0.98  fof(f79,plain,(
% 2.93/0.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.93/0.98    inference(equality_resolution,[],[f60])).
% 2.93/0.98  
% 2.93/0.98  fof(f2,axiom,(
% 2.93/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f35,plain,(
% 2.93/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.93/0.98    inference(nnf_transformation,[],[f2])).
% 2.93/0.98  
% 2.93/0.98  fof(f36,plain,(
% 2.93/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.93/0.98    inference(flattening,[],[f35])).
% 2.93/0.98  
% 2.93/0.98  fof(f45,plain,(
% 2.93/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.93/0.98    inference(cnf_transformation,[],[f36])).
% 2.93/0.98  
% 2.93/0.98  fof(f75,plain,(
% 2.93/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.93/0.98    inference(equality_resolution,[],[f45])).
% 2.93/0.98  
% 2.93/0.98  fof(f57,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f37])).
% 2.93/0.98  
% 2.93/0.98  fof(f81,plain,(
% 2.93/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.93/0.98    inference(equality_resolution,[],[f57])).
% 2.93/0.98  
% 2.93/0.98  fof(f44,plain,(
% 2.93/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.93/0.98    inference(cnf_transformation,[],[f36])).
% 2.93/0.98  
% 2.93/0.98  fof(f76,plain,(
% 2.93/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.93/0.98    inference(equality_resolution,[],[f44])).
% 2.93/0.98  
% 2.93/0.98  fof(f59,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f37])).
% 2.93/0.98  
% 2.93/0.98  fof(f80,plain,(
% 2.93/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.93/0.98    inference(equality_resolution,[],[f59])).
% 2.93/0.98  
% 2.93/0.98  fof(f43,plain,(
% 2.93/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f36])).
% 2.93/0.98  
% 2.93/0.98  cnf(c_19,plain,
% 2.93/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.93/0.98      | k1_xboole_0 = X2 ),
% 2.93/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_31,negated_conjecture,
% 2.93/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.93/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_585,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.93/0.98      | sK1 != X1
% 2.93/0.98      | sK2 != X2
% 2.93/0.98      | sK3 != X0
% 2.93/0.98      | k1_xboole_0 = X2 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_586,plain,
% 2.93/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/0.98      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.93/0.98      | k1_xboole_0 = sK2 ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_585]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_30,negated_conjecture,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.93/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_588,plain,
% 2.93/0.98      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_586,c_30]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1175,plain,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_12,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1181,plain,
% 2.93/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.93/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2385,plain,
% 2.93/0.98      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1175,c_1181]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2461,plain,
% 2.93/0.98      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_588,c_2385]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_13,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1180,plain,
% 2.93/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.93/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2158,plain,
% 2.93/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1175,c_1180]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_28,negated_conjecture,
% 2.93/0.98      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.93/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2173,plain,
% 2.93/0.98      ( k2_relat_1(sK3) = sK2 ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_2158,c_28]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_10,plain,
% 2.93/0.98      ( ~ v2_funct_1(X0)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_29,negated_conjecture,
% 2.93/0.98      ( v2_funct_1(sK3) ),
% 2.93/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_341,plain,
% 2.93/0.98      ( ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.93/0.98      | sK3 != X0 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_342,plain,
% 2.93/0.98      ( ~ v1_funct_1(sK3)
% 2.93/0.98      | ~ v1_relat_1(sK3)
% 2.93/0.98      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_341]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_32,negated_conjecture,
% 2.93/0.98      ( v1_funct_1(sK3) ),
% 2.93/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_344,plain,
% 2.93/0.98      ( ~ v1_relat_1(sK3)
% 2.93/0.98      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_342,c_32]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1172,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 2.93/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_11,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | v1_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1451,plain,
% 2.93/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.93/0.98      | v1_relat_1(sK3) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1477,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_1172,c_32,c_30,c_342,c_1451]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2282,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_2173,c_1477]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_24,plain,
% 2.93/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1176,plain,
% 2.93/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top
% 2.93/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2457,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK3))))) = iProver_top
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.93/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_2282,c_1176]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_9,plain,
% 2.93/0.98      ( ~ v2_funct_1(X0)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_355,plain,
% 2.93/0.98      ( ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.93/0.98      | sK3 != X0 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_356,plain,
% 2.93/0.98      ( ~ v1_funct_1(sK3)
% 2.93/0.98      | ~ v1_relat_1(sK3)
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_355]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_358,plain,
% 2.93/0.98      ( ~ v1_relat_1(sK3)
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_356,c_32]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1171,plain,
% 2.93/0.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 2.93/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1473,plain,
% 2.93/0.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_1171,c_32,c_30,c_356,c_1451]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2458,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.93/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_2457,c_1473]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_33,plain,
% 2.93/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_35,plain,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_7,plain,
% 2.93/0.98      ( ~ v1_funct_1(X0)
% 2.93/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.93/0.98      | ~ v1_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1439,plain,
% 2.93/0.98      ( v1_funct_1(k2_funct_1(sK3))
% 2.93/0.98      | ~ v1_funct_1(sK3)
% 2.93/0.98      | ~ v1_relat_1(sK3) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1440,plain,
% 2.93/0.98      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.93/0.98      | v1_funct_1(sK3) != iProver_top
% 2.93/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1439]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_8,plain,
% 2.93/0.98      ( ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 2.93/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1447,plain,
% 2.93/0.98      ( ~ v1_funct_1(sK3)
% 2.93/0.98      | v1_relat_1(k2_funct_1(sK3))
% 2.93/0.98      | ~ v1_relat_1(sK3) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1448,plain,
% 2.93/0.98      ( v1_funct_1(sK3) != iProver_top
% 2.93/0.98      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 2.93/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1447]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1452,plain,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.93/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3136,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_2458,c_33,c_35,c_1440,c_1448,c_1452]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3143,plain,
% 2.93/0.98      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_3136,c_1181]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3152,plain,
% 2.93/0.98      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_3143,c_2282]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3204,plain,
% 2.93/0.98      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_2461,c_3152]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_25,plain,
% 2.93/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_27,negated_conjecture,
% 2.93/0.98      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 2.93/0.98      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.93/0.98      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 2.93/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_609,plain,
% 2.93/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k1_relat_1(X0) != sK2
% 2.93/0.98      | k2_relat_1(X0) != sK1
% 2.93/0.98      | k2_funct_1(sK3) != X0 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_610,plain,
% 2.93/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.93/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.93/0.98      | ~ v1_relat_1(k2_funct_1(sK3))
% 2.93/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_609]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_622,plain,
% 2.93/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.93/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.93/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.93/0.98      inference(forward_subsumption_resolution,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_610,c_11]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1161,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_611,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.93/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1577,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.93/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_1161,c_33,c_35,c_611,c_1440,c_1448,c_1452]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1578,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.93/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.93/0.98      inference(renaming,[status(thm)],[c_1577]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1581,plain,
% 2.93/0.98      ( k1_relat_1(sK3) != sK1
% 2.93/0.98      | k2_relat_1(sK3) != sK2
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_1578,c_1473,c_1477]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2281,plain,
% 2.93/0.98      ( k1_relat_1(sK3) != sK1
% 2.93/0.98      | sK2 != sK2
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_2173,c_1581]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2285,plain,
% 2.93/0.98      ( k1_relat_1(sK3) != sK1
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.93/0.98      inference(equality_resolution_simp,[status(thm)],[c_2281]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2758,plain,
% 2.93/0.98      ( sK2 = k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_2461,c_2285]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3141,plain,
% 2.93/0.98      ( sK2 = k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_2461,c_3136]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3352,plain,
% 2.93/0.98      ( sK2 = k1_xboole_0 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_3204,c_2758,c_3141]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3364,plain,
% 2.93/0.98      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3352,c_2173]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_15,plain,
% 2.93/0.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.93/0.98      | k1_xboole_0 = X1
% 2.93/0.98      | k1_xboole_0 = X0 ),
% 2.93/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_421,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.93/0.98      | ~ v1_funct_1(X2)
% 2.93/0.98      | ~ v1_relat_1(X2)
% 2.93/0.98      | X2 != X0
% 2.93/0.98      | k1_relat_1(X2) != X1
% 2.93/0.98      | k2_relat_1(X2) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = X1
% 2.93/0.98      | k1_xboole_0 = X0 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_422,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k2_relat_1(X0) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = X0
% 2.93/0.98      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_421]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_438,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | k2_relat_1(X0) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = X0
% 2.93/0.98      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.93/0.98      inference(forward_subsumption_resolution,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_422,c_11]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1169,plain,
% 2.93/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = X0
% 2.93/0.98      | k1_xboole_0 = k1_relat_1(X0)
% 2.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1,plain,
% 2.93/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.93/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1336,plain,
% 2.93/0.98      ( k1_relat_1(X0) = k1_xboole_0
% 2.93/0.98      | k2_relat_1(X0) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = X0
% 2.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_1169,c_1]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3719,plain,
% 2.93/0.98      ( k1_relat_1(sK3) = k1_xboole_0
% 2.93/0.98      | sK3 = k1_xboole_0
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_3364,c_1336]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3373,plain,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3352,c_1175]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3378,plain,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3373,c_1]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4076,plain,
% 2.93/0.98      ( k1_relat_1(sK3) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_3719,c_33,c_3378]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_18,plain,
% 2.93/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.93/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.93/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_479,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.93/0.98      | ~ v1_funct_1(X2)
% 2.93/0.98      | ~ v1_relat_1(X2)
% 2.93/0.98      | X2 != X0
% 2.93/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.93/0.98      | k1_relat_1(X2) != k1_xboole_0
% 2.93/0.98      | k2_relat_1(X2) != X1 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_480,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.93/0.98      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_479]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_494,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.93/0.98      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.93/0.98      inference(forward_subsumption_resolution,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_480,c_11]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1167,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.93/0.98      | k1_relat_1(X0) != k1_xboole_0
% 2.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2,plain,
% 2.93/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.93/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1319,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 2.93/0.98      | k1_relat_1(X0) != k1_xboole_0
% 2.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_1167,c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4081,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK3),sK3) = k1_xboole_0
% 2.93/0.98      | sK3 = k1_xboole_0
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_4076,c_1319]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4099,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.93/0.98      | sK3 = k1_xboole_0
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_4081,c_3364]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_447,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.93/0.98      | sK1 != X1
% 2.93/0.98      | sK2 != k1_xboole_0
% 2.93/0.98      | sK3 != X0
% 2.93/0.98      | k1_xboole_0 = X1
% 2.93/0.98      | k1_xboole_0 = X0 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_448,plain,
% 2.93/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.93/0.98      | sK2 != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = sK1
% 2.93/0.98      | k1_xboole_0 = sK3 ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_447]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1168,plain,
% 2.93/0.98      ( sK2 != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = sK1
% 2.93/0.98      | k1_xboole_0 = sK3
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1266,plain,
% 2.93/0.98      ( sK1 = k1_xboole_0
% 2.93/0.98      | sK2 != k1_xboole_0
% 2.93/0.98      | sK3 = k1_xboole_0
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_1168,c_1]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3365,plain,
% 2.93/0.98      ( sK1 = k1_xboole_0
% 2.93/0.98      | sK3 = k1_xboole_0
% 2.93/0.98      | k1_xboole_0 != k1_xboole_0
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3352,c_1266]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3412,plain,
% 2.93/0.98      ( sK1 = k1_xboole_0
% 2.93/0.98      | sK3 = k1_xboole_0
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(equality_resolution_simp,[status(thm)],[c_3365]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3416,plain,
% 2.93/0.98      ( sK1 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.93/0.98      inference(forward_subsumption_resolution,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_3412,c_3378]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3357,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3352,c_3136]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3437,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3357,c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3358,plain,
% 2.93/0.98      ( k1_relat_1(sK3) != sK1
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3352,c_2285]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3433,plain,
% 2.93/0.98      ( k1_relat_1(sK3) != sK1
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3358,c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3441,plain,
% 2.93/0.98      ( k1_relat_1(sK3) != sK1 ),
% 2.93/0.98      inference(backward_subsumption_resolution,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_3437,c_3433]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4083,plain,
% 2.93/0.98      ( sK1 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_4076,c_3441]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4302,plain,
% 2.93/0.98      ( sK3 = k1_xboole_0 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_4099,c_3416,c_4083]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4314,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_4302,c_3437]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2388,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.93/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_2,c_1181]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5003,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_4314,c_2388]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3363,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3352,c_2282]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4312,plain,
% 2.93/0.98      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_4302,c_3363]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5015,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_5003,c_4312]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_16,plain,
% 2.93/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.93/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.93/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_502,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.93/0.98      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.93/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.93/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.93/0.98      | k2_funct_1(sK3) != X0
% 2.93/0.98      | sK1 != X1
% 2.93/0.98      | sK2 != k1_xboole_0 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_503,plain,
% 2.93/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.93/0.98      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.93/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.93/0.98      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.93/0.98      | sK2 != k1_xboole_0 ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_502]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1166,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.93/0.98      | sK2 != k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1357,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.93/0.98      | sK2 != k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_1166,c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1733,plain,
% 2.93/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.93/0.98      | sK2 != k1_xboole_0
% 2.93/0.98      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_1357,c_33,c_35,c_1440,c_1452]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1734,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.93/0.98      | sK2 != k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(renaming,[status(thm)],[c_1733]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3366,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 != k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3352,c_1734]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3405,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(equality_resolution_simp,[status(thm)],[c_3366]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3409,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 2.93/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3405,c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3440,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 2.93/0.98      inference(backward_subsumption_resolution,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_3437,c_3409]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5180,plain,
% 2.93/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_3440,c_4302]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5898,plain,
% 2.93/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_5015,c_5180]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_104,plain,
% 2.93/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3,plain,
% 2.93/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = X1
% 2.93/0.98      | k1_xboole_0 = X0 ),
% 2.93/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_103,plain,
% 2.93/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.93/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(contradiction,plain,
% 2.93/0.98      ( $false ),
% 2.93/0.98      inference(minisat,[status(thm)],[c_5898,c_104,c_103]) ).
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  ------                               Statistics
% 2.93/0.98  
% 2.93/0.98  ------ General
% 2.93/0.98  
% 2.93/0.98  abstr_ref_over_cycles:                  0
% 2.93/0.98  abstr_ref_under_cycles:                 0
% 2.93/0.98  gc_basic_clause_elim:                   0
% 2.93/0.98  forced_gc_time:                         0
% 2.93/0.98  parsing_time:                           0.009
% 2.93/0.98  unif_index_cands_time:                  0.
% 2.93/0.98  unif_index_add_time:                    0.
% 2.93/0.98  orderings_time:                         0.
% 2.93/0.98  out_proof_time:                         0.008
% 2.93/0.98  total_time:                             0.188
% 2.93/0.98  num_of_symbols:                         49
% 2.93/0.98  num_of_terms:                           4279
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing
% 2.93/0.98  
% 2.93/0.98  num_of_splits:                          0
% 2.93/0.98  num_of_split_atoms:                     0
% 2.93/0.98  num_of_reused_defs:                     0
% 2.93/0.98  num_eq_ax_congr_red:                    5
% 2.93/0.98  num_of_sem_filtered_clauses:            1
% 2.93/0.98  num_of_subtypes:                        0
% 2.93/0.98  monotx_restored_types:                  0
% 2.93/0.98  sat_num_of_epr_types:                   0
% 2.93/0.98  sat_num_of_non_cyclic_types:            0
% 2.93/0.98  sat_guarded_non_collapsed_types:        0
% 2.93/0.98  num_pure_diseq_elim:                    0
% 2.93/0.98  simp_replaced_by:                       0
% 2.93/0.98  res_preprocessed:                       129
% 2.93/0.98  prep_upred:                             0
% 2.93/0.98  prep_unflattend:                        56
% 2.93/0.98  smt_new_axioms:                         0
% 2.93/0.98  pred_elim_cands:                        6
% 2.93/0.98  pred_elim:                              3
% 2.93/0.98  pred_elim_cl:                           -3
% 2.93/0.98  pred_elim_cycles:                       4
% 2.93/0.98  merged_defs:                            0
% 2.93/0.98  merged_defs_ncl:                        0
% 2.93/0.98  bin_hyper_res:                          0
% 2.93/0.98  prep_cycles:                            3
% 2.93/0.98  pred_elim_time:                         0.009
% 2.93/0.98  splitting_time:                         0.
% 2.93/0.98  sem_filter_time:                        0.
% 2.93/0.98  monotx_time:                            0.
% 2.93/0.98  subtype_inf_time:                       0.
% 2.93/0.98  
% 2.93/0.98  ------ Problem properties
% 2.93/0.98  
% 2.93/0.98  clauses:                                35
% 2.93/0.98  conjectures:                            3
% 2.93/0.98  epr:                                    1
% 2.93/0.98  horn:                                   28
% 2.93/0.98  ground:                                 14
% 2.93/0.98  unary:                                  11
% 2.93/0.98  binary:                                 8
% 2.93/0.98  lits:                                   88
% 2.93/0.98  lits_eq:                                41
% 2.93/0.98  fd_pure:                                0
% 2.93/0.98  fd_pseudo:                              0
% 2.93/0.98  fd_cond:                                3
% 2.93/0.98  fd_pseudo_cond:                         0
% 2.93/0.98  ac_symbols:                             0
% 2.93/0.98  
% 2.93/0.98  ------ Propositional Solver
% 2.93/0.98  
% 2.93/0.98  prop_solver_calls:                      24
% 2.93/0.98  prop_fast_solver_calls:                 971
% 2.93/0.98  smt_solver_calls:                       0
% 2.93/0.98  smt_fast_solver_calls:                  0
% 2.93/0.98  prop_num_of_clauses:                    1957
% 2.93/0.98  prop_preprocess_simplified:             5230
% 2.93/0.98  prop_fo_subsumed:                       34
% 2.93/0.98  prop_solver_time:                       0.
% 2.93/0.98  smt_solver_time:                        0.
% 2.93/0.98  smt_fast_solver_time:                   0.
% 2.93/0.98  prop_fast_solver_time:                  0.
% 2.93/0.98  prop_unsat_core_time:                   0.
% 2.93/0.98  
% 2.93/0.98  ------ QBF
% 2.93/0.98  
% 2.93/0.98  qbf_q_res:                              0
% 2.93/0.98  qbf_num_tautologies:                    0
% 2.93/0.98  qbf_prep_cycles:                        0
% 2.93/0.98  
% 2.93/0.98  ------ BMC1
% 2.93/0.98  
% 2.93/0.98  bmc1_current_bound:                     -1
% 2.93/0.98  bmc1_last_solved_bound:                 -1
% 2.93/0.98  bmc1_unsat_core_size:                   -1
% 2.93/0.98  bmc1_unsat_core_parents_size:           -1
% 2.93/0.98  bmc1_merge_next_fun:                    0
% 2.93/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.93/0.98  
% 2.93/0.98  ------ Instantiation
% 2.93/0.98  
% 2.93/0.98  inst_num_of_clauses:                    783
% 2.93/0.98  inst_num_in_passive:                    19
% 2.93/0.98  inst_num_in_active:                     389
% 2.93/0.98  inst_num_in_unprocessed:                383
% 2.93/0.98  inst_num_of_loops:                      500
% 2.93/0.98  inst_num_of_learning_restarts:          0
% 2.93/0.98  inst_num_moves_active_passive:          108
% 2.93/0.98  inst_lit_activity:                      0
% 2.93/0.98  inst_lit_activity_moves:                0
% 2.93/0.98  inst_num_tautologies:                   0
% 2.93/0.98  inst_num_prop_implied:                  0
% 2.93/0.98  inst_num_existing_simplified:           0
% 2.93/0.98  inst_num_eq_res_simplified:             0
% 2.93/0.98  inst_num_child_elim:                    0
% 2.93/0.98  inst_num_of_dismatching_blockings:      274
% 2.93/0.98  inst_num_of_non_proper_insts:           611
% 2.93/0.98  inst_num_of_duplicates:                 0
% 2.93/0.98  inst_inst_num_from_inst_to_res:         0
% 2.93/0.98  inst_dismatching_checking_time:         0.
% 2.93/0.98  
% 2.93/0.98  ------ Resolution
% 2.93/0.98  
% 2.93/0.98  res_num_of_clauses:                     0
% 2.93/0.98  res_num_in_passive:                     0
% 2.93/0.98  res_num_in_active:                      0
% 2.93/0.98  res_num_of_loops:                       132
% 2.93/0.98  res_forward_subset_subsumed:            62
% 2.93/0.98  res_backward_subset_subsumed:           16
% 2.93/0.98  res_forward_subsumed:                   0
% 2.93/0.98  res_backward_subsumed:                  0
% 2.93/0.98  res_forward_subsumption_resolution:     5
% 2.93/0.98  res_backward_subsumption_resolution:    1
% 2.93/0.98  res_clause_to_clause_subsumption:       252
% 2.93/0.98  res_orphan_elimination:                 0
% 2.93/0.98  res_tautology_del:                      140
% 2.93/0.98  res_num_eq_res_simplified:              0
% 2.93/0.98  res_num_sel_changes:                    0
% 2.93/0.98  res_moves_from_active_to_pass:          0
% 2.93/0.98  
% 2.93/0.98  ------ Superposition
% 2.93/0.98  
% 2.93/0.98  sup_time_total:                         0.
% 2.93/0.98  sup_time_generating:                    0.
% 2.93/0.98  sup_time_sim_full:                      0.
% 2.93/0.98  sup_time_sim_immed:                     0.
% 2.93/0.98  
% 2.93/0.98  sup_num_of_clauses:                     86
% 2.93/0.98  sup_num_in_active:                      55
% 2.93/0.98  sup_num_in_passive:                     31
% 2.93/0.98  sup_num_of_loops:                       98
% 2.93/0.98  sup_fw_superposition:                   70
% 2.93/0.98  sup_bw_superposition:                   53
% 2.93/0.98  sup_immediate_simplified:               72
% 2.93/0.98  sup_given_eliminated:                   0
% 2.93/0.98  comparisons_done:                       0
% 2.93/0.98  comparisons_avoided:                    10
% 2.93/0.98  
% 2.93/0.98  ------ Simplifications
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  sim_fw_subset_subsumed:                 16
% 2.93/0.98  sim_bw_subset_subsumed:                 4
% 2.93/0.98  sim_fw_subsumed:                        21
% 2.93/0.98  sim_bw_subsumed:                        2
% 2.93/0.98  sim_fw_subsumption_res:                 2
% 2.93/0.98  sim_bw_subsumption_res:                 4
% 2.93/0.98  sim_tautology_del:                      2
% 2.93/0.98  sim_eq_tautology_del:                   11
% 2.93/0.98  sim_eq_res_simp:                        3
% 2.93/0.98  sim_fw_demodulated:                     22
% 2.93/0.98  sim_bw_demodulated:                     42
% 2.93/0.98  sim_light_normalised:                   45
% 2.93/0.98  sim_joinable_taut:                      0
% 2.93/0.98  sim_joinable_simp:                      0
% 2.93/0.98  sim_ac_normalised:                      0
% 2.93/0.98  sim_smt_subsumption:                    0
% 2.93/0.98  
%------------------------------------------------------------------------------
