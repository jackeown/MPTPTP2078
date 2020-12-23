%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:34 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  167 (7685 expanded)
%              Number of clauses        :  107 (2298 expanded)
%              Number of leaves         :   13 (1520 expanded)
%              Depth                    :   27
%              Number of atoms          :  511 (42431 expanded)
%              Number of equality atoms :  264 (8354 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f26])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
        | ~ v1_funct_1(k2_funct_1(sK6)) )
      & k2_relset_1(sK4,sK5,sK6) = sK5
      & v2_funct_1(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & k2_relset_1(sK4,sK5,sK6) = sK5
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f45])).

fof(f78,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_999,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X1
    | sK5 != X2
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_999])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1002,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_33])).

cnf(c_1632,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1635,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3059,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1632,c_1635])).

cnf(c_3287,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1002,c_3059])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1634,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2747,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1632,c_1634])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2759,plain,
    ( k2_relat_1(sK6) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_2747,c_31])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_336,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_337,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_339,plain,
    ( ~ v1_relat_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_35])).

cnf(c_1630,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1922,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1930,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_35,c_33,c_337,c_1922])).

cnf(c_2817,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = sK5 ),
    inference(demodulation,[status(thm)],[c_2759,c_1930])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3283,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6))))) = iProver_top
    | v1_relat_1(k2_funct_1(sK6)) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_1633])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_350,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_351,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_353,plain,
    ( ~ v1_relat_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_35])).

cnf(c_1629,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_1926,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_35,c_33,c_351,c_1922])).

cnf(c_3284,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK6)) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3283,c_1926])).

cnf(c_36,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1923,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1976,plain,
    ( ~ v1_relat_1(sK6)
    | v1_funct_1(k2_funct_1(sK6))
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1977,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1975,plain,
    ( v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1979,plain,
    ( v1_relat_1(k2_funct_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_3918,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3284,c_36,c_38,c_1923,c_1977,c_1979])).

cnf(c_3926,plain,
    ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
    inference(superposition,[status(thm)],[c_3918,c_1635])).

cnf(c_3932,plain,
    ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_3926,c_2817])).

cnf(c_4013,plain,
    ( k1_relset_1(sK5,sK4,k2_funct_1(sK6)) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3287,c_3932])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k2_funct_1(sK6) != X0
    | k1_relat_1(X0) != sK5
    | k2_relat_1(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
    inference(unflattening,[status(thm)],[c_1010])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1011,c_18])).

cnf(c_1620,plain,
    ( k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_1965,plain,
    ( k1_relat_1(sK6) != sK4
    | k2_relat_1(sK6) != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1620,c_1926,c_1930])).

cnf(c_2816,plain,
    ( k1_relat_1(sK6) != sK4
    | sK5 != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2759,c_1965])).

cnf(c_2820,plain,
    ( k1_relat_1(sK6) != sK4
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2816])).

cnf(c_3512,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | k1_relat_1(sK6) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2820,c_36,c_38,c_1923,c_1965,c_1977,c_2759])).

cnf(c_3513,plain,
    ( k1_relat_1(sK6) != sK4
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3512])).

cnf(c_3518,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_3513])).

cnf(c_3923,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_3918])).

cnf(c_4061,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4013,c_3518,c_3923])).

cnf(c_4066,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4061,c_3918])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4146,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4066,c_5])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK6) != X0
    | sK4 != X1
    | sK5 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_928,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_1624,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_1820,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1624,c_5])).

cnf(c_2214,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | sK5 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_36,c_38,c_1923,c_1977])).

cnf(c_2215,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
    | sK5 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2214])).

cnf(c_4077,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4061,c_2215])).

cnf(c_4113,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4077])).

cnf(c_4117,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4113,c_5])).

cnf(c_4150,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4146,c_4117])).

cnf(c_4082,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4061,c_1632])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4087,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4082,c_4])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_884,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X1
    | sK5 != k1_xboole_0
    | sK6 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_885,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_1626,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK6
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_1741,plain,
    ( sK4 = k1_xboole_0
    | sK5 != k1_xboole_0
    | sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1626,c_4])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_101,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2191,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2192,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2191])).

cnf(c_2194,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2243,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK6)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2244,plain,
    ( sK6 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2243])).

cnf(c_2246,plain,
    ( sK6 = k1_xboole_0
    | v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_2336,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_101,c_2194,c_2246])).

cnf(c_4245,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4087,c_2336])).

cnf(c_6458,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4150,c_4245])).

cnf(c_4850,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4245,c_4146])).

cnf(c_3061,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1635])).

cnf(c_6131,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4850,c_3061])).

cnf(c_4074,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4061,c_2817])).

cnf(c_4847,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4245,c_4074])).

cnf(c_6143,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6131,c_4847])).

cnf(c_6459,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6458,c_6143])).

cnf(c_6460,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6459])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:17:47 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.94/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/0.99  
% 2.94/0.99  ------  iProver source info
% 2.94/0.99  
% 2.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/0.99  git: non_committed_changes: false
% 2.94/0.99  git: last_make_outside_of_git: false
% 2.94/0.99  
% 2.94/0.99  ------ 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options
% 2.94/0.99  
% 2.94/0.99  --out_options                           all
% 2.94/0.99  --tptp_safe_out                         true
% 2.94/0.99  --problem_path                          ""
% 2.94/0.99  --include_path                          ""
% 2.94/0.99  --clausifier                            res/vclausify_rel
% 2.94/0.99  --clausifier_options                    --mode clausify
% 2.94/0.99  --stdin                                 false
% 2.94/0.99  --stats_out                             all
% 2.94/0.99  
% 2.94/0.99  ------ General Options
% 2.94/0.99  
% 2.94/0.99  --fof                                   false
% 2.94/0.99  --time_out_real                         305.
% 2.94/0.99  --time_out_virtual                      -1.
% 2.94/0.99  --symbol_type_check                     false
% 2.94/0.99  --clausify_out                          false
% 2.94/0.99  --sig_cnt_out                           false
% 2.94/0.99  --trig_cnt_out                          false
% 2.94/0.99  --trig_cnt_out_tolerance                1.
% 2.94/0.99  --trig_cnt_out_sk_spl                   false
% 2.94/0.99  --abstr_cl_out                          false
% 2.94/0.99  
% 2.94/0.99  ------ Global Options
% 2.94/0.99  
% 2.94/0.99  --schedule                              default
% 2.94/0.99  --add_important_lit                     false
% 2.94/0.99  --prop_solver_per_cl                    1000
% 2.94/0.99  --min_unsat_core                        false
% 2.94/0.99  --soft_assumptions                      false
% 2.94/0.99  --soft_lemma_size                       3
% 2.94/0.99  --prop_impl_unit_size                   0
% 2.94/0.99  --prop_impl_unit                        []
% 2.94/0.99  --share_sel_clauses                     true
% 2.94/0.99  --reset_solvers                         false
% 2.94/0.99  --bc_imp_inh                            [conj_cone]
% 2.94/0.99  --conj_cone_tolerance                   3.
% 2.94/0.99  --extra_neg_conj                        none
% 2.94/0.99  --large_theory_mode                     true
% 2.94/0.99  --prolific_symb_bound                   200
% 2.94/0.99  --lt_threshold                          2000
% 2.94/0.99  --clause_weak_htbl                      true
% 2.94/0.99  --gc_record_bc_elim                     false
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing Options
% 2.94/0.99  
% 2.94/0.99  --preprocessing_flag                    true
% 2.94/0.99  --time_out_prep_mult                    0.1
% 2.94/0.99  --splitting_mode                        input
% 2.94/0.99  --splitting_grd                         true
% 2.94/0.99  --splitting_cvd                         false
% 2.94/0.99  --splitting_cvd_svl                     false
% 2.94/0.99  --splitting_nvd                         32
% 2.94/0.99  --sub_typing                            true
% 2.94/0.99  --prep_gs_sim                           true
% 2.94/0.99  --prep_unflatten                        true
% 2.94/0.99  --prep_res_sim                          true
% 2.94/0.99  --prep_upred                            true
% 2.94/0.99  --prep_sem_filter                       exhaustive
% 2.94/0.99  --prep_sem_filter_out                   false
% 2.94/0.99  --pred_elim                             true
% 2.94/0.99  --res_sim_input                         true
% 2.94/0.99  --eq_ax_congr_red                       true
% 2.94/0.99  --pure_diseq_elim                       true
% 2.94/0.99  --brand_transform                       false
% 2.94/0.99  --non_eq_to_eq                          false
% 2.94/0.99  --prep_def_merge                        true
% 2.94/0.99  --prep_def_merge_prop_impl              false
% 2.94/0.99  --prep_def_merge_mbd                    true
% 2.94/0.99  --prep_def_merge_tr_red                 false
% 2.94/0.99  --prep_def_merge_tr_cl                  false
% 2.94/0.99  --smt_preprocessing                     true
% 2.94/0.99  --smt_ac_axioms                         fast
% 2.94/0.99  --preprocessed_out                      false
% 2.94/0.99  --preprocessed_stats                    false
% 2.94/0.99  
% 2.94/0.99  ------ Abstraction refinement Options
% 2.94/0.99  
% 2.94/0.99  --abstr_ref                             []
% 2.94/0.99  --abstr_ref_prep                        false
% 2.94/0.99  --abstr_ref_until_sat                   false
% 2.94/0.99  --abstr_ref_sig_restrict                funpre
% 2.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.99  --abstr_ref_under                       []
% 2.94/0.99  
% 2.94/0.99  ------ SAT Options
% 2.94/0.99  
% 2.94/0.99  --sat_mode                              false
% 2.94/0.99  --sat_fm_restart_options                ""
% 2.94/0.99  --sat_gr_def                            false
% 2.94/0.99  --sat_epr_types                         true
% 2.94/0.99  --sat_non_cyclic_types                  false
% 2.94/0.99  --sat_finite_models                     false
% 2.94/0.99  --sat_fm_lemmas                         false
% 2.94/0.99  --sat_fm_prep                           false
% 2.94/0.99  --sat_fm_uc_incr                        true
% 2.94/0.99  --sat_out_model                         small
% 2.94/0.99  --sat_out_clauses                       false
% 2.94/0.99  
% 2.94/0.99  ------ QBF Options
% 2.94/0.99  
% 2.94/0.99  --qbf_mode                              false
% 2.94/0.99  --qbf_elim_univ                         false
% 2.94/0.99  --qbf_dom_inst                          none
% 2.94/0.99  --qbf_dom_pre_inst                      false
% 2.94/0.99  --qbf_sk_in                             false
% 2.94/0.99  --qbf_pred_elim                         true
% 2.94/0.99  --qbf_split                             512
% 2.94/0.99  
% 2.94/0.99  ------ BMC1 Options
% 2.94/0.99  
% 2.94/0.99  --bmc1_incremental                      false
% 2.94/0.99  --bmc1_axioms                           reachable_all
% 2.94/0.99  --bmc1_min_bound                        0
% 2.94/0.99  --bmc1_max_bound                        -1
% 2.94/0.99  --bmc1_max_bound_default                -1
% 2.94/0.99  --bmc1_symbol_reachability              true
% 2.94/0.99  --bmc1_property_lemmas                  false
% 2.94/0.99  --bmc1_k_induction                      false
% 2.94/0.99  --bmc1_non_equiv_states                 false
% 2.94/0.99  --bmc1_deadlock                         false
% 2.94/0.99  --bmc1_ucm                              false
% 2.94/0.99  --bmc1_add_unsat_core                   none
% 2.94/0.99  --bmc1_unsat_core_children              false
% 2.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.99  --bmc1_out_stat                         full
% 2.94/0.99  --bmc1_ground_init                      false
% 2.94/0.99  --bmc1_pre_inst_next_state              false
% 2.94/0.99  --bmc1_pre_inst_state                   false
% 2.94/0.99  --bmc1_pre_inst_reach_state             false
% 2.94/0.99  --bmc1_out_unsat_core                   false
% 2.94/0.99  --bmc1_aig_witness_out                  false
% 2.94/0.99  --bmc1_verbose                          false
% 2.94/0.99  --bmc1_dump_clauses_tptp                false
% 2.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.99  --bmc1_dump_file                        -
% 2.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.99  --bmc1_ucm_extend_mode                  1
% 2.94/0.99  --bmc1_ucm_init_mode                    2
% 2.94/0.99  --bmc1_ucm_cone_mode                    none
% 2.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.99  --bmc1_ucm_relax_model                  4
% 2.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.99  --bmc1_ucm_layered_model                none
% 2.94/0.99  --bmc1_ucm_max_lemma_size               10
% 2.94/0.99  
% 2.94/0.99  ------ AIG Options
% 2.94/0.99  
% 2.94/0.99  --aig_mode                              false
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation Options
% 2.94/0.99  
% 2.94/0.99  --instantiation_flag                    true
% 2.94/0.99  --inst_sos_flag                         false
% 2.94/0.99  --inst_sos_phase                        true
% 2.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel_side                     num_symb
% 2.94/0.99  --inst_solver_per_active                1400
% 2.94/0.99  --inst_solver_calls_frac                1.
% 2.94/0.99  --inst_passive_queue_type               priority_queues
% 2.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.99  --inst_passive_queues_freq              [25;2]
% 2.94/0.99  --inst_dismatching                      true
% 2.94/0.99  --inst_eager_unprocessed_to_passive     true
% 2.94/0.99  --inst_prop_sim_given                   true
% 2.94/0.99  --inst_prop_sim_new                     false
% 2.94/0.99  --inst_subs_new                         false
% 2.94/0.99  --inst_eq_res_simp                      false
% 2.94/0.99  --inst_subs_given                       false
% 2.94/0.99  --inst_orphan_elimination               true
% 2.94/0.99  --inst_learning_loop_flag               true
% 2.94/0.99  --inst_learning_start                   3000
% 2.94/0.99  --inst_learning_factor                  2
% 2.94/0.99  --inst_start_prop_sim_after_learn       3
% 2.94/0.99  --inst_sel_renew                        solver
% 2.94/0.99  --inst_lit_activity_flag                true
% 2.94/0.99  --inst_restr_to_given                   false
% 2.94/0.99  --inst_activity_threshold               500
% 2.94/0.99  --inst_out_proof                        true
% 2.94/0.99  
% 2.94/0.99  ------ Resolution Options
% 2.94/0.99  
% 2.94/0.99  --resolution_flag                       true
% 2.94/0.99  --res_lit_sel                           adaptive
% 2.94/0.99  --res_lit_sel_side                      none
% 2.94/0.99  --res_ordering                          kbo
% 2.94/0.99  --res_to_prop_solver                    active
% 2.94/0.99  --res_prop_simpl_new                    false
% 2.94/0.99  --res_prop_simpl_given                  true
% 2.94/0.99  --res_passive_queue_type                priority_queues
% 2.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.99  --res_passive_queues_freq               [15;5]
% 2.94/0.99  --res_forward_subs                      full
% 2.94/0.99  --res_backward_subs                     full
% 2.94/0.99  --res_forward_subs_resolution           true
% 2.94/0.99  --res_backward_subs_resolution          true
% 2.94/0.99  --res_orphan_elimination                true
% 2.94/0.99  --res_time_limit                        2.
% 2.94/0.99  --res_out_proof                         true
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Options
% 2.94/0.99  
% 2.94/0.99  --superposition_flag                    true
% 2.94/0.99  --sup_passive_queue_type                priority_queues
% 2.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.99  --demod_completeness_check              fast
% 2.94/0.99  --demod_use_ground                      true
% 2.94/0.99  --sup_to_prop_solver                    passive
% 2.94/0.99  --sup_prop_simpl_new                    true
% 2.94/0.99  --sup_prop_simpl_given                  true
% 2.94/0.99  --sup_fun_splitting                     false
% 2.94/0.99  --sup_smt_interval                      50000
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Simplification Setup
% 2.94/0.99  
% 2.94/0.99  --sup_indices_passive                   []
% 2.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_full_bw                           [BwDemod]
% 2.94/0.99  --sup_immed_triv                        [TrivRules]
% 2.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_immed_bw_main                     []
% 2.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  
% 2.94/0.99  ------ Combination Options
% 2.94/0.99  
% 2.94/0.99  --comb_res_mult                         3
% 2.94/0.99  --comb_sup_mult                         2
% 2.94/0.99  --comb_inst_mult                        10
% 2.94/0.99  
% 2.94/0.99  ------ Debug Options
% 2.94/0.99  
% 2.94/0.99  --dbg_backtrace                         false
% 2.94/0.99  --dbg_dump_prop_clauses                 false
% 2.94/0.99  --dbg_dump_prop_clauses_file            -
% 2.94/0.99  --dbg_out_stat                          false
% 2.94/0.99  ------ Parsing...
% 2.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/0.99  ------ Proving...
% 2.94/0.99  ------ Problem Properties 
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  clauses                                 36
% 2.94/0.99  conjectures                             3
% 2.94/0.99  EPR                                     4
% 2.94/0.99  Horn                                    29
% 2.94/0.99  unary                                   8
% 2.94/0.99  binary                                  10
% 2.94/0.99  lits                                    95
% 2.94/0.99  lits eq                                 40
% 2.94/0.99  fd_pure                                 0
% 2.94/0.99  fd_pseudo                               0
% 2.94/0.99  fd_cond                                 2
% 2.94/0.99  fd_pseudo_cond                          3
% 2.94/0.99  AC symbols                              0
% 2.94/0.99  
% 2.94/0.99  ------ Schedule dynamic 5 is on 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  ------ 
% 2.94/0.99  Current options:
% 2.94/0.99  ------ 
% 2.94/0.99  
% 2.94/0.99  ------ Input Options
% 2.94/0.99  
% 2.94/0.99  --out_options                           all
% 2.94/0.99  --tptp_safe_out                         true
% 2.94/0.99  --problem_path                          ""
% 2.94/0.99  --include_path                          ""
% 2.94/0.99  --clausifier                            res/vclausify_rel
% 2.94/0.99  --clausifier_options                    --mode clausify
% 2.94/0.99  --stdin                                 false
% 2.94/0.99  --stats_out                             all
% 2.94/0.99  
% 2.94/0.99  ------ General Options
% 2.94/0.99  
% 2.94/0.99  --fof                                   false
% 2.94/0.99  --time_out_real                         305.
% 2.94/0.99  --time_out_virtual                      -1.
% 2.94/0.99  --symbol_type_check                     false
% 2.94/0.99  --clausify_out                          false
% 2.94/0.99  --sig_cnt_out                           false
% 2.94/0.99  --trig_cnt_out                          false
% 2.94/0.99  --trig_cnt_out_tolerance                1.
% 2.94/0.99  --trig_cnt_out_sk_spl                   false
% 2.94/0.99  --abstr_cl_out                          false
% 2.94/0.99  
% 2.94/0.99  ------ Global Options
% 2.94/0.99  
% 2.94/0.99  --schedule                              default
% 2.94/0.99  --add_important_lit                     false
% 2.94/0.99  --prop_solver_per_cl                    1000
% 2.94/0.99  --min_unsat_core                        false
% 2.94/0.99  --soft_assumptions                      false
% 2.94/0.99  --soft_lemma_size                       3
% 2.94/0.99  --prop_impl_unit_size                   0
% 2.94/0.99  --prop_impl_unit                        []
% 2.94/0.99  --share_sel_clauses                     true
% 2.94/0.99  --reset_solvers                         false
% 2.94/0.99  --bc_imp_inh                            [conj_cone]
% 2.94/0.99  --conj_cone_tolerance                   3.
% 2.94/0.99  --extra_neg_conj                        none
% 2.94/0.99  --large_theory_mode                     true
% 2.94/0.99  --prolific_symb_bound                   200
% 2.94/0.99  --lt_threshold                          2000
% 2.94/0.99  --clause_weak_htbl                      true
% 2.94/0.99  --gc_record_bc_elim                     false
% 2.94/0.99  
% 2.94/0.99  ------ Preprocessing Options
% 2.94/0.99  
% 2.94/0.99  --preprocessing_flag                    true
% 2.94/0.99  --time_out_prep_mult                    0.1
% 2.94/0.99  --splitting_mode                        input
% 2.94/0.99  --splitting_grd                         true
% 2.94/0.99  --splitting_cvd                         false
% 2.94/0.99  --splitting_cvd_svl                     false
% 2.94/0.99  --splitting_nvd                         32
% 2.94/0.99  --sub_typing                            true
% 2.94/0.99  --prep_gs_sim                           true
% 2.94/0.99  --prep_unflatten                        true
% 2.94/0.99  --prep_res_sim                          true
% 2.94/0.99  --prep_upred                            true
% 2.94/0.99  --prep_sem_filter                       exhaustive
% 2.94/0.99  --prep_sem_filter_out                   false
% 2.94/0.99  --pred_elim                             true
% 2.94/0.99  --res_sim_input                         true
% 2.94/0.99  --eq_ax_congr_red                       true
% 2.94/0.99  --pure_diseq_elim                       true
% 2.94/0.99  --brand_transform                       false
% 2.94/0.99  --non_eq_to_eq                          false
% 2.94/0.99  --prep_def_merge                        true
% 2.94/0.99  --prep_def_merge_prop_impl              false
% 2.94/0.99  --prep_def_merge_mbd                    true
% 2.94/0.99  --prep_def_merge_tr_red                 false
% 2.94/0.99  --prep_def_merge_tr_cl                  false
% 2.94/0.99  --smt_preprocessing                     true
% 2.94/0.99  --smt_ac_axioms                         fast
% 2.94/0.99  --preprocessed_out                      false
% 2.94/0.99  --preprocessed_stats                    false
% 2.94/0.99  
% 2.94/0.99  ------ Abstraction refinement Options
% 2.94/0.99  
% 2.94/0.99  --abstr_ref                             []
% 2.94/0.99  --abstr_ref_prep                        false
% 2.94/0.99  --abstr_ref_until_sat                   false
% 2.94/0.99  --abstr_ref_sig_restrict                funpre
% 2.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/0.99  --abstr_ref_under                       []
% 2.94/0.99  
% 2.94/0.99  ------ SAT Options
% 2.94/0.99  
% 2.94/0.99  --sat_mode                              false
% 2.94/0.99  --sat_fm_restart_options                ""
% 2.94/0.99  --sat_gr_def                            false
% 2.94/0.99  --sat_epr_types                         true
% 2.94/0.99  --sat_non_cyclic_types                  false
% 2.94/0.99  --sat_finite_models                     false
% 2.94/0.99  --sat_fm_lemmas                         false
% 2.94/0.99  --sat_fm_prep                           false
% 2.94/0.99  --sat_fm_uc_incr                        true
% 2.94/0.99  --sat_out_model                         small
% 2.94/0.99  --sat_out_clauses                       false
% 2.94/0.99  
% 2.94/0.99  ------ QBF Options
% 2.94/0.99  
% 2.94/0.99  --qbf_mode                              false
% 2.94/0.99  --qbf_elim_univ                         false
% 2.94/0.99  --qbf_dom_inst                          none
% 2.94/0.99  --qbf_dom_pre_inst                      false
% 2.94/0.99  --qbf_sk_in                             false
% 2.94/0.99  --qbf_pred_elim                         true
% 2.94/0.99  --qbf_split                             512
% 2.94/0.99  
% 2.94/0.99  ------ BMC1 Options
% 2.94/0.99  
% 2.94/0.99  --bmc1_incremental                      false
% 2.94/0.99  --bmc1_axioms                           reachable_all
% 2.94/0.99  --bmc1_min_bound                        0
% 2.94/0.99  --bmc1_max_bound                        -1
% 2.94/0.99  --bmc1_max_bound_default                -1
% 2.94/0.99  --bmc1_symbol_reachability              true
% 2.94/0.99  --bmc1_property_lemmas                  false
% 2.94/0.99  --bmc1_k_induction                      false
% 2.94/0.99  --bmc1_non_equiv_states                 false
% 2.94/0.99  --bmc1_deadlock                         false
% 2.94/0.99  --bmc1_ucm                              false
% 2.94/0.99  --bmc1_add_unsat_core                   none
% 2.94/0.99  --bmc1_unsat_core_children              false
% 2.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/0.99  --bmc1_out_stat                         full
% 2.94/0.99  --bmc1_ground_init                      false
% 2.94/0.99  --bmc1_pre_inst_next_state              false
% 2.94/0.99  --bmc1_pre_inst_state                   false
% 2.94/0.99  --bmc1_pre_inst_reach_state             false
% 2.94/0.99  --bmc1_out_unsat_core                   false
% 2.94/0.99  --bmc1_aig_witness_out                  false
% 2.94/0.99  --bmc1_verbose                          false
% 2.94/0.99  --bmc1_dump_clauses_tptp                false
% 2.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.94/0.99  --bmc1_dump_file                        -
% 2.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.94/0.99  --bmc1_ucm_extend_mode                  1
% 2.94/0.99  --bmc1_ucm_init_mode                    2
% 2.94/0.99  --bmc1_ucm_cone_mode                    none
% 2.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.94/0.99  --bmc1_ucm_relax_model                  4
% 2.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/0.99  --bmc1_ucm_layered_model                none
% 2.94/0.99  --bmc1_ucm_max_lemma_size               10
% 2.94/0.99  
% 2.94/0.99  ------ AIG Options
% 2.94/0.99  
% 2.94/0.99  --aig_mode                              false
% 2.94/0.99  
% 2.94/0.99  ------ Instantiation Options
% 2.94/0.99  
% 2.94/0.99  --instantiation_flag                    true
% 2.94/0.99  --inst_sos_flag                         false
% 2.94/0.99  --inst_sos_phase                        true
% 2.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/0.99  --inst_lit_sel_side                     none
% 2.94/0.99  --inst_solver_per_active                1400
% 2.94/0.99  --inst_solver_calls_frac                1.
% 2.94/0.99  --inst_passive_queue_type               priority_queues
% 2.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/0.99  --inst_passive_queues_freq              [25;2]
% 2.94/0.99  --inst_dismatching                      true
% 2.94/0.99  --inst_eager_unprocessed_to_passive     true
% 2.94/0.99  --inst_prop_sim_given                   true
% 2.94/0.99  --inst_prop_sim_new                     false
% 2.94/0.99  --inst_subs_new                         false
% 2.94/0.99  --inst_eq_res_simp                      false
% 2.94/0.99  --inst_subs_given                       false
% 2.94/0.99  --inst_orphan_elimination               true
% 2.94/0.99  --inst_learning_loop_flag               true
% 2.94/0.99  --inst_learning_start                   3000
% 2.94/0.99  --inst_learning_factor                  2
% 2.94/0.99  --inst_start_prop_sim_after_learn       3
% 2.94/0.99  --inst_sel_renew                        solver
% 2.94/0.99  --inst_lit_activity_flag                true
% 2.94/0.99  --inst_restr_to_given                   false
% 2.94/0.99  --inst_activity_threshold               500
% 2.94/0.99  --inst_out_proof                        true
% 2.94/0.99  
% 2.94/0.99  ------ Resolution Options
% 2.94/0.99  
% 2.94/0.99  --resolution_flag                       false
% 2.94/0.99  --res_lit_sel                           adaptive
% 2.94/0.99  --res_lit_sel_side                      none
% 2.94/0.99  --res_ordering                          kbo
% 2.94/0.99  --res_to_prop_solver                    active
% 2.94/0.99  --res_prop_simpl_new                    false
% 2.94/0.99  --res_prop_simpl_given                  true
% 2.94/0.99  --res_passive_queue_type                priority_queues
% 2.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/0.99  --res_passive_queues_freq               [15;5]
% 2.94/0.99  --res_forward_subs                      full
% 2.94/0.99  --res_backward_subs                     full
% 2.94/0.99  --res_forward_subs_resolution           true
% 2.94/0.99  --res_backward_subs_resolution          true
% 2.94/0.99  --res_orphan_elimination                true
% 2.94/0.99  --res_time_limit                        2.
% 2.94/0.99  --res_out_proof                         true
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Options
% 2.94/0.99  
% 2.94/0.99  --superposition_flag                    true
% 2.94/0.99  --sup_passive_queue_type                priority_queues
% 2.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.94/0.99  --demod_completeness_check              fast
% 2.94/0.99  --demod_use_ground                      true
% 2.94/0.99  --sup_to_prop_solver                    passive
% 2.94/0.99  --sup_prop_simpl_new                    true
% 2.94/0.99  --sup_prop_simpl_given                  true
% 2.94/0.99  --sup_fun_splitting                     false
% 2.94/0.99  --sup_smt_interval                      50000
% 2.94/0.99  
% 2.94/0.99  ------ Superposition Simplification Setup
% 2.94/0.99  
% 2.94/0.99  --sup_indices_passive                   []
% 2.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_full_bw                           [BwDemod]
% 2.94/0.99  --sup_immed_triv                        [TrivRules]
% 2.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_immed_bw_main                     []
% 2.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/0.99  
% 2.94/0.99  ------ Combination Options
% 2.94/0.99  
% 2.94/0.99  --comb_res_mult                         3
% 2.94/0.99  --comb_sup_mult                         2
% 2.94/0.99  --comb_inst_mult                        10
% 2.94/0.99  
% 2.94/0.99  ------ Debug Options
% 2.94/0.99  
% 2.94/0.99  --dbg_backtrace                         false
% 2.94/0.99  --dbg_dump_prop_clauses                 false
% 2.94/0.99  --dbg_dump_prop_clauses_file            -
% 2.94/0.99  --dbg_out_stat                          false
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  ------ Proving...
% 2.94/0.99  
% 2.94/0.99  
% 2.94/0.99  % SZS status Theorem for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99   Resolution empty clause
% 2.94/0.99  
% 2.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/0.99  
% 2.94/0.99  fof(f13,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f26,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f13])).
% 2.94/0.99  
% 2.94/0.99  fof(f27,plain,(
% 2.94/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(flattening,[],[f26])).
% 2.94/0.99  
% 2.94/0.99  fof(f44,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(nnf_transformation,[],[f27])).
% 2.94/0.99  
% 2.94/0.99  fof(f68,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f44])).
% 2.94/0.99  
% 2.94/0.99  fof(f15,conjecture,(
% 2.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f16,negated_conjecture,(
% 2.94/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.94/0.99    inference(negated_conjecture,[],[f15])).
% 2.94/0.99  
% 2.94/0.99  fof(f30,plain,(
% 2.94/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.94/0.99    inference(ennf_transformation,[],[f16])).
% 2.94/0.99  
% 2.94/0.99  fof(f31,plain,(
% 2.94/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.94/0.99    inference(flattening,[],[f30])).
% 2.94/0.99  
% 2.94/0.99  fof(f45,plain,(
% 2.94/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & k2_relset_1(sK4,sK5,sK6) = sK5 & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 2.94/0.99    introduced(choice_axiom,[])).
% 2.94/0.99  
% 2.94/0.99  fof(f46,plain,(
% 2.94/0.99    (~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & k2_relset_1(sK4,sK5,sK6) = sK5 & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 2.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f45])).
% 2.94/0.99  
% 2.94/0.99  fof(f78,plain,(
% 2.94/0.99    v1_funct_2(sK6,sK4,sK5)),
% 2.94/0.99    inference(cnf_transformation,[],[f46])).
% 2.94/0.99  
% 2.94/0.99  fof(f79,plain,(
% 2.94/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.94/0.99    inference(cnf_transformation,[],[f46])).
% 2.94/0.99  
% 2.94/0.99  fof(f11,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f24,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f11])).
% 2.94/0.99  
% 2.94/0.99  fof(f66,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f24])).
% 2.94/0.99  
% 2.94/0.99  fof(f12,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f25,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f12])).
% 2.94/0.99  
% 2.94/0.99  fof(f67,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f25])).
% 2.94/0.99  
% 2.94/0.99  fof(f81,plain,(
% 2.94/0.99    k2_relset_1(sK4,sK5,sK6) = sK5),
% 2.94/0.99    inference(cnf_transformation,[],[f46])).
% 2.94/0.99  
% 2.94/0.99  fof(f9,axiom,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f21,plain,(
% 2.94/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f9])).
% 2.94/0.99  
% 2.94/0.99  fof(f22,plain,(
% 2.94/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(flattening,[],[f21])).
% 2.94/0.99  
% 2.94/0.99  fof(f63,plain,(
% 2.94/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f22])).
% 2.94/0.99  
% 2.94/0.99  fof(f80,plain,(
% 2.94/0.99    v2_funct_1(sK6)),
% 2.94/0.99    inference(cnf_transformation,[],[f46])).
% 2.94/0.99  
% 2.94/0.99  fof(f77,plain,(
% 2.94/0.99    v1_funct_1(sK6)),
% 2.94/0.99    inference(cnf_transformation,[],[f46])).
% 2.94/0.99  
% 2.94/0.99  fof(f10,axiom,(
% 2.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f23,plain,(
% 2.94/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.94/0.99    inference(ennf_transformation,[],[f10])).
% 2.94/0.99  
% 2.94/0.99  fof(f65,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f23])).
% 2.94/0.99  
% 2.94/0.99  fof(f14,axiom,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f28,plain,(
% 2.94/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f14])).
% 2.94/0.99  
% 2.94/0.99  fof(f29,plain,(
% 2.94/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(flattening,[],[f28])).
% 2.94/0.99  
% 2.94/0.99  fof(f76,plain,(
% 2.94/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f29])).
% 2.94/0.99  
% 2.94/0.99  fof(f64,plain,(
% 2.94/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f22])).
% 2.94/0.99  
% 2.94/0.99  fof(f8,axiom,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f19,plain,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.94/0.99    inference(ennf_transformation,[],[f8])).
% 2.94/0.99  
% 2.94/0.99  fof(f20,plain,(
% 2.94/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.94/0.99    inference(flattening,[],[f19])).
% 2.94/0.99  
% 2.94/0.99  fof(f62,plain,(
% 2.94/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f20])).
% 2.94/0.99  
% 2.94/0.99  fof(f61,plain,(
% 2.94/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f20])).
% 2.94/0.99  
% 2.94/0.99  fof(f75,plain,(
% 2.94/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f29])).
% 2.94/0.99  
% 2.94/0.99  fof(f82,plain,(
% 2.94/0.99    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))),
% 2.94/0.99    inference(cnf_transformation,[],[f46])).
% 2.94/0.99  
% 2.94/0.99  fof(f4,axiom,(
% 2.94/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f36,plain,(
% 2.94/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/0.99    inference(nnf_transformation,[],[f4])).
% 2.94/0.99  
% 2.94/0.99  fof(f37,plain,(
% 2.94/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.94/0.99    inference(flattening,[],[f36])).
% 2.94/0.99  
% 2.94/0.99  fof(f52,plain,(
% 2.94/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.94/0.99    inference(cnf_transformation,[],[f37])).
% 2.94/0.99  
% 2.94/0.99  fof(f84,plain,(
% 2.94/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.94/0.99    inference(equality_resolution,[],[f52])).
% 2.94/0.99  
% 2.94/0.99  fof(f71,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f44])).
% 2.94/0.99  
% 2.94/0.99  fof(f90,plain,(
% 2.94/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.94/0.99    inference(equality_resolution,[],[f71])).
% 2.94/0.99  
% 2.94/0.99  fof(f53,plain,(
% 2.94/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.94/0.99    inference(cnf_transformation,[],[f37])).
% 2.94/0.99  
% 2.94/0.99  fof(f83,plain,(
% 2.94/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.94/0.99    inference(equality_resolution,[],[f53])).
% 2.94/0.99  
% 2.94/0.99  fof(f72,plain,(
% 2.94/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.94/0.99    inference(cnf_transformation,[],[f44])).
% 2.94/0.99  
% 2.94/0.99  fof(f89,plain,(
% 2.94/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.94/0.99    inference(equality_resolution,[],[f72])).
% 2.94/0.99  
% 2.94/0.99  fof(f2,axiom,(
% 2.94/0.99    v1_xboole_0(k1_xboole_0)),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f49,plain,(
% 2.94/0.99    v1_xboole_0(k1_xboole_0)),
% 2.94/0.99    inference(cnf_transformation,[],[f2])).
% 2.94/0.99  
% 2.94/0.99  fof(f5,axiom,(
% 2.94/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f18,plain,(
% 2.94/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.94/0.99    inference(ennf_transformation,[],[f5])).
% 2.94/0.99  
% 2.94/0.99  fof(f54,plain,(
% 2.94/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f18])).
% 2.94/0.99  
% 2.94/0.99  fof(f3,axiom,(
% 2.94/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/0.99  
% 2.94/0.99  fof(f17,plain,(
% 2.94/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.94/0.99    inference(ennf_transformation,[],[f3])).
% 2.94/0.99  
% 2.94/0.99  fof(f50,plain,(
% 2.94/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.94/0.99    inference(cnf_transformation,[],[f17])).
% 2.94/0.99  
% 2.94/0.99  cnf(c_26,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_34,negated_conjecture,
% 2.94/0.99      ( v1_funct_2(sK6,sK4,sK5) ),
% 2.94/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_999,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.94/0.99      | sK4 != X1
% 2.94/0.99      | sK5 != X2
% 2.94/0.99      | sK6 != X0
% 2.94/0.99      | k1_xboole_0 = X2 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1000,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.94/0.99      | k1_relset_1(sK4,sK5,sK6) = sK4
% 2.94/0.99      | k1_xboole_0 = sK5 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_999]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_33,negated_conjecture,
% 2.94/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.94/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1002,plain,
% 2.94/0.99      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1000,c_33]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1632,plain,
% 2.94/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_19,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1635,plain,
% 2.94/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3059,plain,
% 2.94/0.99      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1632,c_1635]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3287,plain,
% 2.94/0.99      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1002,c_3059]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_20,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.94/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1634,plain,
% 2.94/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2747,plain,
% 2.94/0.99      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_1632,c_1634]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_31,negated_conjecture,
% 2.94/0.99      ( k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 2.94/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2759,plain,
% 2.94/0.99      ( k2_relat_1(sK6) = sK5 ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_2747,c_31]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_17,plain,
% 2.94/0.99      ( ~ v2_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_32,negated_conjecture,
% 2.94/0.99      ( v2_funct_1(sK6) ),
% 2.94/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_336,plain,
% 2.94/0.99      ( ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.94/0.99      | sK6 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_337,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK6)
% 2.94/0.99      | ~ v1_funct_1(sK6)
% 2.94/0.99      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_336]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_35,negated_conjecture,
% 2.94/0.99      ( v1_funct_1(sK6) ),
% 2.94/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_339,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK6) | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_337,c_35]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1630,plain,
% 2.94/0.99      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
% 2.94/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_18,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1922,plain,
% 2.94/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.94/0.99      | v1_relat_1(sK6) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1930,plain,
% 2.94/0.99      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1630,c_35,c_33,c_337,c_1922]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2817,plain,
% 2.94/0.99      ( k1_relat_1(k2_funct_1(sK6)) = sK5 ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_2759,c_1930]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_27,plain,
% 2.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1633,plain,
% 2.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.94/0.99      | v1_relat_1(X0) != iProver_top
% 2.94/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3283,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(k2_funct_1(sK6))))) = iProver_top
% 2.94/0.99      | v1_relat_1(k2_funct_1(sK6)) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_2817,c_1633]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_16,plain,
% 2.94/0.99      ( ~ v2_funct_1(X0)
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_350,plain,
% 2.94/0.99      ( ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.94/0.99      | sK6 != X0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_351,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK6)
% 2.94/0.99      | ~ v1_funct_1(sK6)
% 2.94/0.99      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_350]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_353,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK6) | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 2.94/0.99      inference(global_propositional_subsumption,[status(thm)],[c_351,c_35]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1629,plain,
% 2.94/0.99      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
% 2.94/0.99      | v1_relat_1(sK6) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1926,plain,
% 2.94/0.99      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1629,c_35,c_33,c_351,c_1922]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3284,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top
% 2.94/0.99      | v1_relat_1(k2_funct_1(sK6)) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3283,c_1926]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_36,plain,
% 2.94/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_38,plain,
% 2.94/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1923,plain,
% 2.94/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.94/0.99      | v1_relat_1(sK6) = iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_14,plain,
% 2.94/0.99      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1976,plain,
% 2.94/0.99      ( ~ v1_relat_1(sK6) | v1_funct_1(k2_funct_1(sK6)) | ~ v1_funct_1(sK6) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1977,plain,
% 2.94/0.99      ( v1_relat_1(sK6) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) = iProver_top
% 2.94/0.99      | v1_funct_1(sK6) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1976]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_15,plain,
% 2.94/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1975,plain,
% 2.94/0.99      ( v1_relat_1(k2_funct_1(sK6)) | ~ v1_relat_1(sK6) | ~ v1_funct_1(sK6) ),
% 2.94/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1979,plain,
% 2.94/0.99      ( v1_relat_1(k2_funct_1(sK6)) = iProver_top
% 2.94/0.99      | v1_relat_1(sK6) != iProver_top
% 2.94/0.99      | v1_funct_1(sK6) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3918,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_3284,c_36,c_38,c_1923,c_1977,c_1979]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3926,plain,
% 2.94/0.99      ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3918,c_1635]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3932,plain,
% 2.94/0.99      ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = sK5 ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_3926,c_2817]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4013,plain,
% 2.94/0.99      ( k1_relset_1(sK5,sK4,k2_funct_1(sK6)) = sK5 | sK5 = k1_xboole_0 ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3287,c_3932]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_28,plain,
% 2.94/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X0) ),
% 2.94/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_30,negated_conjecture,
% 2.94/0.99      ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
% 2.94/0.99      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 2.94/0.99      | ~ v1_funct_1(k2_funct_1(sK6)) ),
% 2.94/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1010,plain,
% 2.94/0.99      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 2.94/0.99      | ~ v1_relat_1(X0)
% 2.94/0.99      | ~ v1_funct_1(X0)
% 2.94/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 2.94/0.99      | k2_funct_1(sK6) != X0
% 2.94/0.99      | k1_relat_1(X0) != sK5
% 2.94/0.99      | k2_relat_1(X0) != sK4 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1011,plain,
% 2.94/0.99      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 2.94/0.99      | ~ v1_relat_1(k2_funct_1(sK6))
% 2.94/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 2.94/0.99      | k1_relat_1(k2_funct_1(sK6)) != sK5
% 2.94/0.99      | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_1010]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1023,plain,
% 2.94/0.99      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 2.94/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 2.94/0.99      | k1_relat_1(k2_funct_1(sK6)) != sK5
% 2.94/0.99      | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
% 2.94/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1011,c_18]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1620,plain,
% 2.94/0.99      ( k1_relat_1(k2_funct_1(sK6)) != sK5
% 2.94/0.99      | k2_relat_1(k2_funct_1(sK6)) != sK4
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1965,plain,
% 2.94/0.99      ( k1_relat_1(sK6) != sK4
% 2.94/0.99      | k2_relat_1(sK6) != sK5
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(light_normalisation,[status(thm)],[c_1620,c_1926,c_1930]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2816,plain,
% 2.94/0.99      ( k1_relat_1(sK6) != sK4
% 2.94/0.99      | sK5 != sK5
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_2759,c_1965]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2820,plain,
% 2.94/0.99      ( k1_relat_1(sK6) != sK4
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_2816]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3512,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | k1_relat_1(sK6) != sK4 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_2820,c_36,c_38,c_1923,c_1965,c_1977,c_2759]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3513,plain,
% 2.94/0.99      ( k1_relat_1(sK6) != sK4
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_3512]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3518,plain,
% 2.94/0.99      ( sK5 = k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3287,c_3513]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_3923,plain,
% 2.94/0.99      ( sK5 = k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 2.94/0.99      inference(superposition,[status(thm)],[c_3287,c_3918]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4061,plain,
% 2.94/0.99      ( sK5 = k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_4013,c_3518,c_3923]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4066,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK6)))) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4061,c_3918]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_5,plain,
% 2.94/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.94/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4146,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4066,c_5]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_23,plain,
% 2.94/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.94/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.94/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_927,plain,
% 2.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.94/0.99      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 2.94/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 2.94/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.94/0.99      | k2_funct_1(sK6) != X0
% 2.94/0.99      | sK4 != X1
% 2.94/0.99      | sK5 != k1_xboole_0 ),
% 2.94/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_928,plain,
% 2.94/0.99      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 2.94/0.99      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 2.94/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 2.94/0.99      | k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
% 2.94/0.99      | sK5 != k1_xboole_0 ),
% 2.94/0.99      inference(unflattening,[status(thm)],[c_927]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1624,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
% 2.94/0.99      | sK5 != k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_1820,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
% 2.94/0.99      | sK5 != k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.94/0.99      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_1624,c_5]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2214,plain,
% 2.94/0.99      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | sK5 != k1_xboole_0
% 2.94/0.99      | k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0 ),
% 2.94/0.99      inference(global_propositional_subsumption,
% 2.94/0.99                [status(thm)],
% 2.94/0.99                [c_1820,c_36,c_38,c_1923,c_1977]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_2215,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
% 2.94/0.99      | sK5 != k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.99      inference(renaming,[status(thm)],[c_2214]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4077,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
% 2.94/0.99      | k1_xboole_0 != k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4061,c_2215]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4113,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_4077]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4117,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0
% 2.94/0.99      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4113,c_5]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4150,plain,
% 2.94/0.99      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(sK6)) != k1_xboole_0 ),
% 2.94/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_4146,c_4117]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4082,plain,
% 2.94/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4061,c_1632]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4,plain,
% 2.94/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.94/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_4087,plain,
% 2.94/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/0.99      inference(demodulation,[status(thm)],[c_4082,c_4]) ).
% 2.94/0.99  
% 2.94/0.99  cnf(c_22,plain,
% 2.94/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.94/1.00      | k1_xboole_0 = X1
% 2.94/1.00      | k1_xboole_0 = X0 ),
% 2.94/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_884,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.94/1.00      | sK4 != X1
% 2.94/1.00      | sK5 != k1_xboole_0
% 2.94/1.00      | sK6 != X0
% 2.94/1.00      | k1_xboole_0 = X0
% 2.94/1.00      | k1_xboole_0 = X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_885,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
% 2.94/1.00      | sK5 != k1_xboole_0
% 2.94/1.00      | k1_xboole_0 = sK4
% 2.94/1.00      | k1_xboole_0 = sK6 ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_884]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1626,plain,
% 2.94/1.00      ( sK5 != k1_xboole_0
% 2.94/1.00      | k1_xboole_0 = sK4
% 2.94/1.00      | k1_xboole_0 = sK6
% 2.94/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_885]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1741,plain,
% 2.94/1.00      ( sK4 = k1_xboole_0
% 2.94/1.00      | sK5 != k1_xboole_0
% 2.94/1.00      | sK6 = k1_xboole_0
% 2.94/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_1626,c_4]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2,plain,
% 2.94/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_101,plain,
% 2.94/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.94/1.00      | ~ v1_xboole_0(X1)
% 2.94/1.00      | v1_xboole_0(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2191,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 2.94/1.00      | ~ v1_xboole_0(X0)
% 2.94/1.00      | v1_xboole_0(sK6) ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2192,plain,
% 2.94/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
% 2.94/1.00      | v1_xboole_0(X0) != iProver_top
% 2.94/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_2191]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2194,plain,
% 2.94/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.94/1.00      | v1_xboole_0(sK6) = iProver_top
% 2.94/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_2192]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3,plain,
% 2.94/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.94/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2243,plain,
% 2.94/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK6) | sK6 = X0 ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2244,plain,
% 2.94/1.00      ( sK6 = X0
% 2.94/1.00      | v1_xboole_0(X0) != iProver_top
% 2.94/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_2243]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2246,plain,
% 2.94/1.00      ( sK6 = k1_xboole_0
% 2.94/1.00      | v1_xboole_0(sK6) != iProver_top
% 2.94/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_2244]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_2336,plain,
% 2.94/1.00      ( sK6 = k1_xboole_0
% 2.94/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_1741,c_101,c_2194,c_2246]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4245,plain,
% 2.94/1.00      ( sK6 = k1_xboole_0 ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_4087,c_2336]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6458,plain,
% 2.94/1.00      ( k1_relset_1(k1_xboole_0,sK4,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_4150,c_4245]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4850,plain,
% 2.94/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_4245,c_4146]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3061,plain,
% 2.94/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.94/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_5,c_1635]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6131,plain,
% 2.94/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_4850,c_3061]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4074,plain,
% 2.94/1.00      ( k1_relat_1(k2_funct_1(sK6)) = k1_xboole_0 ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_4061,c_2817]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4847,plain,
% 2.94/1.00      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_4245,c_4074]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6143,plain,
% 2.94/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.94/1.00      inference(light_normalisation,[status(thm)],[c_6131,c_4847]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6459,plain,
% 2.94/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.94/1.00      inference(demodulation,[status(thm)],[c_6458,c_6143]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6460,plain,
% 2.94/1.00      ( $false ),
% 2.94/1.00      inference(equality_resolution_simp,[status(thm)],[c_6459]) ).
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  ------                               Statistics
% 2.94/1.00  
% 2.94/1.00  ------ General
% 2.94/1.00  
% 2.94/1.00  abstr_ref_over_cycles:                  0
% 2.94/1.00  abstr_ref_under_cycles:                 0
% 2.94/1.00  gc_basic_clause_elim:                   0
% 2.94/1.00  forced_gc_time:                         0
% 2.94/1.00  parsing_time:                           0.009
% 2.94/1.00  unif_index_cands_time:                  0.
% 2.94/1.00  unif_index_add_time:                    0.
% 2.94/1.00  orderings_time:                         0.
% 2.94/1.00  out_proof_time:                         0.008
% 2.94/1.00  total_time:                             0.177
% 2.94/1.00  num_of_symbols:                         54
% 2.94/1.00  num_of_terms:                           4307
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing
% 2.94/1.00  
% 2.94/1.00  num_of_splits:                          0
% 2.94/1.00  num_of_split_atoms:                     0
% 2.94/1.00  num_of_reused_defs:                     0
% 2.94/1.00  num_eq_ax_congr_red:                    16
% 2.94/1.00  num_of_sem_filtered_clauses:            1
% 2.94/1.00  num_of_subtypes:                        0
% 2.94/1.00  monotx_restored_types:                  0
% 2.94/1.00  sat_num_of_epr_types:                   0
% 2.94/1.00  sat_num_of_non_cyclic_types:            0
% 2.94/1.00  sat_guarded_non_collapsed_types:        0
% 2.94/1.00  num_pure_diseq_elim:                    0
% 2.94/1.00  simp_replaced_by:                       0
% 2.94/1.00  res_preprocessed:                       138
% 2.94/1.00  prep_upred:                             0
% 2.94/1.00  prep_unflattend:                        63
% 2.94/1.00  smt_new_axioms:                         0
% 2.94/1.00  pred_elim_cands:                        7
% 2.94/1.00  pred_elim:                              2
% 2.94/1.00  pred_elim_cl:                           -1
% 2.94/1.00  pred_elim_cycles:                       4
% 2.94/1.00  merged_defs:                            0
% 2.94/1.00  merged_defs_ncl:                        0
% 2.94/1.00  bin_hyper_res:                          0
% 2.94/1.00  prep_cycles:                            3
% 2.94/1.00  pred_elim_time:                         0.015
% 2.94/1.00  splitting_time:                         0.
% 2.94/1.00  sem_filter_time:                        0.
% 2.94/1.00  monotx_time:                            0.
% 2.94/1.00  subtype_inf_time:                       0.
% 2.94/1.00  
% 2.94/1.00  ------ Problem properties
% 2.94/1.00  
% 2.94/1.00  clauses:                                36
% 2.94/1.00  conjectures:                            3
% 2.94/1.00  epr:                                    4
% 2.94/1.00  horn:                                   29
% 2.94/1.00  ground:                                 16
% 2.94/1.00  unary:                                  8
% 2.94/1.00  binary:                                 10
% 2.94/1.00  lits:                                   95
% 2.94/1.00  lits_eq:                                40
% 2.94/1.00  fd_pure:                                0
% 2.94/1.00  fd_pseudo:                              0
% 2.94/1.00  fd_cond:                                2
% 2.94/1.00  fd_pseudo_cond:                         3
% 2.94/1.00  ac_symbols:                             0
% 2.94/1.00  
% 2.94/1.00  ------ Propositional Solver
% 2.94/1.00  
% 2.94/1.00  prop_solver_calls:                      25
% 2.94/1.00  prop_fast_solver_calls:                 1125
% 2.94/1.00  smt_solver_calls:                       0
% 2.94/1.00  smt_fast_solver_calls:                  0
% 2.94/1.00  prop_num_of_clauses:                    2285
% 2.94/1.00  prop_preprocess_simplified:             5790
% 2.94/1.00  prop_fo_subsumed:                       34
% 2.94/1.00  prop_solver_time:                       0.
% 2.94/1.00  smt_solver_time:                        0.
% 2.94/1.00  smt_fast_solver_time:                   0.
% 2.94/1.00  prop_fast_solver_time:                  0.
% 2.94/1.00  prop_unsat_core_time:                   0.
% 2.94/1.00  
% 2.94/1.00  ------ QBF
% 2.94/1.00  
% 2.94/1.00  qbf_q_res:                              0
% 2.94/1.00  qbf_num_tautologies:                    0
% 2.94/1.00  qbf_prep_cycles:                        0
% 2.94/1.00  
% 2.94/1.00  ------ BMC1
% 2.94/1.00  
% 2.94/1.00  bmc1_current_bound:                     -1
% 2.94/1.00  bmc1_last_solved_bound:                 -1
% 2.94/1.00  bmc1_unsat_core_size:                   -1
% 2.94/1.00  bmc1_unsat_core_parents_size:           -1
% 2.94/1.00  bmc1_merge_next_fun:                    0
% 2.94/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation
% 2.94/1.00  
% 2.94/1.00  inst_num_of_clauses:                    848
% 2.94/1.00  inst_num_in_passive:                    10
% 2.94/1.00  inst_num_in_active:                     417
% 2.94/1.00  inst_num_in_unprocessed:                421
% 2.94/1.00  inst_num_of_loops:                      490
% 2.94/1.00  inst_num_of_learning_restarts:          0
% 2.94/1.00  inst_num_moves_active_passive:          69
% 2.94/1.00  inst_lit_activity:                      0
% 2.94/1.00  inst_lit_activity_moves:                0
% 2.94/1.00  inst_num_tautologies:                   0
% 2.94/1.00  inst_num_prop_implied:                  0
% 2.94/1.00  inst_num_existing_simplified:           0
% 2.94/1.00  inst_num_eq_res_simplified:             0
% 2.94/1.00  inst_num_child_elim:                    0
% 2.94/1.00  inst_num_of_dismatching_blockings:      101
% 2.94/1.00  inst_num_of_non_proper_insts:           742
% 2.94/1.00  inst_num_of_duplicates:                 0
% 2.94/1.00  inst_inst_num_from_inst_to_res:         0
% 2.94/1.00  inst_dismatching_checking_time:         0.
% 2.94/1.00  
% 2.94/1.00  ------ Resolution
% 2.94/1.00  
% 2.94/1.00  res_num_of_clauses:                     0
% 2.94/1.00  res_num_in_passive:                     0
% 2.94/1.00  res_num_in_active:                      0
% 2.94/1.00  res_num_of_loops:                       141
% 2.94/1.00  res_forward_subset_subsumed:            23
% 2.94/1.00  res_backward_subset_subsumed:           2
% 2.94/1.00  res_forward_subsumed:                   0
% 2.94/1.00  res_backward_subsumed:                  0
% 2.94/1.00  res_forward_subsumption_resolution:     3
% 2.94/1.00  res_backward_subsumption_resolution:    0
% 2.94/1.00  res_clause_to_clause_subsumption:       202
% 2.94/1.00  res_orphan_elimination:                 0
% 2.94/1.00  res_tautology_del:                      68
% 2.94/1.00  res_num_eq_res_simplified:              0
% 2.94/1.00  res_num_sel_changes:                    0
% 2.94/1.00  res_moves_from_active_to_pass:          0
% 2.94/1.00  
% 2.94/1.00  ------ Superposition
% 2.94/1.00  
% 2.94/1.00  sup_time_total:                         0.
% 2.94/1.00  sup_time_generating:                    0.
% 2.94/1.00  sup_time_sim_full:                      0.
% 2.94/1.00  sup_time_sim_immed:                     0.
% 2.94/1.00  
% 2.94/1.00  sup_num_of_clauses:                     81
% 2.94/1.00  sup_num_in_active:                      55
% 2.94/1.00  sup_num_in_passive:                     26
% 2.94/1.00  sup_num_of_loops:                       96
% 2.94/1.00  sup_fw_superposition:                   46
% 2.94/1.00  sup_bw_superposition:                   59
% 2.94/1.00  sup_immediate_simplified:               65
% 2.94/1.00  sup_given_eliminated:                   2
% 2.94/1.00  comparisons_done:                       0
% 2.94/1.00  comparisons_avoided:                    7
% 2.94/1.00  
% 2.94/1.00  ------ Simplifications
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  sim_fw_subset_subsumed:                 16
% 2.94/1.00  sim_bw_subset_subsumed:                 5
% 2.94/1.00  sim_fw_subsumed:                        4
% 2.94/1.00  sim_bw_subsumed:                        1
% 2.94/1.00  sim_fw_subsumption_res:                 1
% 2.94/1.00  sim_bw_subsumption_res:                 3
% 2.94/1.00  sim_tautology_del:                      5
% 2.94/1.00  sim_eq_tautology_del:                   13
% 2.94/1.00  sim_eq_res_simp:                        2
% 2.94/1.00  sim_fw_demodulated:                     23
% 2.94/1.00  sim_bw_demodulated:                     44
% 2.94/1.00  sim_light_normalised:                   48
% 2.94/1.00  sim_joinable_taut:                      0
% 2.94/1.00  sim_joinable_simp:                      0
% 2.94/1.00  sim_ac_normalised:                      0
% 2.94/1.00  sim_smt_subsumption:                    0
% 2.94/1.00  
%------------------------------------------------------------------------------
