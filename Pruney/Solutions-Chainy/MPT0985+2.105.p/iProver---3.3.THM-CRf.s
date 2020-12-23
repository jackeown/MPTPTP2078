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
% DateTime   : Thu Dec  3 12:02:41 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  187 (1896 expanded)
%              Number of clauses        :  111 ( 642 expanded)
%              Number of leaves         :   20 ( 359 expanded)
%              Depth                    :   23
%              Number of atoms          :  545 (9709 expanded)
%              Number of equality atoms :  252 (2122 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
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

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f53,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f64,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f54,f64])).

fof(f110,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f111,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f109,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f107,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f114,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f65])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f118,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f23,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK1(X0,X1),X0,X1)
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK1(X0,X1),X0,X1)
      & v1_funct_1(sK1(X0,X1))
      & v1_relat_1(sK1(X0,X1))
      & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f62])).

fof(f105,plain,(
    ! [X0,X1] : v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f63])).

fof(f9,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f59])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f102,plain,(
    ! [X0,X1] : m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_833,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_47])).

cnf(c_834,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_836,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_46])).

cnf(c_1624,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1630,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4214,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1624,c_1630])).

cnf(c_4302,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_836,c_4214])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1632,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3325,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1632])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1639,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3502,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3325,c_1639])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1629,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3390,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1624,c_1629])).

cnf(c_44,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3402,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3390,c_44])).

cnf(c_3511,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3502,c_3402])).

cnf(c_4451,plain,
    ( k9_relat_1(sK4,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4302,c_3511])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_45,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_561,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_45])).

cnf(c_562,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_564,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_48])).

cnf(c_1619,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_3414,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3402,c_1619])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_2015,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2016,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_3661,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3414,c_51,c_2016])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_43,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_857,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK4) != X0
    | k2_relat_1(X0) != sK2
    | k1_relat_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_43])).

cnf(c_858,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_870,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_858,c_23])).

cnf(c_1607,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_870])).

cnf(c_49,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_859,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1985,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1986,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1985])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1998,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1999,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2267,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_49,c_51,c_859,c_1986,c_1999,c_2016])).

cnf(c_2268,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2267])).

cnf(c_3664,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3661,c_2268])).

cnf(c_4931,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3664])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_575,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_45])).

cnf(c_576,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_578,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_48])).

cnf(c_1618,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_3504,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3325,c_1618])).

cnf(c_4933,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4931,c_3504])).

cnf(c_4937,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_4933])).

cnf(c_40,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3774,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3504,c_1625])).

cnf(c_3804,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3774,c_3661])).

cnf(c_5428,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3804,c_49,c_51,c_1986,c_1999,c_2016])).

cnf(c_5433,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_5428])).

cnf(c_5500,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4451,c_4937,c_5433])).

cnf(c_5504,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5500,c_5428])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_5614,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5504,c_5])).

cnf(c_36,plain,
    ( v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_844,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | sK1(X0,X1) != k2_funct_1(sK4)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_43])).

cnf(c_845,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | sK1(sK3,sK2) != k2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_1608,plain,
    ( sK1(sK3,sK2) != k2_funct_1(sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_846,plain,
    ( sK1(sK3,sK2) != k2_funct_1(sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_2190,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | sK1(sK3,sK2) != k2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1608,c_49,c_51,c_846,c_1986,c_2016])).

cnf(c_2191,plain,
    ( sK1(sK3,sK2) != k2_funct_1(sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2190])).

cnf(c_5524,plain,
    ( sK1(k1_xboole_0,sK2) != k2_funct_1(sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5500,c_2191])).

cnf(c_5543,plain,
    ( sK1(k1_xboole_0,sK2) != k2_funct_1(sK4)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5524,c_5])).

cnf(c_5617,plain,
    ( sK1(k1_xboole_0,sK2) != k2_funct_1(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5614,c_5543])).

cnf(c_12,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22,plain,
    ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2187,plain,
    ( k2_funct_1(k1_xboole_0) = k6_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_22])).

cnf(c_2188,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2187,c_12])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1622,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_3258,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1622])).

cnf(c_5514,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5500,c_3258])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_5586,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5514,c_4])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_160,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6587,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5586,c_160])).

cnf(c_8033,plain,
    ( sK1(k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5617,c_2188,c_6587])).

cnf(c_39,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1626,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2879,plain,
    ( m1_subset_1(sK1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1626])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_513,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X3 != X2
    | sK0(X3) != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_1621,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_3080,plain,
    ( sK1(k1_xboole_0,X0) = k1_xboole_0
    | m1_subset_1(sK0(sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2879,c_1621])).

cnf(c_3260,plain,
    ( sK1(k1_xboole_0,X0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2879,c_1622])).

cnf(c_8019,plain,
    ( sK1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3080,c_160,c_3260])).

cnf(c_8034,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8033,c_8019])).

cnf(c_8035,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8034])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.87/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.02  
% 2.87/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/1.02  
% 2.87/1.02  ------  iProver source info
% 2.87/1.02  
% 2.87/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.87/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/1.02  git: non_committed_changes: false
% 2.87/1.02  git: last_make_outside_of_git: false
% 2.87/1.02  
% 2.87/1.02  ------ 
% 2.87/1.02  
% 2.87/1.02  ------ Input Options
% 2.87/1.02  
% 2.87/1.02  --out_options                           all
% 2.87/1.02  --tptp_safe_out                         true
% 2.87/1.02  --problem_path                          ""
% 2.87/1.02  --include_path                          ""
% 2.87/1.02  --clausifier                            res/vclausify_rel
% 2.87/1.02  --clausifier_options                    --mode clausify
% 2.87/1.02  --stdin                                 false
% 2.87/1.02  --stats_out                             all
% 2.87/1.02  
% 2.87/1.02  ------ General Options
% 2.87/1.02  
% 2.87/1.02  --fof                                   false
% 2.87/1.02  --time_out_real                         305.
% 2.87/1.02  --time_out_virtual                      -1.
% 2.87/1.02  --symbol_type_check                     false
% 2.87/1.02  --clausify_out                          false
% 2.87/1.02  --sig_cnt_out                           false
% 2.87/1.02  --trig_cnt_out                          false
% 2.87/1.02  --trig_cnt_out_tolerance                1.
% 2.87/1.02  --trig_cnt_out_sk_spl                   false
% 2.87/1.02  --abstr_cl_out                          false
% 2.87/1.02  
% 2.87/1.02  ------ Global Options
% 2.87/1.02  
% 2.87/1.02  --schedule                              default
% 2.87/1.02  --add_important_lit                     false
% 2.87/1.02  --prop_solver_per_cl                    1000
% 2.87/1.02  --min_unsat_core                        false
% 2.87/1.02  --soft_assumptions                      false
% 2.87/1.02  --soft_lemma_size                       3
% 2.87/1.02  --prop_impl_unit_size                   0
% 2.87/1.02  --prop_impl_unit                        []
% 2.87/1.02  --share_sel_clauses                     true
% 2.87/1.02  --reset_solvers                         false
% 2.87/1.02  --bc_imp_inh                            [conj_cone]
% 2.87/1.02  --conj_cone_tolerance                   3.
% 2.87/1.02  --extra_neg_conj                        none
% 2.87/1.02  --large_theory_mode                     true
% 2.87/1.02  --prolific_symb_bound                   200
% 2.87/1.02  --lt_threshold                          2000
% 2.87/1.02  --clause_weak_htbl                      true
% 2.87/1.02  --gc_record_bc_elim                     false
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing Options
% 2.87/1.02  
% 2.87/1.02  --preprocessing_flag                    true
% 2.87/1.02  --time_out_prep_mult                    0.1
% 2.87/1.02  --splitting_mode                        input
% 2.87/1.02  --splitting_grd                         true
% 2.87/1.02  --splitting_cvd                         false
% 2.87/1.02  --splitting_cvd_svl                     false
% 2.87/1.02  --splitting_nvd                         32
% 2.87/1.02  --sub_typing                            true
% 2.87/1.02  --prep_gs_sim                           true
% 2.87/1.02  --prep_unflatten                        true
% 2.87/1.02  --prep_res_sim                          true
% 2.87/1.02  --prep_upred                            true
% 2.87/1.02  --prep_sem_filter                       exhaustive
% 2.87/1.02  --prep_sem_filter_out                   false
% 2.87/1.02  --pred_elim                             true
% 2.87/1.02  --res_sim_input                         true
% 2.87/1.02  --eq_ax_congr_red                       true
% 2.87/1.02  --pure_diseq_elim                       true
% 2.87/1.02  --brand_transform                       false
% 2.87/1.02  --non_eq_to_eq                          false
% 2.87/1.02  --prep_def_merge                        true
% 2.87/1.02  --prep_def_merge_prop_impl              false
% 2.87/1.02  --prep_def_merge_mbd                    true
% 2.87/1.02  --prep_def_merge_tr_red                 false
% 2.87/1.02  --prep_def_merge_tr_cl                  false
% 2.87/1.02  --smt_preprocessing                     true
% 2.87/1.02  --smt_ac_axioms                         fast
% 2.87/1.02  --preprocessed_out                      false
% 2.87/1.02  --preprocessed_stats                    false
% 2.87/1.02  
% 2.87/1.02  ------ Abstraction refinement Options
% 2.87/1.02  
% 2.87/1.02  --abstr_ref                             []
% 2.87/1.02  --abstr_ref_prep                        false
% 2.87/1.02  --abstr_ref_until_sat                   false
% 2.87/1.02  --abstr_ref_sig_restrict                funpre
% 2.87/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.02  --abstr_ref_under                       []
% 2.87/1.02  
% 2.87/1.02  ------ SAT Options
% 2.87/1.02  
% 2.87/1.02  --sat_mode                              false
% 2.87/1.02  --sat_fm_restart_options                ""
% 2.87/1.02  --sat_gr_def                            false
% 2.87/1.02  --sat_epr_types                         true
% 2.87/1.02  --sat_non_cyclic_types                  false
% 2.87/1.02  --sat_finite_models                     false
% 2.87/1.02  --sat_fm_lemmas                         false
% 2.87/1.02  --sat_fm_prep                           false
% 2.87/1.02  --sat_fm_uc_incr                        true
% 2.87/1.02  --sat_out_model                         small
% 2.87/1.02  --sat_out_clauses                       false
% 2.87/1.02  
% 2.87/1.02  ------ QBF Options
% 2.87/1.02  
% 2.87/1.02  --qbf_mode                              false
% 2.87/1.02  --qbf_elim_univ                         false
% 2.87/1.02  --qbf_dom_inst                          none
% 2.87/1.02  --qbf_dom_pre_inst                      false
% 2.87/1.02  --qbf_sk_in                             false
% 2.87/1.02  --qbf_pred_elim                         true
% 2.87/1.02  --qbf_split                             512
% 2.87/1.02  
% 2.87/1.02  ------ BMC1 Options
% 2.87/1.02  
% 2.87/1.02  --bmc1_incremental                      false
% 2.87/1.02  --bmc1_axioms                           reachable_all
% 2.87/1.02  --bmc1_min_bound                        0
% 2.87/1.02  --bmc1_max_bound                        -1
% 2.87/1.02  --bmc1_max_bound_default                -1
% 2.87/1.02  --bmc1_symbol_reachability              true
% 2.87/1.02  --bmc1_property_lemmas                  false
% 2.87/1.02  --bmc1_k_induction                      false
% 2.87/1.02  --bmc1_non_equiv_states                 false
% 2.87/1.02  --bmc1_deadlock                         false
% 2.87/1.02  --bmc1_ucm                              false
% 2.87/1.02  --bmc1_add_unsat_core                   none
% 2.87/1.02  --bmc1_unsat_core_children              false
% 2.87/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.02  --bmc1_out_stat                         full
% 2.87/1.02  --bmc1_ground_init                      false
% 2.87/1.02  --bmc1_pre_inst_next_state              false
% 2.87/1.02  --bmc1_pre_inst_state                   false
% 2.87/1.02  --bmc1_pre_inst_reach_state             false
% 2.87/1.02  --bmc1_out_unsat_core                   false
% 2.87/1.02  --bmc1_aig_witness_out                  false
% 2.87/1.02  --bmc1_verbose                          false
% 2.87/1.02  --bmc1_dump_clauses_tptp                false
% 2.87/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.02  --bmc1_dump_file                        -
% 2.87/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.02  --bmc1_ucm_extend_mode                  1
% 2.87/1.02  --bmc1_ucm_init_mode                    2
% 2.87/1.02  --bmc1_ucm_cone_mode                    none
% 2.87/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.02  --bmc1_ucm_relax_model                  4
% 2.87/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.02  --bmc1_ucm_layered_model                none
% 2.87/1.02  --bmc1_ucm_max_lemma_size               10
% 2.87/1.02  
% 2.87/1.02  ------ AIG Options
% 2.87/1.02  
% 2.87/1.02  --aig_mode                              false
% 2.87/1.02  
% 2.87/1.02  ------ Instantiation Options
% 2.87/1.02  
% 2.87/1.02  --instantiation_flag                    true
% 2.87/1.02  --inst_sos_flag                         false
% 2.87/1.02  --inst_sos_phase                        true
% 2.87/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.02  --inst_lit_sel_side                     num_symb
% 2.87/1.02  --inst_solver_per_active                1400
% 2.87/1.02  --inst_solver_calls_frac                1.
% 2.87/1.02  --inst_passive_queue_type               priority_queues
% 2.87/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.02  --inst_passive_queues_freq              [25;2]
% 2.87/1.02  --inst_dismatching                      true
% 2.87/1.02  --inst_eager_unprocessed_to_passive     true
% 2.87/1.02  --inst_prop_sim_given                   true
% 2.87/1.02  --inst_prop_sim_new                     false
% 2.87/1.02  --inst_subs_new                         false
% 2.87/1.02  --inst_eq_res_simp                      false
% 2.87/1.02  --inst_subs_given                       false
% 2.87/1.02  --inst_orphan_elimination               true
% 2.87/1.02  --inst_learning_loop_flag               true
% 2.87/1.02  --inst_learning_start                   3000
% 2.87/1.02  --inst_learning_factor                  2
% 2.87/1.02  --inst_start_prop_sim_after_learn       3
% 2.87/1.02  --inst_sel_renew                        solver
% 2.87/1.02  --inst_lit_activity_flag                true
% 2.87/1.02  --inst_restr_to_given                   false
% 2.87/1.02  --inst_activity_threshold               500
% 2.87/1.02  --inst_out_proof                        true
% 2.87/1.02  
% 2.87/1.02  ------ Resolution Options
% 2.87/1.02  
% 2.87/1.02  --resolution_flag                       true
% 2.87/1.02  --res_lit_sel                           adaptive
% 2.87/1.02  --res_lit_sel_side                      none
% 2.87/1.02  --res_ordering                          kbo
% 2.87/1.02  --res_to_prop_solver                    active
% 2.87/1.02  --res_prop_simpl_new                    false
% 2.87/1.02  --res_prop_simpl_given                  true
% 2.87/1.02  --res_passive_queue_type                priority_queues
% 2.87/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.02  --res_passive_queues_freq               [15;5]
% 2.87/1.02  --res_forward_subs                      full
% 2.87/1.02  --res_backward_subs                     full
% 2.87/1.02  --res_forward_subs_resolution           true
% 2.87/1.02  --res_backward_subs_resolution          true
% 2.87/1.02  --res_orphan_elimination                true
% 2.87/1.02  --res_time_limit                        2.
% 2.87/1.02  --res_out_proof                         true
% 2.87/1.02  
% 2.87/1.02  ------ Superposition Options
% 2.87/1.02  
% 2.87/1.02  --superposition_flag                    true
% 2.87/1.02  --sup_passive_queue_type                priority_queues
% 2.87/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.02  --demod_completeness_check              fast
% 2.87/1.02  --demod_use_ground                      true
% 2.87/1.02  --sup_to_prop_solver                    passive
% 2.87/1.02  --sup_prop_simpl_new                    true
% 2.87/1.02  --sup_prop_simpl_given                  true
% 2.87/1.02  --sup_fun_splitting                     false
% 2.87/1.02  --sup_smt_interval                      50000
% 2.87/1.02  
% 2.87/1.02  ------ Superposition Simplification Setup
% 2.87/1.02  
% 2.87/1.02  --sup_indices_passive                   []
% 2.87/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_full_bw                           [BwDemod]
% 2.87/1.02  --sup_immed_triv                        [TrivRules]
% 2.87/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_immed_bw_main                     []
% 2.87/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.02  
% 2.87/1.02  ------ Combination Options
% 2.87/1.02  
% 2.87/1.02  --comb_res_mult                         3
% 2.87/1.02  --comb_sup_mult                         2
% 2.87/1.02  --comb_inst_mult                        10
% 2.87/1.02  
% 2.87/1.02  ------ Debug Options
% 2.87/1.02  
% 2.87/1.02  --dbg_backtrace                         false
% 2.87/1.02  --dbg_dump_prop_clauses                 false
% 2.87/1.02  --dbg_dump_prop_clauses_file            -
% 2.87/1.02  --dbg_out_stat                          false
% 2.87/1.02  ------ Parsing...
% 2.87/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/1.02  ------ Proving...
% 2.87/1.02  ------ Problem Properties 
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  clauses                                 50
% 2.87/1.02  conjectures                             3
% 2.87/1.02  EPR                                     4
% 2.87/1.02  Horn                                    42
% 2.87/1.02  unary                                   16
% 2.87/1.02  binary                                  13
% 2.87/1.02  lits                                    118
% 2.87/1.02  lits eq                                 55
% 2.87/1.02  fd_pure                                 0
% 2.87/1.02  fd_pseudo                               0
% 2.87/1.02  fd_cond                                 7
% 2.87/1.02  fd_pseudo_cond                          1
% 2.87/1.02  AC symbols                              0
% 2.87/1.02  
% 2.87/1.02  ------ Schedule dynamic 5 is on 
% 2.87/1.02  
% 2.87/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  ------ 
% 2.87/1.02  Current options:
% 2.87/1.02  ------ 
% 2.87/1.02  
% 2.87/1.02  ------ Input Options
% 2.87/1.02  
% 2.87/1.02  --out_options                           all
% 2.87/1.02  --tptp_safe_out                         true
% 2.87/1.02  --problem_path                          ""
% 2.87/1.02  --include_path                          ""
% 2.87/1.02  --clausifier                            res/vclausify_rel
% 2.87/1.02  --clausifier_options                    --mode clausify
% 2.87/1.02  --stdin                                 false
% 2.87/1.02  --stats_out                             all
% 2.87/1.02  
% 2.87/1.02  ------ General Options
% 2.87/1.02  
% 2.87/1.02  --fof                                   false
% 2.87/1.02  --time_out_real                         305.
% 2.87/1.02  --time_out_virtual                      -1.
% 2.87/1.02  --symbol_type_check                     false
% 2.87/1.02  --clausify_out                          false
% 2.87/1.02  --sig_cnt_out                           false
% 2.87/1.02  --trig_cnt_out                          false
% 2.87/1.02  --trig_cnt_out_tolerance                1.
% 2.87/1.02  --trig_cnt_out_sk_spl                   false
% 2.87/1.02  --abstr_cl_out                          false
% 2.87/1.02  
% 2.87/1.02  ------ Global Options
% 2.87/1.02  
% 2.87/1.02  --schedule                              default
% 2.87/1.02  --add_important_lit                     false
% 2.87/1.02  --prop_solver_per_cl                    1000
% 2.87/1.02  --min_unsat_core                        false
% 2.87/1.02  --soft_assumptions                      false
% 2.87/1.02  --soft_lemma_size                       3
% 2.87/1.02  --prop_impl_unit_size                   0
% 2.87/1.02  --prop_impl_unit                        []
% 2.87/1.02  --share_sel_clauses                     true
% 2.87/1.02  --reset_solvers                         false
% 2.87/1.02  --bc_imp_inh                            [conj_cone]
% 2.87/1.02  --conj_cone_tolerance                   3.
% 2.87/1.02  --extra_neg_conj                        none
% 2.87/1.02  --large_theory_mode                     true
% 2.87/1.02  --prolific_symb_bound                   200
% 2.87/1.02  --lt_threshold                          2000
% 2.87/1.02  --clause_weak_htbl                      true
% 2.87/1.02  --gc_record_bc_elim                     false
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing Options
% 2.87/1.02  
% 2.87/1.02  --preprocessing_flag                    true
% 2.87/1.02  --time_out_prep_mult                    0.1
% 2.87/1.02  --splitting_mode                        input
% 2.87/1.02  --splitting_grd                         true
% 2.87/1.02  --splitting_cvd                         false
% 2.87/1.02  --splitting_cvd_svl                     false
% 2.87/1.02  --splitting_nvd                         32
% 2.87/1.02  --sub_typing                            true
% 2.87/1.02  --prep_gs_sim                           true
% 2.87/1.02  --prep_unflatten                        true
% 2.87/1.02  --prep_res_sim                          true
% 2.87/1.02  --prep_upred                            true
% 2.87/1.02  --prep_sem_filter                       exhaustive
% 2.87/1.02  --prep_sem_filter_out                   false
% 2.87/1.02  --pred_elim                             true
% 2.87/1.02  --res_sim_input                         true
% 2.87/1.02  --eq_ax_congr_red                       true
% 2.87/1.02  --pure_diseq_elim                       true
% 2.87/1.02  --brand_transform                       false
% 2.87/1.02  --non_eq_to_eq                          false
% 2.87/1.02  --prep_def_merge                        true
% 2.87/1.02  --prep_def_merge_prop_impl              false
% 2.87/1.02  --prep_def_merge_mbd                    true
% 2.87/1.02  --prep_def_merge_tr_red                 false
% 2.87/1.02  --prep_def_merge_tr_cl                  false
% 2.87/1.02  --smt_preprocessing                     true
% 2.87/1.02  --smt_ac_axioms                         fast
% 2.87/1.02  --preprocessed_out                      false
% 2.87/1.02  --preprocessed_stats                    false
% 2.87/1.02  
% 2.87/1.02  ------ Abstraction refinement Options
% 2.87/1.02  
% 2.87/1.02  --abstr_ref                             []
% 2.87/1.02  --abstr_ref_prep                        false
% 2.87/1.02  --abstr_ref_until_sat                   false
% 2.87/1.02  --abstr_ref_sig_restrict                funpre
% 2.87/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.02  --abstr_ref_under                       []
% 2.87/1.02  
% 2.87/1.02  ------ SAT Options
% 2.87/1.02  
% 2.87/1.02  --sat_mode                              false
% 2.87/1.02  --sat_fm_restart_options                ""
% 2.87/1.02  --sat_gr_def                            false
% 2.87/1.02  --sat_epr_types                         true
% 2.87/1.02  --sat_non_cyclic_types                  false
% 2.87/1.02  --sat_finite_models                     false
% 2.87/1.02  --sat_fm_lemmas                         false
% 2.87/1.02  --sat_fm_prep                           false
% 2.87/1.02  --sat_fm_uc_incr                        true
% 2.87/1.02  --sat_out_model                         small
% 2.87/1.02  --sat_out_clauses                       false
% 2.87/1.02  
% 2.87/1.02  ------ QBF Options
% 2.87/1.02  
% 2.87/1.02  --qbf_mode                              false
% 2.87/1.02  --qbf_elim_univ                         false
% 2.87/1.02  --qbf_dom_inst                          none
% 2.87/1.02  --qbf_dom_pre_inst                      false
% 2.87/1.02  --qbf_sk_in                             false
% 2.87/1.02  --qbf_pred_elim                         true
% 2.87/1.02  --qbf_split                             512
% 2.87/1.02  
% 2.87/1.02  ------ BMC1 Options
% 2.87/1.02  
% 2.87/1.02  --bmc1_incremental                      false
% 2.87/1.02  --bmc1_axioms                           reachable_all
% 2.87/1.02  --bmc1_min_bound                        0
% 2.87/1.02  --bmc1_max_bound                        -1
% 2.87/1.02  --bmc1_max_bound_default                -1
% 2.87/1.02  --bmc1_symbol_reachability              true
% 2.87/1.02  --bmc1_property_lemmas                  false
% 2.87/1.02  --bmc1_k_induction                      false
% 2.87/1.02  --bmc1_non_equiv_states                 false
% 2.87/1.02  --bmc1_deadlock                         false
% 2.87/1.02  --bmc1_ucm                              false
% 2.87/1.02  --bmc1_add_unsat_core                   none
% 2.87/1.02  --bmc1_unsat_core_children              false
% 2.87/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.02  --bmc1_out_stat                         full
% 2.87/1.02  --bmc1_ground_init                      false
% 2.87/1.02  --bmc1_pre_inst_next_state              false
% 2.87/1.02  --bmc1_pre_inst_state                   false
% 2.87/1.02  --bmc1_pre_inst_reach_state             false
% 2.87/1.02  --bmc1_out_unsat_core                   false
% 2.87/1.02  --bmc1_aig_witness_out                  false
% 2.87/1.02  --bmc1_verbose                          false
% 2.87/1.02  --bmc1_dump_clauses_tptp                false
% 2.87/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.02  --bmc1_dump_file                        -
% 2.87/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.02  --bmc1_ucm_extend_mode                  1
% 2.87/1.02  --bmc1_ucm_init_mode                    2
% 2.87/1.02  --bmc1_ucm_cone_mode                    none
% 2.87/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.02  --bmc1_ucm_relax_model                  4
% 2.87/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.02  --bmc1_ucm_layered_model                none
% 2.87/1.02  --bmc1_ucm_max_lemma_size               10
% 2.87/1.02  
% 2.87/1.02  ------ AIG Options
% 2.87/1.02  
% 2.87/1.02  --aig_mode                              false
% 2.87/1.02  
% 2.87/1.02  ------ Instantiation Options
% 2.87/1.02  
% 2.87/1.02  --instantiation_flag                    true
% 2.87/1.02  --inst_sos_flag                         false
% 2.87/1.02  --inst_sos_phase                        true
% 2.87/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.02  --inst_lit_sel_side                     none
% 2.87/1.02  --inst_solver_per_active                1400
% 2.87/1.02  --inst_solver_calls_frac                1.
% 2.87/1.02  --inst_passive_queue_type               priority_queues
% 2.87/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.02  --inst_passive_queues_freq              [25;2]
% 2.87/1.02  --inst_dismatching                      true
% 2.87/1.02  --inst_eager_unprocessed_to_passive     true
% 2.87/1.02  --inst_prop_sim_given                   true
% 2.87/1.02  --inst_prop_sim_new                     false
% 2.87/1.02  --inst_subs_new                         false
% 2.87/1.02  --inst_eq_res_simp                      false
% 2.87/1.02  --inst_subs_given                       false
% 2.87/1.02  --inst_orphan_elimination               true
% 2.87/1.02  --inst_learning_loop_flag               true
% 2.87/1.02  --inst_learning_start                   3000
% 2.87/1.02  --inst_learning_factor                  2
% 2.87/1.02  --inst_start_prop_sim_after_learn       3
% 2.87/1.02  --inst_sel_renew                        solver
% 2.87/1.02  --inst_lit_activity_flag                true
% 2.87/1.02  --inst_restr_to_given                   false
% 2.87/1.02  --inst_activity_threshold               500
% 2.87/1.02  --inst_out_proof                        true
% 2.87/1.02  
% 2.87/1.02  ------ Resolution Options
% 2.87/1.02  
% 2.87/1.02  --resolution_flag                       false
% 2.87/1.02  --res_lit_sel                           adaptive
% 2.87/1.02  --res_lit_sel_side                      none
% 2.87/1.02  --res_ordering                          kbo
% 2.87/1.02  --res_to_prop_solver                    active
% 2.87/1.02  --res_prop_simpl_new                    false
% 2.87/1.02  --res_prop_simpl_given                  true
% 2.87/1.02  --res_passive_queue_type                priority_queues
% 2.87/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.02  --res_passive_queues_freq               [15;5]
% 2.87/1.02  --res_forward_subs                      full
% 2.87/1.02  --res_backward_subs                     full
% 2.87/1.02  --res_forward_subs_resolution           true
% 2.87/1.02  --res_backward_subs_resolution          true
% 2.87/1.02  --res_orphan_elimination                true
% 2.87/1.02  --res_time_limit                        2.
% 2.87/1.02  --res_out_proof                         true
% 2.87/1.02  
% 2.87/1.02  ------ Superposition Options
% 2.87/1.02  
% 2.87/1.02  --superposition_flag                    true
% 2.87/1.02  --sup_passive_queue_type                priority_queues
% 2.87/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.02  --demod_completeness_check              fast
% 2.87/1.02  --demod_use_ground                      true
% 2.87/1.02  --sup_to_prop_solver                    passive
% 2.87/1.02  --sup_prop_simpl_new                    true
% 2.87/1.02  --sup_prop_simpl_given                  true
% 2.87/1.02  --sup_fun_splitting                     false
% 2.87/1.02  --sup_smt_interval                      50000
% 2.87/1.02  
% 2.87/1.02  ------ Superposition Simplification Setup
% 2.87/1.02  
% 2.87/1.02  --sup_indices_passive                   []
% 2.87/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_full_bw                           [BwDemod]
% 2.87/1.02  --sup_immed_triv                        [TrivRules]
% 2.87/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_immed_bw_main                     []
% 2.87/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.02  
% 2.87/1.02  ------ Combination Options
% 2.87/1.02  
% 2.87/1.02  --comb_res_mult                         3
% 2.87/1.02  --comb_sup_mult                         2
% 2.87/1.02  --comb_inst_mult                        10
% 2.87/1.02  
% 2.87/1.02  ------ Debug Options
% 2.87/1.02  
% 2.87/1.02  --dbg_backtrace                         false
% 2.87/1.02  --dbg_dump_prop_clauses                 false
% 2.87/1.02  --dbg_dump_prop_clauses_file            -
% 2.87/1.02  --dbg_out_stat                          false
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  ------ Proving...
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  % SZS status Theorem for theBenchmark.p
% 2.87/1.02  
% 2.87/1.02   Resolution empty clause
% 2.87/1.02  
% 2.87/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/1.02  
% 2.87/1.02  fof(f22,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f49,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f22])).
% 2.87/1.02  
% 2.87/1.02  fof(f50,plain,(
% 2.87/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(flattening,[],[f49])).
% 2.87/1.02  
% 2.87/1.02  fof(f61,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(nnf_transformation,[],[f50])).
% 2.87/1.02  
% 2.87/1.02  fof(f96,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f61])).
% 2.87/1.02  
% 2.87/1.02  fof(f25,conjecture,(
% 2.87/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f26,negated_conjecture,(
% 2.87/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.87/1.02    inference(negated_conjecture,[],[f25])).
% 2.87/1.02  
% 2.87/1.02  fof(f53,plain,(
% 2.87/1.02    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.87/1.02    inference(ennf_transformation,[],[f26])).
% 2.87/1.02  
% 2.87/1.02  fof(f54,plain,(
% 2.87/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.87/1.02    inference(flattening,[],[f53])).
% 2.87/1.02  
% 2.87/1.02  fof(f64,plain,(
% 2.87/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.87/1.02    introduced(choice_axiom,[])).
% 2.87/1.02  
% 2.87/1.02  fof(f65,plain,(
% 2.87/1.02    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f54,f64])).
% 2.87/1.02  
% 2.87/1.02  fof(f110,plain,(
% 2.87/1.02    v1_funct_2(sK4,sK2,sK3)),
% 2.87/1.02    inference(cnf_transformation,[],[f65])).
% 2.87/1.02  
% 2.87/1.02  fof(f111,plain,(
% 2.87/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.87/1.02    inference(cnf_transformation,[],[f65])).
% 2.87/1.02  
% 2.87/1.02  fof(f19,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f46,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f19])).
% 2.87/1.02  
% 2.87/1.02  fof(f91,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f46])).
% 2.87/1.02  
% 2.87/1.02  fof(f17,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f44,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f17])).
% 2.87/1.02  
% 2.87/1.02  fof(f89,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f44])).
% 2.87/1.02  
% 2.87/1.02  fof(f7,axiom,(
% 2.87/1.02    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f32,plain,(
% 2.87/1.02    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.87/1.02    inference(ennf_transformation,[],[f7])).
% 2.87/1.02  
% 2.87/1.02  fof(f76,plain,(
% 2.87/1.02    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f32])).
% 2.87/1.02  
% 2.87/1.02  fof(f20,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f47,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f20])).
% 2.87/1.02  
% 2.87/1.02  fof(f92,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f47])).
% 2.87/1.02  
% 2.87/1.02  fof(f113,plain,(
% 2.87/1.02    k2_relset_1(sK2,sK3,sK4) = sK3),
% 2.87/1.02    inference(cnf_transformation,[],[f65])).
% 2.87/1.02  
% 2.87/1.02  fof(f15,axiom,(
% 2.87/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f42,plain,(
% 2.87/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/1.02    inference(ennf_transformation,[],[f15])).
% 2.87/1.02  
% 2.87/1.02  fof(f43,plain,(
% 2.87/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/1.02    inference(flattening,[],[f42])).
% 2.87/1.02  
% 2.87/1.02  fof(f86,plain,(
% 2.87/1.02    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f43])).
% 2.87/1.02  
% 2.87/1.02  fof(f112,plain,(
% 2.87/1.02    v2_funct_1(sK4)),
% 2.87/1.02    inference(cnf_transformation,[],[f65])).
% 2.87/1.02  
% 2.87/1.02  fof(f109,plain,(
% 2.87/1.02    v1_funct_1(sK4)),
% 2.87/1.02    inference(cnf_transformation,[],[f65])).
% 2.87/1.02  
% 2.87/1.02  fof(f24,axiom,(
% 2.87/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f51,plain,(
% 2.87/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/1.02    inference(ennf_transformation,[],[f24])).
% 2.87/1.02  
% 2.87/1.02  fof(f52,plain,(
% 2.87/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/1.02    inference(flattening,[],[f51])).
% 2.87/1.02  
% 2.87/1.02  fof(f107,plain,(
% 2.87/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f52])).
% 2.87/1.02  
% 2.87/1.02  fof(f114,plain,(
% 2.87/1.02    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 2.87/1.02    inference(cnf_transformation,[],[f65])).
% 2.87/1.02  
% 2.87/1.02  fof(f10,axiom,(
% 2.87/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f34,plain,(
% 2.87/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/1.02    inference(ennf_transformation,[],[f10])).
% 2.87/1.02  
% 2.87/1.02  fof(f35,plain,(
% 2.87/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/1.02    inference(flattening,[],[f34])).
% 2.87/1.02  
% 2.87/1.02  fof(f80,plain,(
% 2.87/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f35])).
% 2.87/1.02  
% 2.87/1.02  fof(f79,plain,(
% 2.87/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f35])).
% 2.87/1.02  
% 2.87/1.02  fof(f87,plain,(
% 2.87/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f43])).
% 2.87/1.02  
% 2.87/1.02  fof(f108,plain,(
% 2.87/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f52])).
% 2.87/1.02  
% 2.87/1.02  fof(f3,axiom,(
% 2.87/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f57,plain,(
% 2.87/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.87/1.02    inference(nnf_transformation,[],[f3])).
% 2.87/1.02  
% 2.87/1.02  fof(f58,plain,(
% 2.87/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.87/1.02    inference(flattening,[],[f57])).
% 2.87/1.02  
% 2.87/1.02  fof(f71,plain,(
% 2.87/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.87/1.02    inference(cnf_transformation,[],[f58])).
% 2.87/1.02  
% 2.87/1.02  fof(f118,plain,(
% 2.87/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.87/1.02    inference(equality_resolution,[],[f71])).
% 2.87/1.02  
% 2.87/1.02  fof(f23,axiom,(
% 2.87/1.02    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f27,plain,(
% 2.87/1.02    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(pure_predicate_removal,[],[f23])).
% 2.87/1.02  
% 2.87/1.02  fof(f28,plain,(
% 2.87/1.02    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(pure_predicate_removal,[],[f27])).
% 2.87/1.02  
% 2.87/1.02  fof(f62,plain,(
% 2.87/1.02    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.87/1.02    introduced(choice_axiom,[])).
% 2.87/1.02  
% 2.87/1.02  fof(f63,plain,(
% 2.87/1.02    ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f62])).
% 2.87/1.02  
% 2.87/1.02  fof(f105,plain,(
% 2.87/1.02    ( ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f63])).
% 2.87/1.02  
% 2.87/1.02  fof(f9,axiom,(
% 2.87/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f78,plain,(
% 2.87/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.87/1.02    inference(cnf_transformation,[],[f9])).
% 2.87/1.02  
% 2.87/1.02  fof(f16,axiom,(
% 2.87/1.02    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f88,plain,(
% 2.87/1.02    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f16])).
% 2.87/1.02  
% 2.87/1.02  fof(f6,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f31,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.87/1.02    inference(ennf_transformation,[],[f6])).
% 2.87/1.02  
% 2.87/1.02  fof(f75,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f31])).
% 2.87/1.02  
% 2.87/1.02  fof(f21,axiom,(
% 2.87/1.02    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f48,plain,(
% 2.87/1.02    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.87/1.02    inference(ennf_transformation,[],[f21])).
% 2.87/1.02  
% 2.87/1.02  fof(f59,plain,(
% 2.87/1.02    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.87/1.02    introduced(choice_axiom,[])).
% 2.87/1.02  
% 2.87/1.02  fof(f60,plain,(
% 2.87/1.02    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f59])).
% 2.87/1.02  
% 2.87/1.02  fof(f93,plain,(
% 2.87/1.02    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.87/1.02    inference(cnf_transformation,[],[f60])).
% 2.87/1.02  
% 2.87/1.02  fof(f72,plain,(
% 2.87/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.87/1.02    inference(cnf_transformation,[],[f58])).
% 2.87/1.02  
% 2.87/1.02  fof(f117,plain,(
% 2.87/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.87/1.02    inference(equality_resolution,[],[f72])).
% 2.87/1.02  
% 2.87/1.02  fof(f1,axiom,(
% 2.87/1.02    v1_xboole_0(k1_xboole_0)),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f66,plain,(
% 2.87/1.02    v1_xboole_0(k1_xboole_0)),
% 2.87/1.02    inference(cnf_transformation,[],[f1])).
% 2.87/1.02  
% 2.87/1.02  fof(f102,plain,(
% 2.87/1.02    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f63])).
% 2.87/1.02  
% 2.87/1.02  fof(f5,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f29,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.87/1.02    inference(ennf_transformation,[],[f5])).
% 2.87/1.02  
% 2.87/1.02  fof(f30,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.87/1.02    inference(flattening,[],[f29])).
% 2.87/1.02  
% 2.87/1.02  fof(f74,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f30])).
% 2.87/1.02  
% 2.87/1.02  cnf(c_35,plain,
% 2.87/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.87/1.02      | k1_xboole_0 = X2 ),
% 2.87/1.02      inference(cnf_transformation,[],[f96]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_47,negated_conjecture,
% 2.87/1.02      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.87/1.02      inference(cnf_transformation,[],[f110]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_833,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.87/1.02      | sK2 != X1
% 2.87/1.02      | sK3 != X2
% 2.87/1.02      | sK4 != X0
% 2.87/1.02      | k1_xboole_0 = X2 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_35,c_47]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_834,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.87/1.02      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.87/1.02      | k1_xboole_0 = sK3 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_833]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_46,negated_conjecture,
% 2.87/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.87/1.02      inference(cnf_transformation,[],[f111]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_836,plain,
% 2.87/1.02      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.87/1.02      inference(global_propositional_subsumption,[status(thm)],[c_834,c_46]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1624,plain,
% 2.87/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_25,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f91]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1630,plain,
% 2.87/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.87/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4214,plain,
% 2.87/1.02      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1624,c_1630]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4302,plain,
% 2.87/1.02      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_836,c_4214]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_23,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f89]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1632,plain,
% 2.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.87/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3325,plain,
% 2.87/1.02      ( v1_relat_1(sK4) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1624,c_1632]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_10,plain,
% 2.87/1.02      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1639,plain,
% 2.87/1.02      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.87/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3502,plain,
% 2.87/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_3325,c_1639]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_26,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f92]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1629,plain,
% 2.87/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.87/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3390,plain,
% 2.87/1.02      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1624,c_1629]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_44,negated_conjecture,
% 2.87/1.02      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 2.87/1.02      inference(cnf_transformation,[],[f113]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3402,plain,
% 2.87/1.02      ( k2_relat_1(sK4) = sK3 ),
% 2.87/1.02      inference(light_normalisation,[status(thm)],[c_3390,c_44]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3511,plain,
% 2.87/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = sK3 ),
% 2.87/1.02      inference(light_normalisation,[status(thm)],[c_3502,c_3402]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4451,plain,
% 2.87/1.02      ( k9_relat_1(sK4,sK2) = sK3 | sK3 = k1_xboole_0 ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_4302,c_3511]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_21,plain,
% 2.87/1.02      ( ~ v2_funct_1(X0)
% 2.87/1.02      | ~ v1_funct_1(X0)
% 2.87/1.02      | ~ v1_relat_1(X0)
% 2.87/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_45,negated_conjecture,
% 2.87/1.02      ( v2_funct_1(sK4) ),
% 2.87/1.02      inference(cnf_transformation,[],[f112]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_561,plain,
% 2.87/1.02      ( ~ v1_funct_1(X0)
% 2.87/1.02      | ~ v1_relat_1(X0)
% 2.87/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.87/1.02      | sK4 != X0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_45]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_562,plain,
% 2.87/1.02      ( ~ v1_funct_1(sK4)
% 2.87/1.02      | ~ v1_relat_1(sK4)
% 2.87/1.02      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_561]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_48,negated_conjecture,
% 2.87/1.02      ( v1_funct_1(sK4) ),
% 2.87/1.02      inference(cnf_transformation,[],[f109]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_564,plain,
% 2.87/1.02      ( ~ v1_relat_1(sK4) | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,[status(thm)],[c_562,c_48]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1619,plain,
% 2.87/1.02      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 2.87/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3414,plain,
% 2.87/1.02      ( k1_relat_1(k2_funct_1(sK4)) = sK3 | v1_relat_1(sK4) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_3402,c_1619]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_51,plain,
% 2.87/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2015,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.87/1.02      | v1_relat_1(sK4) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_23]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2016,plain,
% 2.87/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.87/1.02      | v1_relat_1(sK4) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3661,plain,
% 2.87/1.02      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_3414,c_51,c_2016]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_41,plain,
% 2.87/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.87/1.02      | ~ v1_funct_1(X0)
% 2.87/1.02      | ~ v1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f107]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_43,negated_conjecture,
% 2.87/1.02      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 2.87/1.02      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.87/1.02      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 2.87/1.02      inference(cnf_transformation,[],[f114]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_857,plain,
% 2.87/1.02      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.87/1.02      | ~ v1_funct_1(X0)
% 2.87/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.87/1.02      | ~ v1_relat_1(X0)
% 2.87/1.02      | k2_funct_1(sK4) != X0
% 2.87/1.02      | k2_relat_1(X0) != sK2
% 2.87/1.02      | k1_relat_1(X0) != sK3 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_41,c_43]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_858,plain,
% 2.87/1.02      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.87/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.87/1.02      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.87/1.02      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.87/1.02      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_857]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_870,plain,
% 2.87/1.02      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.87/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.87/1.02      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.87/1.02      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 2.87/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_858,c_23]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1607,plain,
% 2.87/1.02      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.87/1.02      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.87/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_870]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_49,plain,
% 2.87/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_859,plain,
% 2.87/1.02      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.87/1.02      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.87/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.87/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_13,plain,
% 2.87/1.02      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1985,plain,
% 2.87/1.02      ( v1_funct_1(k2_funct_1(sK4)) | ~ v1_funct_1(sK4) | ~ v1_relat_1(sK4) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1986,plain,
% 2.87/1.02      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 2.87/1.02      | v1_funct_1(sK4) != iProver_top
% 2.87/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1985]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_14,plain,
% 2.87/1.02      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.87/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1998,plain,
% 2.87/1.02      ( ~ v1_funct_1(sK4) | v1_relat_1(k2_funct_1(sK4)) | ~ v1_relat_1(sK4) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1999,plain,
% 2.87/1.02      ( v1_funct_1(sK4) != iProver_top
% 2.87/1.02      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 2.87/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2267,plain,
% 2.87/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.87/1.02      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.87/1.02      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_1607,c_49,c_51,c_859,c_1986,c_1999,c_2016]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2268,plain,
% 2.87/1.02      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.87/1.02      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_2267]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3664,plain,
% 2.87/1.02      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.87/1.02      | sK3 != sK3
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_3661,c_2268]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4931,plain,
% 2.87/1.02      ( k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.87/1.02      inference(equality_resolution_simp,[status(thm)],[c_3664]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_20,plain,
% 2.87/1.02      ( ~ v2_funct_1(X0)
% 2.87/1.02      | ~ v1_funct_1(X0)
% 2.87/1.02      | ~ v1_relat_1(X0)
% 2.87/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_575,plain,
% 2.87/1.02      ( ~ v1_funct_1(X0)
% 2.87/1.02      | ~ v1_relat_1(X0)
% 2.87/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.87/1.02      | sK4 != X0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_45]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_576,plain,
% 2.87/1.02      ( ~ v1_funct_1(sK4)
% 2.87/1.02      | ~ v1_relat_1(sK4)
% 2.87/1.02      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_575]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_578,plain,
% 2.87/1.02      ( ~ v1_relat_1(sK4) | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,[status(thm)],[c_576,c_48]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1618,plain,
% 2.87/1.02      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 2.87/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3504,plain,
% 2.87/1.02      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_3325,c_1618]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4933,plain,
% 2.87/1.02      ( k1_relat_1(sK4) != sK2
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.87/1.02      inference(light_normalisation,[status(thm)],[c_4931,c_3504]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4937,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_4302,c_4933]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_40,plain,
% 2.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.87/1.02      | ~ v1_funct_1(X0)
% 2.87/1.02      | ~ v1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f108]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1625,plain,
% 2.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.87/1.02      | v1_funct_1(X0) != iProver_top
% 2.87/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3774,plain,
% 2.87/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 2.87/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.87/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_3504,c_1625]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3804,plain,
% 2.87/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 2.87/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.87/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.87/1.02      inference(light_normalisation,[status(thm)],[c_3774,c_3661]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5428,plain,
% 2.87/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_3804,c_49,c_51,c_1986,c_1999,c_2016]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5433,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_4302,c_5428]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5500,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_4451,c_4937,c_5433]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5504,plain,
% 2.87/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_5500,c_5428]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5,plain,
% 2.87/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.87/1.02      inference(cnf_transformation,[],[f118]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5614,plain,
% 2.87/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_5504,c_5]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_36,plain,
% 2.87/1.02      ( v1_funct_2(sK1(X0,X1),X0,X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f105]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_844,plain,
% 2.87/1.02      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.87/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.87/1.02      | sK1(X0,X1) != k2_funct_1(sK4)
% 2.87/1.02      | sK2 != X1
% 2.87/1.02      | sK3 != X0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_36,c_43]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_845,plain,
% 2.87/1.02      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.87/1.02      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.87/1.02      | sK1(sK3,sK2) != k2_funct_1(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_844]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1608,plain,
% 2.87/1.02      ( sK1(sK3,sK2) != k2_funct_1(sK4)
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.87/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_846,plain,
% 2.87/1.02      ( sK1(sK3,sK2) != k2_funct_1(sK4)
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.87/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2190,plain,
% 2.87/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.87/1.02      | sK1(sK3,sK2) != k2_funct_1(sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_1608,c_49,c_51,c_846,c_1986,c_2016]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2191,plain,
% 2.87/1.02      ( sK1(sK3,sK2) != k2_funct_1(sK4)
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_2190]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5524,plain,
% 2.87/1.02      ( sK1(k1_xboole_0,sK2) != k2_funct_1(sK4)
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_5500,c_2191]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5543,plain,
% 2.87/1.02      ( sK1(k1_xboole_0,sK2) != k2_funct_1(sK4)
% 2.87/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_5524,c_5]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5617,plain,
% 2.87/1.02      ( sK1(k1_xboole_0,sK2) != k2_funct_1(sK4) ),
% 2.87/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_5614,c_5543]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_12,plain,
% 2.87/1.02      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.87/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_22,plain,
% 2.87/1.02      ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2187,plain,
% 2.87/1.02      ( k2_funct_1(k1_xboole_0) = k6_relat_1(k1_xboole_0) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_12,c_22]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2188,plain,
% 2.87/1.02      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.87/1.02      inference(light_normalisation,[status(thm)],[c_2187,c_12]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_9,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,X1)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.87/1.02      | ~ v1_xboole_0(X2) ),
% 2.87/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_29,plain,
% 2.87/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.87/1.02      inference(cnf_transformation,[],[f93]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_498,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.87/1.02      | ~ v1_xboole_0(X1)
% 2.87/1.02      | X2 != X0
% 2.87/1.02      | sK0(X2) != X3
% 2.87/1.02      | k1_xboole_0 = X2 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_499,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.87/1.02      | ~ v1_xboole_0(X1)
% 2.87/1.02      | k1_xboole_0 = X0 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_498]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1622,plain,
% 2.87/1.02      ( k1_xboole_0 = X0
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.87/1.02      | v1_xboole_0(X1) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3258,plain,
% 2.87/1.02      ( sK4 = k1_xboole_0 | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1624,c_1622]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5514,plain,
% 2.87/1.02      ( sK4 = k1_xboole_0
% 2.87/1.02      | v1_xboole_0(k2_zfmisc_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_5500,c_3258]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4,plain,
% 2.87/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.87/1.02      inference(cnf_transformation,[],[f117]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5586,plain,
% 2.87/1.02      ( sK4 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_5514,c_4]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_0,plain,
% 2.87/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_160,plain,
% 2.87/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_6587,plain,
% 2.87/1.02      ( sK4 = k1_xboole_0 ),
% 2.87/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5586,c_160]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8033,plain,
% 2.87/1.02      ( sK1(k1_xboole_0,sK2) != k1_xboole_0 ),
% 2.87/1.02      inference(light_normalisation,[status(thm)],[c_5617,c_2188,c_6587]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_39,plain,
% 2.87/1.02      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.87/1.02      inference(cnf_transformation,[],[f102]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1626,plain,
% 2.87/1.02      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2879,plain,
% 2.87/1.02      ( m1_subset_1(sK1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_5,c_1626]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,X1)
% 2.87/1.02      | m1_subset_1(X0,X2)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.87/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_513,plain,
% 2.87/1.02      ( m1_subset_1(X0,X1)
% 2.87/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.87/1.02      | X3 != X2
% 2.87/1.02      | sK0(X3) != X0
% 2.87/1.02      | k1_xboole_0 = X3 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_514,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.87/1.02      | m1_subset_1(sK0(X0),X1)
% 2.87/1.02      | k1_xboole_0 = X0 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_513]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1621,plain,
% 2.87/1.02      ( k1_xboole_0 = X0
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.87/1.02      | m1_subset_1(sK0(X0),X1) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3080,plain,
% 2.87/1.02      ( sK1(k1_xboole_0,X0) = k1_xboole_0
% 2.87/1.02      | m1_subset_1(sK0(sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2879,c_1621]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3260,plain,
% 2.87/1.02      ( sK1(k1_xboole_0,X0) = k1_xboole_0
% 2.87/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2879,c_1622]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8019,plain,
% 2.87/1.02      ( sK1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_3080,c_160,c_3260]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8034,plain,
% 2.87/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_8033,c_8019]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8035,plain,
% 2.87/1.02      ( $false ),
% 2.87/1.02      inference(equality_resolution_simp,[status(thm)],[c_8034]) ).
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.02  
% 2.87/1.02  ------                               Statistics
% 2.87/1.02  
% 2.87/1.02  ------ General
% 2.87/1.02  
% 2.87/1.02  abstr_ref_over_cycles:                  0
% 2.87/1.02  abstr_ref_under_cycles:                 0
% 2.87/1.02  gc_basic_clause_elim:                   0
% 2.87/1.02  forced_gc_time:                         0
% 2.87/1.02  parsing_time:                           0.01
% 2.87/1.02  unif_index_cands_time:                  0.
% 2.87/1.02  unif_index_add_time:                    0.
% 2.87/1.02  orderings_time:                         0.
% 2.87/1.02  out_proof_time:                         0.018
% 2.87/1.02  total_time:                             0.276
% 2.87/1.02  num_of_symbols:                         56
% 2.87/1.02  num_of_terms:                           6519
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing
% 2.87/1.02  
% 2.87/1.02  num_of_splits:                          0
% 2.87/1.02  num_of_split_atoms:                     0
% 2.87/1.02  num_of_reused_defs:                     0
% 2.87/1.02  num_eq_ax_congr_red:                    13
% 2.87/1.02  num_of_sem_filtered_clauses:            1
% 2.87/1.02  num_of_subtypes:                        0
% 2.87/1.02  monotx_restored_types:                  0
% 2.87/1.02  sat_num_of_epr_types:                   0
% 2.87/1.02  sat_num_of_non_cyclic_types:            0
% 2.87/1.02  sat_guarded_non_collapsed_types:        0
% 2.87/1.02  num_pure_diseq_elim:                    0
% 2.87/1.02  simp_replaced_by:                       0
% 2.87/1.02  res_preprocessed:                       186
% 2.87/1.02  prep_upred:                             0
% 2.87/1.02  prep_unflattend:                        64
% 2.87/1.02  smt_new_axioms:                         0
% 2.87/1.02  pred_elim_cands:                        8
% 2.87/1.02  pred_elim:                              3
% 2.87/1.02  pred_elim_cl:                           -3
% 2.87/1.02  pred_elim_cycles:                       4
% 2.87/1.02  merged_defs:                            0
% 2.87/1.02  merged_defs_ncl:                        0
% 2.87/1.02  bin_hyper_res:                          0
% 2.87/1.02  prep_cycles:                            3
% 2.87/1.02  pred_elim_time:                         0.014
% 2.87/1.02  splitting_time:                         0.
% 2.87/1.02  sem_filter_time:                        0.
% 2.87/1.02  monotx_time:                            0.
% 2.87/1.02  subtype_inf_time:                       0.
% 2.87/1.02  
% 2.87/1.02  ------ Problem properties
% 2.87/1.02  
% 2.87/1.02  clauses:                                50
% 2.87/1.02  conjectures:                            3
% 2.87/1.02  epr:                                    4
% 2.87/1.02  horn:                                   42
% 2.87/1.02  ground:                                 16
% 2.87/1.02  unary:                                  16
% 2.87/1.02  binary:                                 13
% 2.87/1.02  lits:                                   118
% 2.87/1.02  lits_eq:                                55
% 2.87/1.02  fd_pure:                                0
% 2.87/1.02  fd_pseudo:                              0
% 2.87/1.02  fd_cond:                                7
% 2.87/1.02  fd_pseudo_cond:                         1
% 2.87/1.02  ac_symbols:                             0
% 2.87/1.02  
% 2.87/1.02  ------ Propositional Solver
% 2.87/1.02  
% 2.87/1.02  prop_solver_calls:                      23
% 2.87/1.02  prop_fast_solver_calls:                 1298
% 2.87/1.02  smt_solver_calls:                       0
% 2.87/1.02  smt_fast_solver_calls:                  0
% 2.87/1.02  prop_num_of_clauses:                    2855
% 2.87/1.02  prop_preprocess_simplified:             8356
% 2.87/1.02  prop_fo_subsumed:                       35
% 2.87/1.02  prop_solver_time:                       0.
% 2.87/1.02  smt_solver_time:                        0.
% 2.87/1.02  smt_fast_solver_time:                   0.
% 2.87/1.02  prop_fast_solver_time:                  0.
% 2.87/1.02  prop_unsat_core_time:                   0.
% 2.87/1.02  
% 2.87/1.02  ------ QBF
% 2.87/1.02  
% 2.87/1.02  qbf_q_res:                              0
% 2.87/1.02  qbf_num_tautologies:                    0
% 2.87/1.02  qbf_prep_cycles:                        0
% 2.87/1.02  
% 2.87/1.02  ------ BMC1
% 2.87/1.02  
% 2.87/1.02  bmc1_current_bound:                     -1
% 2.87/1.02  bmc1_last_solved_bound:                 -1
% 2.87/1.02  bmc1_unsat_core_size:                   -1
% 2.87/1.02  bmc1_unsat_core_parents_size:           -1
% 2.87/1.02  bmc1_merge_next_fun:                    0
% 2.87/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.02  
% 2.87/1.02  ------ Instantiation
% 2.87/1.02  
% 2.87/1.02  inst_num_of_clauses:                    1008
% 2.87/1.02  inst_num_in_passive:                    121
% 2.87/1.02  inst_num_in_active:                     466
% 2.87/1.02  inst_num_in_unprocessed:                421
% 2.87/1.02  inst_num_of_loops:                      560
% 2.87/1.02  inst_num_of_learning_restarts:          0
% 2.87/1.02  inst_num_moves_active_passive:          92
% 2.87/1.02  inst_lit_activity:                      0
% 2.87/1.02  inst_lit_activity_moves:                0
% 2.87/1.02  inst_num_tautologies:                   0
% 2.87/1.02  inst_num_prop_implied:                  0
% 2.87/1.02  inst_num_existing_simplified:           0
% 2.87/1.02  inst_num_eq_res_simplified:             0
% 2.87/1.02  inst_num_child_elim:                    0
% 2.87/1.02  inst_num_of_dismatching_blockings:      318
% 2.87/1.02  inst_num_of_non_proper_insts:           851
% 2.87/1.02  inst_num_of_duplicates:                 0
% 2.87/1.02  inst_inst_num_from_inst_to_res:         0
% 2.87/1.02  inst_dismatching_checking_time:         0.
% 2.87/1.02  
% 2.87/1.02  ------ Resolution
% 2.87/1.02  
% 2.87/1.02  res_num_of_clauses:                     0
% 2.87/1.02  res_num_in_passive:                     0
% 2.87/1.02  res_num_in_active:                      0
% 2.87/1.02  res_num_of_loops:                       189
% 2.87/1.02  res_forward_subset_subsumed:            33
% 2.87/1.02  res_backward_subset_subsumed:           0
% 2.87/1.02  res_forward_subsumed:                   0
% 2.87/1.02  res_backward_subsumed:                  0
% 2.87/1.02  res_forward_subsumption_resolution:     6
% 2.87/1.02  res_backward_subsumption_resolution:    0
% 2.87/1.02  res_clause_to_clause_subsumption:       283
% 2.87/1.02  res_orphan_elimination:                 0
% 2.87/1.02  res_tautology_del:                      94
% 2.87/1.02  res_num_eq_res_simplified:              0
% 2.87/1.02  res_num_sel_changes:                    0
% 2.87/1.02  res_moves_from_active_to_pass:          0
% 2.87/1.02  
% 2.87/1.02  ------ Superposition
% 2.87/1.02  
% 2.87/1.02  sup_time_total:                         0.
% 2.87/1.02  sup_time_generating:                    0.
% 2.87/1.02  sup_time_sim_full:                      0.
% 2.87/1.02  sup_time_sim_immed:                     0.
% 2.87/1.02  
% 2.87/1.02  sup_num_of_clauses:                     119
% 2.87/1.02  sup_num_in_active:                      59
% 2.87/1.02  sup_num_in_passive:                     60
% 2.87/1.02  sup_num_of_loops:                       111
% 2.87/1.02  sup_fw_superposition:                   90
% 2.87/1.02  sup_bw_superposition:                   68
% 2.87/1.02  sup_immediate_simplified:               70
% 2.87/1.02  sup_given_eliminated:                   0
% 2.87/1.02  comparisons_done:                       0
% 2.87/1.02  comparisons_avoided:                    11
% 2.87/1.02  
% 2.87/1.02  ------ Simplifications
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  sim_fw_subset_subsumed:                 13
% 2.87/1.02  sim_bw_subset_subsumed:                 11
% 2.87/1.02  sim_fw_subsumed:                        13
% 2.87/1.02  sim_bw_subsumed:                        1
% 2.87/1.02  sim_fw_subsumption_res:                 2
% 2.87/1.02  sim_bw_subsumption_res:                 4
% 2.87/1.02  sim_tautology_del:                      6
% 2.87/1.02  sim_eq_tautology_del:                   19
% 2.87/1.02  sim_eq_res_simp:                        3
% 2.87/1.02  sim_fw_demodulated:                     21
% 2.87/1.02  sim_bw_demodulated:                     51
% 2.87/1.02  sim_light_normalised:                   62
% 2.87/1.02  sim_joinable_taut:                      0
% 2.87/1.02  sim_joinable_simp:                      0
% 2.87/1.02  sim_ac_normalised:                      0
% 2.87/1.02  sim_smt_subsumption:                    0
% 2.87/1.02  
%------------------------------------------------------------------------------
