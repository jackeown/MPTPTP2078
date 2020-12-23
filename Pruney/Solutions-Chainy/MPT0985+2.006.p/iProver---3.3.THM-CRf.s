%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:20 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  193 (5311 expanded)
%              Number of clauses        :  124 (1782 expanded)
%              Number of leaves         :   17 (1005 expanded)
%              Depth                    :   26
%              Number of atoms          :  551 (27578 expanded)
%              Number of equality atoms :  286 (5447 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f56,plain,
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

fof(f57,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f51,f56])).

fof(f98,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f101,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f108,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_43])).

cnf(c_807,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_809,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_42])).

cnf(c_1603,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1606,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4394,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1603,c_1606])).

cnf(c_4521,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_809,c_4394])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1607,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3172,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_1607])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_530,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_531,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_533,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_44])).

cnf(c_1596,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_3250,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3172,c_1596])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_544,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_41])).

cnf(c_545,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_547,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_545,c_44])).

cnf(c_1595,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_3251,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3172,c_1595])).

cnf(c_3254,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3250,c_3251])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5787,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3254,c_1604])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1605,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3707,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1603,c_1605])).

cnf(c_40,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3719,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3707,c_40])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_516,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_41])).

cnf(c_517,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_519,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_44])).

cnf(c_1597,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_3249,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3172,c_1597])).

cnf(c_3257,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3249,c_3251])).

cnf(c_3731,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3719,c_3257])).

cnf(c_5809,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5787,c_3731])).

cnf(c_45,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1960,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_2111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1610,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5050,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_1610])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1611,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5483,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_1611])).

cnf(c_6107,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5809,c_45,c_47,c_2111,c_5050,c_5483])).

cnf(c_6114,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_6107,c_1606])).

cnf(c_6121,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6114,c_3731])).

cnf(c_6147,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4521,c_6121])).

cnf(c_34,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_817,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_39])).

cnf(c_818,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_830,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_818,c_24])).

cnf(c_1584,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_835,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_1951,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1952,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_2176,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1584,c_45,c_47,c_835,c_1952,c_2111])).

cnf(c_2177,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2176])).

cnf(c_3363,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != sK1
    | k2_relat_1(k4_relat_1(sK2)) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3251,c_2177])).

cnf(c_3603,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3363,c_3254,c_3257])).

cnf(c_3730,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3719,c_3603])).

cnf(c_3737,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3730])).

cnf(c_4584,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4521,c_3737])).

cnf(c_6112,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4521,c_6107])).

cnf(c_6582,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6147,c_4584,c_6112])).

cnf(c_6588,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6582,c_6107])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_6708,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6588,c_4])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_39])).

cnf(c_708,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_1589,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_1846,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1589,c_4])).

cnf(c_2262,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1846,c_45,c_47,c_1952,c_2111])).

cnf(c_2263,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2262])).

cnf(c_3361,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3251,c_2263])).

cnf(c_6599,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6582,c_3361])).

cnf(c_6675,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6599])).

cnf(c_6679,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6675,c_4])).

cnf(c_6711,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6708,c_6679])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1619,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1613,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1618,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2799,plain,
    ( k4_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1613,c_1618])).

cnf(c_2824,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1619,c_2799])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1616,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5769,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_1616])).

cnf(c_6593,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6582,c_5769])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6694,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6593,c_3])).

cnf(c_133,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2084,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2085,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2084])).

cnf(c_2087,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_6613,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6582,c_1603])).

cnf(c_6618,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6613,c_3])).

cnf(c_7372,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6694,c_133,c_2087,c_6618])).

cnf(c_7390,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7372,c_1618])).

cnf(c_8103,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6711,c_2824,c_7390])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1617,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4393,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1617,c_1606])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4408,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4393,c_12])).

cnf(c_8104,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8103,c_4408])).

cnf(c_8105,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:47:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.36/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/0.98  
% 3.36/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.98  
% 3.36/0.98  ------  iProver source info
% 3.36/0.98  
% 3.36/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.98  git: non_committed_changes: false
% 3.36/0.98  git: last_make_outside_of_git: false
% 3.36/0.98  
% 3.36/0.98  ------ 
% 3.36/0.98  
% 3.36/0.98  ------ Input Options
% 3.36/0.98  
% 3.36/0.98  --out_options                           all
% 3.36/0.98  --tptp_safe_out                         true
% 3.36/0.98  --problem_path                          ""
% 3.36/0.98  --include_path                          ""
% 3.36/0.98  --clausifier                            res/vclausify_rel
% 3.36/0.98  --clausifier_options                    --mode clausify
% 3.36/0.98  --stdin                                 false
% 3.36/0.98  --stats_out                             all
% 3.36/0.98  
% 3.36/0.98  ------ General Options
% 3.36/0.98  
% 3.36/0.98  --fof                                   false
% 3.36/0.98  --time_out_real                         305.
% 3.36/0.98  --time_out_virtual                      -1.
% 3.36/0.98  --symbol_type_check                     false
% 3.36/0.98  --clausify_out                          false
% 3.36/0.98  --sig_cnt_out                           false
% 3.36/0.98  --trig_cnt_out                          false
% 3.36/0.98  --trig_cnt_out_tolerance                1.
% 3.36/0.98  --trig_cnt_out_sk_spl                   false
% 3.36/0.98  --abstr_cl_out                          false
% 3.36/0.98  
% 3.36/0.98  ------ Global Options
% 3.36/0.98  
% 3.36/0.98  --schedule                              default
% 3.36/0.98  --add_important_lit                     false
% 3.36/0.98  --prop_solver_per_cl                    1000
% 3.36/0.98  --min_unsat_core                        false
% 3.36/0.98  --soft_assumptions                      false
% 3.36/0.98  --soft_lemma_size                       3
% 3.36/0.98  --prop_impl_unit_size                   0
% 3.36/0.98  --prop_impl_unit                        []
% 3.36/0.98  --share_sel_clauses                     true
% 3.36/0.98  --reset_solvers                         false
% 3.36/0.98  --bc_imp_inh                            [conj_cone]
% 3.36/0.98  --conj_cone_tolerance                   3.
% 3.36/0.98  --extra_neg_conj                        none
% 3.36/0.98  --large_theory_mode                     true
% 3.36/0.98  --prolific_symb_bound                   200
% 3.36/0.98  --lt_threshold                          2000
% 3.36/0.98  --clause_weak_htbl                      true
% 3.36/0.98  --gc_record_bc_elim                     false
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing Options
% 3.36/0.98  
% 3.36/0.98  --preprocessing_flag                    true
% 3.36/0.98  --time_out_prep_mult                    0.1
% 3.36/0.98  --splitting_mode                        input
% 3.36/0.98  --splitting_grd                         true
% 3.36/0.98  --splitting_cvd                         false
% 3.36/0.98  --splitting_cvd_svl                     false
% 3.36/0.98  --splitting_nvd                         32
% 3.36/0.98  --sub_typing                            true
% 3.36/0.98  --prep_gs_sim                           true
% 3.36/0.98  --prep_unflatten                        true
% 3.36/0.98  --prep_res_sim                          true
% 3.36/0.98  --prep_upred                            true
% 3.36/0.98  --prep_sem_filter                       exhaustive
% 3.36/0.98  --prep_sem_filter_out                   false
% 3.36/0.98  --pred_elim                             true
% 3.36/0.98  --res_sim_input                         true
% 3.36/0.98  --eq_ax_congr_red                       true
% 3.36/0.98  --pure_diseq_elim                       true
% 3.36/0.98  --brand_transform                       false
% 3.36/0.98  --non_eq_to_eq                          false
% 3.36/0.98  --prep_def_merge                        true
% 3.36/0.98  --prep_def_merge_prop_impl              false
% 3.36/0.98  --prep_def_merge_mbd                    true
% 3.36/0.98  --prep_def_merge_tr_red                 false
% 3.36/0.98  --prep_def_merge_tr_cl                  false
% 3.36/0.98  --smt_preprocessing                     true
% 3.36/0.98  --smt_ac_axioms                         fast
% 3.36/0.98  --preprocessed_out                      false
% 3.36/0.98  --preprocessed_stats                    false
% 3.36/0.98  
% 3.36/0.98  ------ Abstraction refinement Options
% 3.36/0.98  
% 3.36/0.98  --abstr_ref                             []
% 3.36/0.98  --abstr_ref_prep                        false
% 3.36/0.98  --abstr_ref_until_sat                   false
% 3.36/0.98  --abstr_ref_sig_restrict                funpre
% 3.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.98  --abstr_ref_under                       []
% 3.36/0.98  
% 3.36/0.98  ------ SAT Options
% 3.36/0.98  
% 3.36/0.98  --sat_mode                              false
% 3.36/0.98  --sat_fm_restart_options                ""
% 3.36/0.98  --sat_gr_def                            false
% 3.36/0.98  --sat_epr_types                         true
% 3.36/0.98  --sat_non_cyclic_types                  false
% 3.36/0.98  --sat_finite_models                     false
% 3.36/0.98  --sat_fm_lemmas                         false
% 3.36/0.98  --sat_fm_prep                           false
% 3.36/0.98  --sat_fm_uc_incr                        true
% 3.36/0.98  --sat_out_model                         small
% 3.36/0.98  --sat_out_clauses                       false
% 3.36/0.98  
% 3.36/0.98  ------ QBF Options
% 3.36/0.98  
% 3.36/0.98  --qbf_mode                              false
% 3.36/0.98  --qbf_elim_univ                         false
% 3.36/0.98  --qbf_dom_inst                          none
% 3.36/0.98  --qbf_dom_pre_inst                      false
% 3.36/0.98  --qbf_sk_in                             false
% 3.36/0.98  --qbf_pred_elim                         true
% 3.36/0.98  --qbf_split                             512
% 3.36/0.98  
% 3.36/0.98  ------ BMC1 Options
% 3.36/0.98  
% 3.36/0.98  --bmc1_incremental                      false
% 3.36/0.98  --bmc1_axioms                           reachable_all
% 3.36/0.98  --bmc1_min_bound                        0
% 3.36/0.98  --bmc1_max_bound                        -1
% 3.36/0.98  --bmc1_max_bound_default                -1
% 3.36/0.98  --bmc1_symbol_reachability              true
% 3.36/0.98  --bmc1_property_lemmas                  false
% 3.36/0.98  --bmc1_k_induction                      false
% 3.36/0.98  --bmc1_non_equiv_states                 false
% 3.36/0.98  --bmc1_deadlock                         false
% 3.36/0.98  --bmc1_ucm                              false
% 3.36/0.98  --bmc1_add_unsat_core                   none
% 3.36/0.98  --bmc1_unsat_core_children              false
% 3.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.98  --bmc1_out_stat                         full
% 3.36/0.98  --bmc1_ground_init                      false
% 3.36/0.98  --bmc1_pre_inst_next_state              false
% 3.36/0.98  --bmc1_pre_inst_state                   false
% 3.36/0.98  --bmc1_pre_inst_reach_state             false
% 3.36/0.98  --bmc1_out_unsat_core                   false
% 3.36/0.98  --bmc1_aig_witness_out                  false
% 3.36/0.98  --bmc1_verbose                          false
% 3.36/0.98  --bmc1_dump_clauses_tptp                false
% 3.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.98  --bmc1_dump_file                        -
% 3.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.98  --bmc1_ucm_extend_mode                  1
% 3.36/0.98  --bmc1_ucm_init_mode                    2
% 3.36/0.98  --bmc1_ucm_cone_mode                    none
% 3.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.98  --bmc1_ucm_relax_model                  4
% 3.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.98  --bmc1_ucm_layered_model                none
% 3.36/0.98  --bmc1_ucm_max_lemma_size               10
% 3.36/0.98  
% 3.36/0.98  ------ AIG Options
% 3.36/0.98  
% 3.36/0.98  --aig_mode                              false
% 3.36/0.98  
% 3.36/0.98  ------ Instantiation Options
% 3.36/0.98  
% 3.36/0.98  --instantiation_flag                    true
% 3.36/0.98  --inst_sos_flag                         false
% 3.36/0.98  --inst_sos_phase                        true
% 3.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel_side                     num_symb
% 3.36/0.98  --inst_solver_per_active                1400
% 3.36/0.98  --inst_solver_calls_frac                1.
% 3.36/0.98  --inst_passive_queue_type               priority_queues
% 3.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.98  --inst_passive_queues_freq              [25;2]
% 3.36/0.98  --inst_dismatching                      true
% 3.36/0.98  --inst_eager_unprocessed_to_passive     true
% 3.36/0.98  --inst_prop_sim_given                   true
% 3.36/0.98  --inst_prop_sim_new                     false
% 3.36/0.98  --inst_subs_new                         false
% 3.36/0.98  --inst_eq_res_simp                      false
% 3.36/0.98  --inst_subs_given                       false
% 3.36/0.98  --inst_orphan_elimination               true
% 3.36/0.98  --inst_learning_loop_flag               true
% 3.36/0.98  --inst_learning_start                   3000
% 3.36/0.98  --inst_learning_factor                  2
% 3.36/0.98  --inst_start_prop_sim_after_learn       3
% 3.36/0.98  --inst_sel_renew                        solver
% 3.36/0.98  --inst_lit_activity_flag                true
% 3.36/0.98  --inst_restr_to_given                   false
% 3.36/0.98  --inst_activity_threshold               500
% 3.36/0.98  --inst_out_proof                        true
% 3.36/0.98  
% 3.36/0.98  ------ Resolution Options
% 3.36/0.98  
% 3.36/0.98  --resolution_flag                       true
% 3.36/0.98  --res_lit_sel                           adaptive
% 3.36/0.98  --res_lit_sel_side                      none
% 3.36/0.98  --res_ordering                          kbo
% 3.36/0.98  --res_to_prop_solver                    active
% 3.36/0.98  --res_prop_simpl_new                    false
% 3.36/0.98  --res_prop_simpl_given                  true
% 3.36/0.98  --res_passive_queue_type                priority_queues
% 3.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.98  --res_passive_queues_freq               [15;5]
% 3.36/0.98  --res_forward_subs                      full
% 3.36/0.98  --res_backward_subs                     full
% 3.36/0.98  --res_forward_subs_resolution           true
% 3.36/0.98  --res_backward_subs_resolution          true
% 3.36/0.98  --res_orphan_elimination                true
% 3.36/0.98  --res_time_limit                        2.
% 3.36/0.98  --res_out_proof                         true
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Options
% 3.36/0.98  
% 3.36/0.98  --superposition_flag                    true
% 3.36/0.98  --sup_passive_queue_type                priority_queues
% 3.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.98  --demod_completeness_check              fast
% 3.36/0.98  --demod_use_ground                      true
% 3.36/0.98  --sup_to_prop_solver                    passive
% 3.36/0.98  --sup_prop_simpl_new                    true
% 3.36/0.98  --sup_prop_simpl_given                  true
% 3.36/0.98  --sup_fun_splitting                     false
% 3.36/0.98  --sup_smt_interval                      50000
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Simplification Setup
% 3.36/0.98  
% 3.36/0.98  --sup_indices_passive                   []
% 3.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_full_bw                           [BwDemod]
% 3.36/0.98  --sup_immed_triv                        [TrivRules]
% 3.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_immed_bw_main                     []
% 3.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  
% 3.36/0.98  ------ Combination Options
% 3.36/0.98  
% 3.36/0.98  --comb_res_mult                         3
% 3.36/0.98  --comb_sup_mult                         2
% 3.36/0.98  --comb_inst_mult                        10
% 3.36/0.98  
% 3.36/0.98  ------ Debug Options
% 3.36/0.98  
% 3.36/0.98  --dbg_backtrace                         false
% 3.36/0.98  --dbg_dump_prop_clauses                 false
% 3.36/0.98  --dbg_dump_prop_clauses_file            -
% 3.36/0.98  --dbg_out_stat                          false
% 3.36/0.98  ------ Parsing...
% 3.36/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.98  ------ Proving...
% 3.36/0.98  ------ Problem Properties 
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  clauses                                 45
% 3.36/0.98  conjectures                             3
% 3.36/0.98  EPR                                     7
% 3.36/0.98  Horn                                    39
% 3.36/0.98  unary                                   11
% 3.36/0.98  binary                                  15
% 3.36/0.98  lits                                    116
% 3.36/0.98  lits eq                                 51
% 3.36/0.98  fd_pure                                 0
% 3.36/0.98  fd_pseudo                               0
% 3.36/0.98  fd_cond                                 4
% 3.36/0.98  fd_pseudo_cond                          0
% 3.36/0.98  AC symbols                              0
% 3.36/0.98  
% 3.36/0.98  ------ Schedule dynamic 5 is on 
% 3.36/0.98  
% 3.36/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  ------ 
% 3.36/0.98  Current options:
% 3.36/0.98  ------ 
% 3.36/0.98  
% 3.36/0.98  ------ Input Options
% 3.36/0.98  
% 3.36/0.98  --out_options                           all
% 3.36/0.98  --tptp_safe_out                         true
% 3.36/0.98  --problem_path                          ""
% 3.36/0.98  --include_path                          ""
% 3.36/0.98  --clausifier                            res/vclausify_rel
% 3.36/0.98  --clausifier_options                    --mode clausify
% 3.36/0.98  --stdin                                 false
% 3.36/0.98  --stats_out                             all
% 3.36/0.98  
% 3.36/0.98  ------ General Options
% 3.36/0.98  
% 3.36/0.98  --fof                                   false
% 3.36/0.98  --time_out_real                         305.
% 3.36/0.98  --time_out_virtual                      -1.
% 3.36/0.98  --symbol_type_check                     false
% 3.36/0.98  --clausify_out                          false
% 3.36/0.98  --sig_cnt_out                           false
% 3.36/0.98  --trig_cnt_out                          false
% 3.36/0.98  --trig_cnt_out_tolerance                1.
% 3.36/0.98  --trig_cnt_out_sk_spl                   false
% 3.36/0.98  --abstr_cl_out                          false
% 3.36/0.98  
% 3.36/0.98  ------ Global Options
% 3.36/0.98  
% 3.36/0.98  --schedule                              default
% 3.36/0.98  --add_important_lit                     false
% 3.36/0.98  --prop_solver_per_cl                    1000
% 3.36/0.98  --min_unsat_core                        false
% 3.36/0.98  --soft_assumptions                      false
% 3.36/0.98  --soft_lemma_size                       3
% 3.36/0.98  --prop_impl_unit_size                   0
% 3.36/0.98  --prop_impl_unit                        []
% 3.36/0.98  --share_sel_clauses                     true
% 3.36/0.98  --reset_solvers                         false
% 3.36/0.98  --bc_imp_inh                            [conj_cone]
% 3.36/0.98  --conj_cone_tolerance                   3.
% 3.36/0.98  --extra_neg_conj                        none
% 3.36/0.98  --large_theory_mode                     true
% 3.36/0.98  --prolific_symb_bound                   200
% 3.36/0.98  --lt_threshold                          2000
% 3.36/0.98  --clause_weak_htbl                      true
% 3.36/0.98  --gc_record_bc_elim                     false
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing Options
% 3.36/0.98  
% 3.36/0.98  --preprocessing_flag                    true
% 3.36/0.98  --time_out_prep_mult                    0.1
% 3.36/0.98  --splitting_mode                        input
% 3.36/0.98  --splitting_grd                         true
% 3.36/0.98  --splitting_cvd                         false
% 3.36/0.98  --splitting_cvd_svl                     false
% 3.36/0.98  --splitting_nvd                         32
% 3.36/0.98  --sub_typing                            true
% 3.36/0.98  --prep_gs_sim                           true
% 3.36/0.98  --prep_unflatten                        true
% 3.36/0.98  --prep_res_sim                          true
% 3.36/0.98  --prep_upred                            true
% 3.36/0.98  --prep_sem_filter                       exhaustive
% 3.36/0.98  --prep_sem_filter_out                   false
% 3.36/0.98  --pred_elim                             true
% 3.36/0.98  --res_sim_input                         true
% 3.36/0.98  --eq_ax_congr_red                       true
% 3.36/0.98  --pure_diseq_elim                       true
% 3.36/0.98  --brand_transform                       false
% 3.36/0.98  --non_eq_to_eq                          false
% 3.36/0.98  --prep_def_merge                        true
% 3.36/0.98  --prep_def_merge_prop_impl              false
% 3.36/0.98  --prep_def_merge_mbd                    true
% 3.36/0.98  --prep_def_merge_tr_red                 false
% 3.36/0.98  --prep_def_merge_tr_cl                  false
% 3.36/0.98  --smt_preprocessing                     true
% 3.36/0.98  --smt_ac_axioms                         fast
% 3.36/0.98  --preprocessed_out                      false
% 3.36/0.98  --preprocessed_stats                    false
% 3.36/0.98  
% 3.36/0.98  ------ Abstraction refinement Options
% 3.36/0.98  
% 3.36/0.98  --abstr_ref                             []
% 3.36/0.98  --abstr_ref_prep                        false
% 3.36/0.98  --abstr_ref_until_sat                   false
% 3.36/0.98  --abstr_ref_sig_restrict                funpre
% 3.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.98  --abstr_ref_under                       []
% 3.36/0.98  
% 3.36/0.98  ------ SAT Options
% 3.36/0.98  
% 3.36/0.98  --sat_mode                              false
% 3.36/0.98  --sat_fm_restart_options                ""
% 3.36/0.98  --sat_gr_def                            false
% 3.36/0.98  --sat_epr_types                         true
% 3.36/0.98  --sat_non_cyclic_types                  false
% 3.36/0.98  --sat_finite_models                     false
% 3.36/0.98  --sat_fm_lemmas                         false
% 3.36/0.98  --sat_fm_prep                           false
% 3.36/0.98  --sat_fm_uc_incr                        true
% 3.36/0.98  --sat_out_model                         small
% 3.36/0.98  --sat_out_clauses                       false
% 3.36/0.98  
% 3.36/0.98  ------ QBF Options
% 3.36/0.98  
% 3.36/0.98  --qbf_mode                              false
% 3.36/0.98  --qbf_elim_univ                         false
% 3.36/0.98  --qbf_dom_inst                          none
% 3.36/0.98  --qbf_dom_pre_inst                      false
% 3.36/0.98  --qbf_sk_in                             false
% 3.36/0.98  --qbf_pred_elim                         true
% 3.36/0.98  --qbf_split                             512
% 3.36/0.98  
% 3.36/0.98  ------ BMC1 Options
% 3.36/0.98  
% 3.36/0.98  --bmc1_incremental                      false
% 3.36/0.98  --bmc1_axioms                           reachable_all
% 3.36/0.98  --bmc1_min_bound                        0
% 3.36/0.98  --bmc1_max_bound                        -1
% 3.36/0.98  --bmc1_max_bound_default                -1
% 3.36/0.98  --bmc1_symbol_reachability              true
% 3.36/0.98  --bmc1_property_lemmas                  false
% 3.36/0.98  --bmc1_k_induction                      false
% 3.36/0.98  --bmc1_non_equiv_states                 false
% 3.36/0.98  --bmc1_deadlock                         false
% 3.36/0.98  --bmc1_ucm                              false
% 3.36/0.98  --bmc1_add_unsat_core                   none
% 3.36/0.98  --bmc1_unsat_core_children              false
% 3.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.98  --bmc1_out_stat                         full
% 3.36/0.98  --bmc1_ground_init                      false
% 3.36/0.98  --bmc1_pre_inst_next_state              false
% 3.36/0.98  --bmc1_pre_inst_state                   false
% 3.36/0.98  --bmc1_pre_inst_reach_state             false
% 3.36/0.98  --bmc1_out_unsat_core                   false
% 3.36/0.98  --bmc1_aig_witness_out                  false
% 3.36/0.98  --bmc1_verbose                          false
% 3.36/0.98  --bmc1_dump_clauses_tptp                false
% 3.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.98  --bmc1_dump_file                        -
% 3.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.98  --bmc1_ucm_extend_mode                  1
% 3.36/0.98  --bmc1_ucm_init_mode                    2
% 3.36/0.98  --bmc1_ucm_cone_mode                    none
% 3.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.98  --bmc1_ucm_relax_model                  4
% 3.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.98  --bmc1_ucm_layered_model                none
% 3.36/0.98  --bmc1_ucm_max_lemma_size               10
% 3.36/0.98  
% 3.36/0.98  ------ AIG Options
% 3.36/0.98  
% 3.36/0.98  --aig_mode                              false
% 3.36/0.98  
% 3.36/0.98  ------ Instantiation Options
% 3.36/0.98  
% 3.36/0.98  --instantiation_flag                    true
% 3.36/0.98  --inst_sos_flag                         false
% 3.36/0.98  --inst_sos_phase                        true
% 3.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel_side                     none
% 3.36/0.98  --inst_solver_per_active                1400
% 3.36/0.98  --inst_solver_calls_frac                1.
% 3.36/0.98  --inst_passive_queue_type               priority_queues
% 3.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.98  --inst_passive_queues_freq              [25;2]
% 3.36/0.98  --inst_dismatching                      true
% 3.36/0.98  --inst_eager_unprocessed_to_passive     true
% 3.36/0.98  --inst_prop_sim_given                   true
% 3.36/0.98  --inst_prop_sim_new                     false
% 3.36/0.98  --inst_subs_new                         false
% 3.36/0.98  --inst_eq_res_simp                      false
% 3.36/0.98  --inst_subs_given                       false
% 3.36/0.98  --inst_orphan_elimination               true
% 3.36/0.98  --inst_learning_loop_flag               true
% 3.36/0.98  --inst_learning_start                   3000
% 3.36/0.98  --inst_learning_factor                  2
% 3.36/0.98  --inst_start_prop_sim_after_learn       3
% 3.36/0.98  --inst_sel_renew                        solver
% 3.36/0.98  --inst_lit_activity_flag                true
% 3.36/0.98  --inst_restr_to_given                   false
% 3.36/0.98  --inst_activity_threshold               500
% 3.36/0.98  --inst_out_proof                        true
% 3.36/0.98  
% 3.36/0.98  ------ Resolution Options
% 3.36/0.98  
% 3.36/0.98  --resolution_flag                       false
% 3.36/0.98  --res_lit_sel                           adaptive
% 3.36/0.98  --res_lit_sel_side                      none
% 3.36/0.98  --res_ordering                          kbo
% 3.36/0.98  --res_to_prop_solver                    active
% 3.36/0.98  --res_prop_simpl_new                    false
% 3.36/0.98  --res_prop_simpl_given                  true
% 3.36/0.98  --res_passive_queue_type                priority_queues
% 3.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.98  --res_passive_queues_freq               [15;5]
% 3.36/0.98  --res_forward_subs                      full
% 3.36/0.98  --res_backward_subs                     full
% 3.36/0.98  --res_forward_subs_resolution           true
% 3.36/0.98  --res_backward_subs_resolution          true
% 3.36/0.98  --res_orphan_elimination                true
% 3.36/0.98  --res_time_limit                        2.
% 3.36/0.98  --res_out_proof                         true
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Options
% 3.36/0.98  
% 3.36/0.98  --superposition_flag                    true
% 3.36/0.98  --sup_passive_queue_type                priority_queues
% 3.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.98  --demod_completeness_check              fast
% 3.36/0.98  --demod_use_ground                      true
% 3.36/0.98  --sup_to_prop_solver                    passive
% 3.36/0.98  --sup_prop_simpl_new                    true
% 3.36/0.98  --sup_prop_simpl_given                  true
% 3.36/0.98  --sup_fun_splitting                     false
% 3.36/0.98  --sup_smt_interval                      50000
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Simplification Setup
% 3.36/0.98  
% 3.36/0.98  --sup_indices_passive                   []
% 3.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_full_bw                           [BwDemod]
% 3.36/0.98  --sup_immed_triv                        [TrivRules]
% 3.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_immed_bw_main                     []
% 3.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  
% 3.36/0.98  ------ Combination Options
% 3.36/0.98  
% 3.36/0.98  --comb_res_mult                         3
% 3.36/0.98  --comb_sup_mult                         2
% 3.36/0.98  --comb_inst_mult                        10
% 3.36/0.98  
% 3.36/0.98  ------ Debug Options
% 3.36/0.98  
% 3.36/0.98  --dbg_backtrace                         false
% 3.36/0.98  --dbg_dump_prop_clauses                 false
% 3.36/0.98  --dbg_dump_prop_clauses_file            -
% 3.36/0.98  --dbg_out_stat                          false
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  ------ Proving...
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  % SZS status Theorem for theBenchmark.p
% 3.36/0.98  
% 3.36/0.98   Resolution empty clause
% 3.36/0.98  
% 3.36/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/0.98  
% 3.36/0.98  fof(f20,axiom,(
% 3.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f44,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/0.98    inference(ennf_transformation,[],[f20])).
% 3.36/0.98  
% 3.36/0.98  fof(f45,plain,(
% 3.36/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/0.98    inference(flattening,[],[f44])).
% 3.36/0.98  
% 3.36/0.98  fof(f55,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/0.98    inference(nnf_transformation,[],[f45])).
% 3.36/0.98  
% 3.36/0.98  fof(f85,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f55])).
% 3.36/0.98  
% 3.36/0.98  fof(f23,conjecture,(
% 3.36/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f24,negated_conjecture,(
% 3.36/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.36/0.98    inference(negated_conjecture,[],[f23])).
% 3.36/0.98  
% 3.36/0.98  fof(f50,plain,(
% 3.36/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.36/0.98    inference(ennf_transformation,[],[f24])).
% 3.36/0.98  
% 3.36/0.98  fof(f51,plain,(
% 3.36/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.36/0.98    inference(flattening,[],[f50])).
% 3.36/0.98  
% 3.36/0.98  fof(f56,plain,(
% 3.36/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.36/0.98    introduced(choice_axiom,[])).
% 3.36/0.98  
% 3.36/0.98  fof(f57,plain,(
% 3.36/0.98    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.36/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f51,f56])).
% 3.36/0.98  
% 3.36/0.98  fof(f98,plain,(
% 3.36/0.98    v1_funct_2(sK2,sK0,sK1)),
% 3.36/0.98    inference(cnf_transformation,[],[f57])).
% 3.36/0.98  
% 3.36/0.98  fof(f99,plain,(
% 3.36/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.36/0.98    inference(cnf_transformation,[],[f57])).
% 3.36/0.98  
% 3.36/0.98  fof(f18,axiom,(
% 3.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f42,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/0.98    inference(ennf_transformation,[],[f18])).
% 3.36/0.98  
% 3.36/0.98  fof(f83,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f42])).
% 3.36/0.98  
% 3.36/0.98  fof(f17,axiom,(
% 3.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f41,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/0.98    inference(ennf_transformation,[],[f17])).
% 3.36/0.98  
% 3.36/0.98  fof(f82,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f41])).
% 3.36/0.98  
% 3.36/0.98  fof(f15,axiom,(
% 3.36/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f39,plain,(
% 3.36/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.36/0.98    inference(ennf_transformation,[],[f15])).
% 3.36/0.98  
% 3.36/0.98  fof(f40,plain,(
% 3.36/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.36/0.98    inference(flattening,[],[f39])).
% 3.36/0.98  
% 3.36/0.98  fof(f79,plain,(
% 3.36/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f40])).
% 3.36/0.98  
% 3.36/0.98  fof(f100,plain,(
% 3.36/0.98    v2_funct_1(sK2)),
% 3.36/0.98    inference(cnf_transformation,[],[f57])).
% 3.36/0.98  
% 3.36/0.98  fof(f97,plain,(
% 3.36/0.98    v1_funct_1(sK2)),
% 3.36/0.98    inference(cnf_transformation,[],[f57])).
% 3.36/0.98  
% 3.36/0.98  fof(f13,axiom,(
% 3.36/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f35,plain,(
% 3.36/0.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.36/0.98    inference(ennf_transformation,[],[f13])).
% 3.36/0.98  
% 3.36/0.98  fof(f36,plain,(
% 3.36/0.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.36/0.98    inference(flattening,[],[f35])).
% 3.36/0.98  
% 3.36/0.98  fof(f75,plain,(
% 3.36/0.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f36])).
% 3.36/0.98  
% 3.36/0.98  fof(f21,axiom,(
% 3.36/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f46,plain,(
% 3.36/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.36/0.98    inference(ennf_transformation,[],[f21])).
% 3.36/0.98  
% 3.36/0.98  fof(f47,plain,(
% 3.36/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.36/0.98    inference(flattening,[],[f46])).
% 3.36/0.98  
% 3.36/0.98  fof(f93,plain,(
% 3.36/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f47])).
% 3.36/0.98  
% 3.36/0.98  fof(f19,axiom,(
% 3.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f43,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/0.98    inference(ennf_transformation,[],[f19])).
% 3.36/0.98  
% 3.36/0.98  fof(f84,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f43])).
% 3.36/0.98  
% 3.36/0.98  fof(f101,plain,(
% 3.36/0.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.36/0.98    inference(cnf_transformation,[],[f57])).
% 3.36/0.98  
% 3.36/0.98  fof(f78,plain,(
% 3.36/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f40])).
% 3.36/0.98  
% 3.36/0.98  fof(f14,axiom,(
% 3.36/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f37,plain,(
% 3.36/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.36/0.98    inference(ennf_transformation,[],[f14])).
% 3.36/0.98  
% 3.36/0.98  fof(f38,plain,(
% 3.36/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.36/0.98    inference(flattening,[],[f37])).
% 3.36/0.98  
% 3.36/0.98  fof(f76,plain,(
% 3.36/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f38])).
% 3.36/0.98  
% 3.36/0.98  fof(f77,plain,(
% 3.36/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f38])).
% 3.36/0.98  
% 3.36/0.98  fof(f92,plain,(
% 3.36/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f47])).
% 3.36/0.98  
% 3.36/0.98  fof(f102,plain,(
% 3.36/0.98    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.36/0.98    inference(cnf_transformation,[],[f57])).
% 3.36/0.98  
% 3.36/0.98  fof(f4,axiom,(
% 3.36/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f52,plain,(
% 3.36/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/0.98    inference(nnf_transformation,[],[f4])).
% 3.36/0.98  
% 3.36/0.98  fof(f53,plain,(
% 3.36/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/0.98    inference(flattening,[],[f52])).
% 3.36/0.98  
% 3.36/0.98  fof(f62,plain,(
% 3.36/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.36/0.98    inference(cnf_transformation,[],[f53])).
% 3.36/0.98  
% 3.36/0.98  fof(f104,plain,(
% 3.36/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.36/0.98    inference(equality_resolution,[],[f62])).
% 3.36/0.98  
% 3.36/0.98  fof(f88,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f55])).
% 3.36/0.98  
% 3.36/0.98  fof(f108,plain,(
% 3.36/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.36/0.98    inference(equality_resolution,[],[f88])).
% 3.36/0.98  
% 3.36/0.98  fof(f1,axiom,(
% 3.36/0.98    v1_xboole_0(k1_xboole_0)),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f58,plain,(
% 3.36/0.98    v1_xboole_0(k1_xboole_0)),
% 3.36/0.98    inference(cnf_transformation,[],[f1])).
% 3.36/0.98  
% 3.36/0.98  fof(f9,axiom,(
% 3.36/0.98    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f31,plain,(
% 3.36/0.98    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 3.36/0.98    inference(ennf_transformation,[],[f9])).
% 3.36/0.98  
% 3.36/0.98  fof(f67,plain,(
% 3.36/0.98    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f31])).
% 3.36/0.98  
% 3.36/0.98  fof(f2,axiom,(
% 3.36/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f28,plain,(
% 3.36/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.36/0.98    inference(ennf_transformation,[],[f2])).
% 3.36/0.98  
% 3.36/0.98  fof(f59,plain,(
% 3.36/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f28])).
% 3.36/0.98  
% 3.36/0.98  fof(f6,axiom,(
% 3.36/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f29,plain,(
% 3.36/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.36/0.98    inference(ennf_transformation,[],[f6])).
% 3.36/0.98  
% 3.36/0.98  fof(f65,plain,(
% 3.36/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f29])).
% 3.36/0.98  
% 3.36/0.98  fof(f63,plain,(
% 3.36/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.36/0.98    inference(cnf_transformation,[],[f53])).
% 3.36/0.98  
% 3.36/0.98  fof(f103,plain,(
% 3.36/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.36/0.98    inference(equality_resolution,[],[f63])).
% 3.36/0.98  
% 3.36/0.98  fof(f5,axiom,(
% 3.36/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f64,plain,(
% 3.36/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f5])).
% 3.36/0.98  
% 3.36/0.98  fof(f10,axiom,(
% 3.36/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.36/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f69,plain,(
% 3.36/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.36/0.98    inference(cnf_transformation,[],[f10])).
% 3.36/0.98  
% 3.36/0.98  cnf(c_32,plain,
% 3.36/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.36/0.98      | k1_xboole_0 = X2 ),
% 3.36/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_43,negated_conjecture,
% 3.36/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.36/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_806,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.36/0.98      | sK0 != X1
% 3.36/0.98      | sK1 != X2
% 3.36/0.98      | sK2 != X0
% 3.36/0.98      | k1_xboole_0 = X2 ),
% 3.36/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_43]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_807,plain,
% 3.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.36/0.98      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.36/0.98      | k1_xboole_0 = sK1 ),
% 3.36/0.98      inference(unflattening,[status(thm)],[c_806]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_42,negated_conjecture,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.36/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_809,plain,
% 3.36/0.98      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.36/0.98      inference(global_propositional_subsumption,[status(thm)],[c_807,c_42]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1603,plain,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_25,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1606,plain,
% 3.36/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.36/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4394,plain,
% 3.36/0.98      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1603,c_1606]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4521,plain,
% 3.36/0.98      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_809,c_4394]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_24,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1607,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3172,plain,
% 3.36/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1603,c_1607]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_20,plain,
% 3.36/0.98      ( ~ v2_funct_1(X0)
% 3.36/0.98      | ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0)
% 3.36/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_41,negated_conjecture,
% 3.36/0.98      ( v2_funct_1(sK2) ),
% 3.36/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_530,plain,
% 3.36/0.98      ( ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0)
% 3.36/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.36/0.98      | sK2 != X0 ),
% 3.36/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_41]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_531,plain,
% 3.36/0.98      ( ~ v1_funct_1(sK2)
% 3.36/0.98      | ~ v1_relat_1(sK2)
% 3.36/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.36/0.98      inference(unflattening,[status(thm)],[c_530]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_44,negated_conjecture,
% 3.36/0.98      ( v1_funct_1(sK2) ),
% 3.36/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_533,plain,
% 3.36/0.98      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.36/0.98      inference(global_propositional_subsumption,[status(thm)],[c_531,c_44]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1596,plain,
% 3.36/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.36/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3250,plain,
% 3.36/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_3172,c_1596]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_17,plain,
% 3.36/0.98      ( ~ v2_funct_1(X0)
% 3.36/0.98      | ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0)
% 3.36/0.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_544,plain,
% 3.36/0.98      ( ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0)
% 3.36/0.98      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.36/0.98      | sK2 != X0 ),
% 3.36/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_41]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_545,plain,
% 3.36/0.98      ( ~ v1_funct_1(sK2)
% 3.36/0.98      | ~ v1_relat_1(sK2)
% 3.36/0.98      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.36/0.98      inference(unflattening,[status(thm)],[c_544]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_547,plain,
% 3.36/0.98      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.36/0.98      inference(global_propositional_subsumption,[status(thm)],[c_545,c_44]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1595,plain,
% 3.36/0.98      ( k2_funct_1(sK2) = k4_relat_1(sK2) | v1_relat_1(sK2) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3251,plain,
% 3.36/0.98      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_3172,c_1595]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3254,plain,
% 3.36/0.98      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_3250,c_3251]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_33,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.36/0.98      | ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1604,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.36/0.98      | v1_funct_1(X0) != iProver_top
% 3.36/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_5787,plain,
% 3.36/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.36/0.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.36/0.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_3254,c_1604]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_26,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1605,plain,
% 3.36/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.36/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3707,plain,
% 3.36/0.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1603,c_1605]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_40,negated_conjecture,
% 3.36/0.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.36/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3719,plain,
% 3.36/0.98      ( k2_relat_1(sK2) = sK1 ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_3707,c_40]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_21,plain,
% 3.36/0.98      ( ~ v2_funct_1(X0)
% 3.36/0.98      | ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0)
% 3.36/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_516,plain,
% 3.36/0.98      ( ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0)
% 3.36/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.36/0.98      | sK2 != X0 ),
% 3.36/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_41]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_517,plain,
% 3.36/0.98      ( ~ v1_funct_1(sK2)
% 3.36/0.98      | ~ v1_relat_1(sK2)
% 3.36/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.36/0.98      inference(unflattening,[status(thm)],[c_516]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_519,plain,
% 3.36/0.98      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.36/0.98      inference(global_propositional_subsumption,[status(thm)],[c_517,c_44]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1597,plain,
% 3.36/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.36/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3249,plain,
% 3.36/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_3172,c_1597]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3257,plain,
% 3.36/0.98      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_3249,c_3251]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3731,plain,
% 3.36/0.98      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_3719,c_3257]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_5809,plain,
% 3.36/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.36/0.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.36/0.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_5787,c_3731]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_45,plain,
% 3.36/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_47,plain,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1960,plain,
% 3.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK2) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2110,plain,
% 3.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.36/0.98      | v1_relat_1(sK2) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_1960]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2111,plain,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.36/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_19,plain,
% 3.36/0.98      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.36/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1610,plain,
% 3.36/0.98      ( v1_funct_1(X0) != iProver_top
% 3.36/0.98      | v1_relat_1(X0) != iProver_top
% 3.36/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_5050,plain,
% 3.36/0.98      ( v1_funct_1(sK2) != iProver_top
% 3.36/0.98      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 3.36/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_3251,c_1610]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_18,plain,
% 3.36/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1611,plain,
% 3.36/0.98      ( v1_funct_1(X0) != iProver_top
% 3.36/0.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.36/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_5483,plain,
% 3.36/0.98      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.36/0.98      | v1_funct_1(sK2) != iProver_top
% 3.36/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_3251,c_1611]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6107,plain,
% 3.36/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.36/0.98      inference(global_propositional_subsumption,
% 3.36/0.98                [status(thm)],
% 3.36/0.98                [c_5809,c_45,c_47,c_2111,c_5050,c_5483]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6114,plain,
% 3.36/0.98      ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_6107,c_1606]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6121,plain,
% 3.36/0.98      ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_6114,c_3731]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6147,plain,
% 3.36/0.98      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_4521,c_6121]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_34,plain,
% 3.36/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.36/0.98      | ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_relat_1(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_39,negated_conjecture,
% 3.36/0.98      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.36/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.36/0.98      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.36/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_817,plain,
% 3.36/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.36/0.98      | ~ v1_funct_1(X0)
% 3.36/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.36/0.98      | ~ v1_relat_1(X0)
% 3.36/0.98      | k2_funct_1(sK2) != X0
% 3.36/0.98      | k1_relat_1(X0) != sK1
% 3.36/0.98      | k2_relat_1(X0) != sK0 ),
% 3.36/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_39]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_818,plain,
% 3.36/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.36/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.36/0.98      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.36/0.98      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.36/0.98      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.36/0.98      inference(unflattening,[status(thm)],[c_817]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_830,plain,
% 3.36/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.36/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.36/0.98      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.36/0.98      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.36/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_818,c_24]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1584,plain,
% 3.36/0.98      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.36/0.98      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_835,plain,
% 3.36/0.98      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.36/0.98      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1951,plain,
% 3.36/0.98      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1952,plain,
% 3.36/0.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.36/0.98      | v1_funct_1(sK2) != iProver_top
% 3.36/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2176,plain,
% 3.36/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.36/0.98      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.36/0.98      inference(global_propositional_subsumption,
% 3.36/0.98                [status(thm)],
% 3.36/0.98                [c_1584,c_45,c_47,c_835,c_1952,c_2111]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2177,plain,
% 3.36/0.98      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.36/0.98      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.36/0.98      inference(renaming,[status(thm)],[c_2176]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3363,plain,
% 3.36/0.98      ( k1_relat_1(k4_relat_1(sK2)) != sK1
% 3.36/0.98      | k2_relat_1(k4_relat_1(sK2)) != sK0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_3251,c_2177]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3603,plain,
% 3.36/0.98      ( k1_relat_1(sK2) != sK0
% 3.36/0.98      | k2_relat_1(sK2) != sK1
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_3363,c_3254,c_3257]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3730,plain,
% 3.36/0.98      ( k1_relat_1(sK2) != sK0
% 3.36/0.98      | sK1 != sK1
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_3719,c_3603]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3737,plain,
% 3.36/0.98      ( k1_relat_1(sK2) != sK0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.36/0.98      inference(equality_resolution_simp,[status(thm)],[c_3730]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4584,plain,
% 3.36/0.98      ( sK1 = k1_xboole_0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_4521,c_3737]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6112,plain,
% 3.36/0.98      ( sK1 = k1_xboole_0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_4521,c_6107]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6582,plain,
% 3.36/0.98      ( sK1 = k1_xboole_0 ),
% 3.36/0.98      inference(global_propositional_subsumption,
% 3.36/0.98                [status(thm)],
% 3.36/0.98                [c_6147,c_4584,c_6112]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6588,plain,
% 3.36/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6582,c_6107]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4,plain,
% 3.36/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6708,plain,
% 3.36/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6588,c_4]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_29,plain,
% 3.36/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.36/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.36/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_707,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.36/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.36/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.36/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.36/0.98      | k2_funct_1(sK2) != X0
% 3.36/0.98      | sK0 != X1
% 3.36/0.98      | sK1 != k1_xboole_0 ),
% 3.36/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_39]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_708,plain,
% 3.36/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.36/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.36/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.36/0.98      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.36/0.98      | sK1 != k1_xboole_0 ),
% 3.36/0.98      inference(unflattening,[status(thm)],[c_707]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1589,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.36/0.98      | sK1 != k1_xboole_0
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.36/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1846,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.36/0.98      | sK1 != k1_xboole_0
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.36/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_1589,c_4]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2262,plain,
% 3.36/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | sK1 != k1_xboole_0
% 3.36/0.98      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.36/0.98      inference(global_propositional_subsumption,
% 3.36/0.98                [status(thm)],
% 3.36/0.98                [c_1846,c_45,c_47,c_1952,c_2111]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2263,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.36/0.98      | sK1 != k1_xboole_0
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/0.98      inference(renaming,[status(thm)],[c_2262]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3361,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 3.36/0.98      | sK1 != k1_xboole_0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_3251,c_2263]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6599,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 3.36/0.98      | k1_xboole_0 != k1_xboole_0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6582,c_3361]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6675,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/0.98      inference(equality_resolution_simp,[status(thm)],[c_6599]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6679,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 3.36/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6675,c_4]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6711,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0 ),
% 3.36/0.98      inference(backward_subsumption_resolution,[status(thm)],[c_6708,c_6679]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_0,plain,
% 3.36/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1619,plain,
% 3.36/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_10,plain,
% 3.36/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0)) ),
% 3.36/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1613,plain,
% 3.36/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.36/0.98      | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1,plain,
% 3.36/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.36/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1618,plain,
% 3.36/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2799,plain,
% 3.36/0.98      ( k4_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1613,c_1618]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2824,plain,
% 3.36/0.98      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1619,c_2799]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_7,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.36/0.98      | ~ v1_xboole_0(X1)
% 3.36/0.98      | v1_xboole_0(X0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1616,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.36/0.98      | v1_xboole_0(X1) != iProver_top
% 3.36/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_5769,plain,
% 3.36/0.98      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.36/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1603,c_1616]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6593,plain,
% 3.36/0.98      ( v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) != iProver_top
% 3.36/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6582,c_5769]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3,plain,
% 3.36/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6694,plain,
% 3.36/0.98      ( v1_xboole_0(sK2) = iProver_top
% 3.36/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6593,c_3]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_133,plain,
% 3.36/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2084,plain,
% 3.36/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.36/0.98      | ~ v1_xboole_0(X0)
% 3.36/0.98      | v1_xboole_0(sK2) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2085,plain,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.36/0.98      | v1_xboole_0(X0) != iProver_top
% 3.36/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_2084]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2087,plain,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.36/0.98      | v1_xboole_0(sK2) = iProver_top
% 3.36/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_2085]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6613,plain,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6582,c_1603]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6618,plain,
% 3.36/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_6613,c_3]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_7372,plain,
% 3.36/0.98      ( v1_xboole_0(sK2) = iProver_top ),
% 3.36/0.98      inference(global_propositional_subsumption,
% 3.36/0.98                [status(thm)],
% 3.36/0.98                [c_6694,c_133,c_2087,c_6618]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_7390,plain,
% 3.36/0.98      ( sK2 = k1_xboole_0 ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_7372,c_1618]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8103,plain,
% 3.36/0.98      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_6711,c_2824,c_7390]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6,plain,
% 3.36/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.36/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1617,plain,
% 3.36/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4393,plain,
% 3.36/0.98      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1617,c_1606]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_12,plain,
% 3.36/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4408,plain,
% 3.36/0.98      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.98      inference(light_normalisation,[status(thm)],[c_4393,c_12]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8104,plain,
% 3.36/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_8103,c_4408]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8105,plain,
% 3.36/0.98      ( $false ),
% 3.36/0.98      inference(equality_resolution_simp,[status(thm)],[c_8104]) ).
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/0.98  
% 3.36/0.98  ------                               Statistics
% 3.36/0.98  
% 3.36/0.98  ------ General
% 3.36/0.98  
% 3.36/0.98  abstr_ref_over_cycles:                  0
% 3.36/0.98  abstr_ref_under_cycles:                 0
% 3.36/0.98  gc_basic_clause_elim:                   0
% 3.36/0.98  forced_gc_time:                         0
% 3.36/0.98  parsing_time:                           0.013
% 3.36/0.98  unif_index_cands_time:                  0.
% 3.36/0.98  unif_index_add_time:                    0.
% 3.36/0.98  orderings_time:                         0.
% 3.36/0.98  out_proof_time:                         0.01
% 3.36/0.98  total_time:                             0.312
% 3.36/0.98  num_of_symbols:                         50
% 3.36/0.98  num_of_terms:                           6503
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing
% 3.36/0.98  
% 3.36/0.98  num_of_splits:                          0
% 3.36/0.98  num_of_split_atoms:                     0
% 3.36/0.98  num_of_reused_defs:                     0
% 3.36/0.98  num_eq_ax_congr_red:                    4
% 3.36/0.98  num_of_sem_filtered_clauses:            1
% 3.36/0.98  num_of_subtypes:                        0
% 3.36/0.98  monotx_restored_types:                  0
% 3.36/0.98  sat_num_of_epr_types:                   0
% 3.36/0.98  sat_num_of_non_cyclic_types:            0
% 3.36/0.98  sat_guarded_non_collapsed_types:        0
% 3.36/0.98  num_pure_diseq_elim:                    0
% 3.36/0.98  simp_replaced_by:                       0
% 3.36/0.98  res_preprocessed:                       160
% 3.36/0.98  prep_upred:                             0
% 3.36/0.98  prep_unflattend:                        56
% 3.36/0.98  smt_new_axioms:                         0
% 3.36/0.98  pred_elim_cands:                        7
% 3.36/0.98  pred_elim:                              3
% 3.36/0.98  pred_elim_cl:                           -4
% 3.36/0.98  pred_elim_cycles:                       4
% 3.36/0.98  merged_defs:                            0
% 3.36/0.98  merged_defs_ncl:                        0
% 3.36/0.98  bin_hyper_res:                          0
% 3.36/0.98  prep_cycles:                            3
% 3.36/0.98  pred_elim_time:                         0.012
% 3.36/0.98  splitting_time:                         0.
% 3.36/0.98  sem_filter_time:                        0.
% 3.36/0.98  monotx_time:                            0.
% 3.36/0.98  subtype_inf_time:                       0.
% 3.36/0.98  
% 3.36/0.98  ------ Problem properties
% 3.36/0.98  
% 3.36/0.98  clauses:                                45
% 3.36/0.98  conjectures:                            3
% 3.36/0.98  epr:                                    7
% 3.36/0.98  horn:                                   39
% 3.36/0.98  ground:                                 20
% 3.36/0.98  unary:                                  11
% 3.36/0.98  binary:                                 15
% 3.36/0.98  lits:                                   116
% 3.36/0.98  lits_eq:                                51
% 3.36/0.98  fd_pure:                                0
% 3.36/0.98  fd_pseudo:                              0
% 3.36/0.98  fd_cond:                                4
% 3.36/0.98  fd_pseudo_cond:                         0
% 3.36/0.98  ac_symbols:                             0
% 3.36/0.98  
% 3.36/0.98  ------ Propositional Solver
% 3.36/0.98  
% 3.36/0.98  prop_solver_calls:                      25
% 3.36/0.98  prop_fast_solver_calls:                 1307
% 3.36/0.98  smt_solver_calls:                       0
% 3.36/0.98  smt_fast_solver_calls:                  0
% 3.36/0.98  prop_num_of_clauses:                    2728
% 3.36/0.98  prop_preprocess_simplified:             7218
% 3.36/0.98  prop_fo_subsumed:                       58
% 3.36/0.98  prop_solver_time:                       0.
% 3.36/0.98  smt_solver_time:                        0.
% 3.36/0.98  smt_fast_solver_time:                   0.
% 3.36/0.98  prop_fast_solver_time:                  0.
% 3.36/0.98  prop_unsat_core_time:                   0.
% 3.36/0.98  
% 3.36/0.98  ------ QBF
% 3.36/0.98  
% 3.36/0.98  qbf_q_res:                              0
% 3.36/0.98  qbf_num_tautologies:                    0
% 3.36/0.98  qbf_prep_cycles:                        0
% 3.36/0.98  
% 3.36/0.98  ------ BMC1
% 3.36/0.98  
% 3.36/0.98  bmc1_current_bound:                     -1
% 3.36/0.98  bmc1_last_solved_bound:                 -1
% 3.36/0.98  bmc1_unsat_core_size:                   -1
% 3.36/0.98  bmc1_unsat_core_parents_size:           -1
% 3.36/0.98  bmc1_merge_next_fun:                    0
% 3.36/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.36/0.98  
% 3.36/0.98  ------ Instantiation
% 3.36/0.98  
% 3.36/0.98  inst_num_of_clauses:                    975
% 3.36/0.98  inst_num_in_passive:                    488
% 3.36/0.98  inst_num_in_active:                     483
% 3.36/0.98  inst_num_in_unprocessed:                4
% 3.36/0.98  inst_num_of_loops:                      590
% 3.36/0.98  inst_num_of_learning_restarts:          0
% 3.36/0.98  inst_num_moves_active_passive:          102
% 3.36/0.98  inst_lit_activity:                      0
% 3.36/0.98  inst_lit_activity_moves:                0
% 3.36/0.98  inst_num_tautologies:                   0
% 3.36/0.98  inst_num_prop_implied:                  0
% 3.36/0.98  inst_num_existing_simplified:           0
% 3.36/0.98  inst_num_eq_res_simplified:             0
% 3.36/0.98  inst_num_child_elim:                    0
% 3.36/0.98  inst_num_of_dismatching_blockings:      510
% 3.36/0.98  inst_num_of_non_proper_insts:           912
% 3.36/0.98  inst_num_of_duplicates:                 0
% 3.36/0.98  inst_inst_num_from_inst_to_res:         0
% 3.36/0.98  inst_dismatching_checking_time:         0.
% 3.36/0.98  
% 3.36/0.98  ------ Resolution
% 3.36/0.98  
% 3.36/0.98  res_num_of_clauses:                     0
% 3.36/0.98  res_num_in_passive:                     0
% 3.36/0.98  res_num_in_active:                      0
% 3.36/0.98  res_num_of_loops:                       163
% 3.36/0.98  res_forward_subset_subsumed:            43
% 3.36/0.98  res_backward_subset_subsumed:           4
% 3.36/0.98  res_forward_subsumed:                   0
% 3.36/0.98  res_backward_subsumed:                  0
% 3.36/0.98  res_forward_subsumption_resolution:     6
% 3.36/0.98  res_backward_subsumption_resolution:    0
% 3.36/0.98  res_clause_to_clause_subsumption:       400
% 3.36/0.98  res_orphan_elimination:                 0
% 3.36/0.98  res_tautology_del:                      143
% 3.36/0.98  res_num_eq_res_simplified:              0
% 3.36/0.98  res_num_sel_changes:                    0
% 3.36/0.98  res_moves_from_active_to_pass:          0
% 3.36/0.98  
% 3.36/0.98  ------ Superposition
% 3.36/0.98  
% 3.36/0.98  sup_time_total:                         0.
% 3.36/0.98  sup_time_generating:                    0.
% 3.36/0.98  sup_time_sim_full:                      0.
% 3.36/0.98  sup_time_sim_immed:                     0.
% 3.36/0.98  
% 3.36/0.98  sup_num_of_clauses:                     82
% 3.36/0.98  sup_num_in_active:                      54
% 3.36/0.98  sup_num_in_passive:                     28
% 3.36/0.98  sup_num_of_loops:                       116
% 3.36/0.98  sup_fw_superposition:                   85
% 3.36/0.98  sup_bw_superposition:                   80
% 3.36/0.98  sup_immediate_simplified:               109
% 3.36/0.98  sup_given_eliminated:                   2
% 3.36/0.98  comparisons_done:                       0
% 3.36/0.98  comparisons_avoided:                    5
% 3.36/0.98  
% 3.36/0.98  ------ Simplifications
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  sim_fw_subset_subsumed:                 21
% 3.36/0.98  sim_bw_subset_subsumed:                 7
% 3.36/0.98  sim_fw_subsumed:                        19
% 3.36/0.98  sim_bw_subsumed:                        3
% 3.36/0.98  sim_fw_subsumption_res:                 2
% 3.36/0.98  sim_bw_subsumption_res:                 4
% 3.36/0.98  sim_tautology_del:                      3
% 3.36/0.98  sim_eq_tautology_del:                   35
% 3.36/0.98  sim_eq_res_simp:                        8
% 3.36/0.98  sim_fw_demodulated:                     24
% 3.36/0.98  sim_bw_demodulated:                     59
% 3.36/0.98  sim_light_normalised:                   81
% 3.36/0.98  sim_joinable_taut:                      0
% 3.36/0.98  sim_joinable_simp:                      0
% 3.36/0.98  sim_ac_normalised:                      0
% 3.36/0.98  sim_smt_subsumption:                    0
% 3.36/0.98  
%------------------------------------------------------------------------------
