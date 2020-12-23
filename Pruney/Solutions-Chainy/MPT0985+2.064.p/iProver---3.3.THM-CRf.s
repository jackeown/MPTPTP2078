%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:33 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  179 (7645 expanded)
%              Number of clauses        :  114 (2339 expanded)
%              Number of leaves         :   16 (1501 expanded)
%              Depth                    :   26
%              Number of atoms          :  572 (41867 expanded)
%              Number of equality atoms :  273 (8282 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f48,plain,
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

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48])).

fof(f84,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_661,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_663,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_35])).

cnf(c_1335,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1339,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3497,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1335,c_1339])).

cnf(c_3520,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_663,c_3497])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_410,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_411,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_413,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_37])).

cnf(c_1331,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1664,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1668,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1331,c_37,c_35,c_411,c_1664])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1336,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4891,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1336])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1338,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2872,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1335,c_1338])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2884,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2872,c_33])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_396,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_397,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_399,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_37])).

cnf(c_1332,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1672,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1332,c_37,c_35,c_397,c_1664])).

cnf(c_2952,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2884,c_1672])).

cnf(c_4919,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4891,c_2952])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1665,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1743,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1744,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1743])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1746,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1747,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1746])).

cnf(c_5549,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4919,c_38,c_40,c_1665,c_1744,c_1747])).

cnf(c_5557,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5549,c_1339])).

cnf(c_5571,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5557,c_2952])).

cnf(c_5780,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3520,c_5571])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_671,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_672,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_684,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_672,c_15])).

cnf(c_1320,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_673,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_1970,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_38,c_40,c_673,c_1665,c_1744,c_1747])).

cnf(c_1971,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1970])).

cnf(c_1974,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1971,c_1668,c_1672])).

cnf(c_2950,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2884,c_1974])).

cnf(c_2962,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2950])).

cnf(c_3632,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3520,c_2962])).

cnf(c_5554,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3520,c_5549])).

cnf(c_6604,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5780,c_3632,c_5554])).

cnf(c_6609,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6604,c_5549])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_29])).

cnf(c_369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_481,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_465,c_369])).

cnf(c_1329,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_3358,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2884,c_1329])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_798,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1819,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_1821,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2189,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2191,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2139,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3212,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3648,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3358,c_35,c_0,c_1821,c_2191,c_3212])).

cnf(c_6622,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6604,c_3648])).

cnf(c_6709,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6622])).

cnf(c_6798,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6609,c_6709])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6800,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6798,c_4])).

cnf(c_3499,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1339])).

cnf(c_6960,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6800,c_3499])).

cnf(c_6628,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6604,c_2952])).

cnf(c_6716,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6709,c_6628])).

cnf(c_7816,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6960,c_6716])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_562,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_1325,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1557,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1325,c_4])).

cnf(c_2063,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_38,c_40,c_1665,c_1744])).

cnf(c_2064,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2063])).

cnf(c_6631,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6604,c_2064])).

cnf(c_6668,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6631])).

cnf(c_6672,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6668,c_4])).

cnf(c_6718,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6709,c_6672])).

cnf(c_6802,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6800,c_6718])).

cnf(c_7819,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7816,c_6802])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7819,c_108,c_107])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:51:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.15/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/0.99  
% 3.15/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.15/0.99  
% 3.15/0.99  ------  iProver source info
% 3.15/0.99  
% 3.15/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.15/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.15/0.99  git: non_committed_changes: false
% 3.15/0.99  git: last_make_outside_of_git: false
% 3.15/0.99  
% 3.15/0.99  ------ 
% 3.15/0.99  
% 3.15/0.99  ------ Input Options
% 3.15/0.99  
% 3.15/0.99  --out_options                           all
% 3.15/0.99  --tptp_safe_out                         true
% 3.15/0.99  --problem_path                          ""
% 3.15/0.99  --include_path                          ""
% 3.15/0.99  --clausifier                            res/vclausify_rel
% 3.15/0.99  --clausifier_options                    --mode clausify
% 3.15/0.99  --stdin                                 false
% 3.15/0.99  --stats_out                             all
% 3.15/0.99  
% 3.15/0.99  ------ General Options
% 3.15/0.99  
% 3.15/0.99  --fof                                   false
% 3.15/0.99  --time_out_real                         305.
% 3.15/0.99  --time_out_virtual                      -1.
% 3.15/0.99  --symbol_type_check                     false
% 3.15/0.99  --clausify_out                          false
% 3.15/0.99  --sig_cnt_out                           false
% 3.15/0.99  --trig_cnt_out                          false
% 3.15/0.99  --trig_cnt_out_tolerance                1.
% 3.15/0.99  --trig_cnt_out_sk_spl                   false
% 3.15/0.99  --abstr_cl_out                          false
% 3.15/0.99  
% 3.15/0.99  ------ Global Options
% 3.15/0.99  
% 3.15/0.99  --schedule                              default
% 3.15/0.99  --add_important_lit                     false
% 3.15/0.99  --prop_solver_per_cl                    1000
% 3.15/0.99  --min_unsat_core                        false
% 3.15/0.99  --soft_assumptions                      false
% 3.15/0.99  --soft_lemma_size                       3
% 3.15/0.99  --prop_impl_unit_size                   0
% 3.15/0.99  --prop_impl_unit                        []
% 3.15/0.99  --share_sel_clauses                     true
% 3.15/0.99  --reset_solvers                         false
% 3.15/0.99  --bc_imp_inh                            [conj_cone]
% 3.15/0.99  --conj_cone_tolerance                   3.
% 3.15/0.99  --extra_neg_conj                        none
% 3.15/0.99  --large_theory_mode                     true
% 3.15/0.99  --prolific_symb_bound                   200
% 3.15/0.99  --lt_threshold                          2000
% 3.15/0.99  --clause_weak_htbl                      true
% 3.15/0.99  --gc_record_bc_elim                     false
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing Options
% 3.15/0.99  
% 3.15/0.99  --preprocessing_flag                    true
% 3.15/0.99  --time_out_prep_mult                    0.1
% 3.15/0.99  --splitting_mode                        input
% 3.15/0.99  --splitting_grd                         true
% 3.15/0.99  --splitting_cvd                         false
% 3.15/0.99  --splitting_cvd_svl                     false
% 3.15/0.99  --splitting_nvd                         32
% 3.15/0.99  --sub_typing                            true
% 3.15/0.99  --prep_gs_sim                           true
% 3.15/0.99  --prep_unflatten                        true
% 3.15/0.99  --prep_res_sim                          true
% 3.15/0.99  --prep_upred                            true
% 3.15/0.99  --prep_sem_filter                       exhaustive
% 3.15/0.99  --prep_sem_filter_out                   false
% 3.15/0.99  --pred_elim                             true
% 3.15/0.99  --res_sim_input                         true
% 3.15/0.99  --eq_ax_congr_red                       true
% 3.15/0.99  --pure_diseq_elim                       true
% 3.15/0.99  --brand_transform                       false
% 3.15/0.99  --non_eq_to_eq                          false
% 3.15/0.99  --prep_def_merge                        true
% 3.15/0.99  --prep_def_merge_prop_impl              false
% 3.15/0.99  --prep_def_merge_mbd                    true
% 3.15/0.99  --prep_def_merge_tr_red                 false
% 3.15/0.99  --prep_def_merge_tr_cl                  false
% 3.15/0.99  --smt_preprocessing                     true
% 3.15/0.99  --smt_ac_axioms                         fast
% 3.15/0.99  --preprocessed_out                      false
% 3.15/0.99  --preprocessed_stats                    false
% 3.15/0.99  
% 3.15/0.99  ------ Abstraction refinement Options
% 3.15/0.99  
% 3.15/0.99  --abstr_ref                             []
% 3.15/0.99  --abstr_ref_prep                        false
% 3.15/0.99  --abstr_ref_until_sat                   false
% 3.15/0.99  --abstr_ref_sig_restrict                funpre
% 3.15/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/0.99  --abstr_ref_under                       []
% 3.15/0.99  
% 3.15/0.99  ------ SAT Options
% 3.15/0.99  
% 3.15/0.99  --sat_mode                              false
% 3.15/0.99  --sat_fm_restart_options                ""
% 3.15/0.99  --sat_gr_def                            false
% 3.15/0.99  --sat_epr_types                         true
% 3.15/0.99  --sat_non_cyclic_types                  false
% 3.15/0.99  --sat_finite_models                     false
% 3.15/0.99  --sat_fm_lemmas                         false
% 3.15/0.99  --sat_fm_prep                           false
% 3.15/0.99  --sat_fm_uc_incr                        true
% 3.15/0.99  --sat_out_model                         small
% 3.15/0.99  --sat_out_clauses                       false
% 3.15/0.99  
% 3.15/0.99  ------ QBF Options
% 3.15/0.99  
% 3.15/0.99  --qbf_mode                              false
% 3.15/0.99  --qbf_elim_univ                         false
% 3.15/0.99  --qbf_dom_inst                          none
% 3.15/0.99  --qbf_dom_pre_inst                      false
% 3.15/0.99  --qbf_sk_in                             false
% 3.15/0.99  --qbf_pred_elim                         true
% 3.15/0.99  --qbf_split                             512
% 3.15/0.99  
% 3.15/0.99  ------ BMC1 Options
% 3.15/0.99  
% 3.15/0.99  --bmc1_incremental                      false
% 3.15/0.99  --bmc1_axioms                           reachable_all
% 3.15/0.99  --bmc1_min_bound                        0
% 3.15/0.99  --bmc1_max_bound                        -1
% 3.15/0.99  --bmc1_max_bound_default                -1
% 3.15/0.99  --bmc1_symbol_reachability              true
% 3.15/0.99  --bmc1_property_lemmas                  false
% 3.15/0.99  --bmc1_k_induction                      false
% 3.15/0.99  --bmc1_non_equiv_states                 false
% 3.15/0.99  --bmc1_deadlock                         false
% 3.15/0.99  --bmc1_ucm                              false
% 3.15/0.99  --bmc1_add_unsat_core                   none
% 3.15/0.99  --bmc1_unsat_core_children              false
% 3.15/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/0.99  --bmc1_out_stat                         full
% 3.15/0.99  --bmc1_ground_init                      false
% 3.15/0.99  --bmc1_pre_inst_next_state              false
% 3.15/0.99  --bmc1_pre_inst_state                   false
% 3.15/0.99  --bmc1_pre_inst_reach_state             false
% 3.15/0.99  --bmc1_out_unsat_core                   false
% 3.15/0.99  --bmc1_aig_witness_out                  false
% 3.15/0.99  --bmc1_verbose                          false
% 3.15/0.99  --bmc1_dump_clauses_tptp                false
% 3.15/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.15/0.99  --bmc1_dump_file                        -
% 3.15/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.15/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.15/0.99  --bmc1_ucm_extend_mode                  1
% 3.15/0.99  --bmc1_ucm_init_mode                    2
% 3.15/0.99  --bmc1_ucm_cone_mode                    none
% 3.15/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.15/0.99  --bmc1_ucm_relax_model                  4
% 3.15/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.15/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/0.99  --bmc1_ucm_layered_model                none
% 3.15/0.99  --bmc1_ucm_max_lemma_size               10
% 3.15/0.99  
% 3.15/0.99  ------ AIG Options
% 3.15/0.99  
% 3.15/0.99  --aig_mode                              false
% 3.15/0.99  
% 3.15/0.99  ------ Instantiation Options
% 3.15/0.99  
% 3.15/0.99  --instantiation_flag                    true
% 3.15/0.99  --inst_sos_flag                         false
% 3.15/0.99  --inst_sos_phase                        true
% 3.15/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/0.99  --inst_lit_sel_side                     num_symb
% 3.15/0.99  --inst_solver_per_active                1400
% 3.15/0.99  --inst_solver_calls_frac                1.
% 3.15/0.99  --inst_passive_queue_type               priority_queues
% 3.15/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/0.99  --inst_passive_queues_freq              [25;2]
% 3.15/0.99  --inst_dismatching                      true
% 3.15/0.99  --inst_eager_unprocessed_to_passive     true
% 3.15/0.99  --inst_prop_sim_given                   true
% 3.15/0.99  --inst_prop_sim_new                     false
% 3.15/0.99  --inst_subs_new                         false
% 3.15/0.99  --inst_eq_res_simp                      false
% 3.15/0.99  --inst_subs_given                       false
% 3.15/0.99  --inst_orphan_elimination               true
% 3.15/0.99  --inst_learning_loop_flag               true
% 3.15/0.99  --inst_learning_start                   3000
% 3.15/0.99  --inst_learning_factor                  2
% 3.15/0.99  --inst_start_prop_sim_after_learn       3
% 3.15/0.99  --inst_sel_renew                        solver
% 3.15/0.99  --inst_lit_activity_flag                true
% 3.15/0.99  --inst_restr_to_given                   false
% 3.15/0.99  --inst_activity_threshold               500
% 3.15/0.99  --inst_out_proof                        true
% 3.15/0.99  
% 3.15/0.99  ------ Resolution Options
% 3.15/0.99  
% 3.15/0.99  --resolution_flag                       true
% 3.15/0.99  --res_lit_sel                           adaptive
% 3.15/0.99  --res_lit_sel_side                      none
% 3.15/0.99  --res_ordering                          kbo
% 3.15/0.99  --res_to_prop_solver                    active
% 3.15/0.99  --res_prop_simpl_new                    false
% 3.15/0.99  --res_prop_simpl_given                  true
% 3.15/0.99  --res_passive_queue_type                priority_queues
% 3.15/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/0.99  --res_passive_queues_freq               [15;5]
% 3.15/0.99  --res_forward_subs                      full
% 3.15/0.99  --res_backward_subs                     full
% 3.15/0.99  --res_forward_subs_resolution           true
% 3.15/0.99  --res_backward_subs_resolution          true
% 3.15/0.99  --res_orphan_elimination                true
% 3.15/0.99  --res_time_limit                        2.
% 3.15/0.99  --res_out_proof                         true
% 3.15/0.99  
% 3.15/0.99  ------ Superposition Options
% 3.15/0.99  
% 3.15/0.99  --superposition_flag                    true
% 3.15/0.99  --sup_passive_queue_type                priority_queues
% 3.15/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.15/0.99  --demod_completeness_check              fast
% 3.15/0.99  --demod_use_ground                      true
% 3.15/0.99  --sup_to_prop_solver                    passive
% 3.15/0.99  --sup_prop_simpl_new                    true
% 3.15/0.99  --sup_prop_simpl_given                  true
% 3.15/0.99  --sup_fun_splitting                     false
% 3.15/0.99  --sup_smt_interval                      50000
% 3.15/0.99  
% 3.15/0.99  ------ Superposition Simplification Setup
% 3.15/0.99  
% 3.15/0.99  --sup_indices_passive                   []
% 3.15/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_full_bw                           [BwDemod]
% 3.15/0.99  --sup_immed_triv                        [TrivRules]
% 3.15/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_immed_bw_main                     []
% 3.15/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.99  
% 3.15/0.99  ------ Combination Options
% 3.15/0.99  
% 3.15/0.99  --comb_res_mult                         3
% 3.15/0.99  --comb_sup_mult                         2
% 3.15/0.99  --comb_inst_mult                        10
% 3.15/0.99  
% 3.15/0.99  ------ Debug Options
% 3.15/0.99  
% 3.15/0.99  --dbg_backtrace                         false
% 3.15/0.99  --dbg_dump_prop_clauses                 false
% 3.15/0.99  --dbg_dump_prop_clauses_file            -
% 3.15/0.99  --dbg_out_stat                          false
% 3.15/0.99  ------ Parsing...
% 3.15/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.15/0.99  ------ Proving...
% 3.15/0.99  ------ Problem Properties 
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  clauses                                 38
% 3.15/0.99  conjectures                             3
% 3.15/0.99  EPR                                     3
% 3.15/0.99  Horn                                    32
% 3.15/0.99  unary                                   10
% 3.15/0.99  binary                                  6
% 3.15/0.99  lits                                    107
% 3.15/0.99  lits eq                                 47
% 3.15/0.99  fd_pure                                 0
% 3.15/0.99  fd_pseudo                               0
% 3.15/0.99  fd_cond                                 3
% 3.15/0.99  fd_pseudo_cond                          1
% 3.15/0.99  AC symbols                              0
% 3.15/0.99  
% 3.15/0.99  ------ Schedule dynamic 5 is on 
% 3.15/0.99  
% 3.15/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  ------ 
% 3.15/0.99  Current options:
% 3.15/0.99  ------ 
% 3.15/0.99  
% 3.15/0.99  ------ Input Options
% 3.15/0.99  
% 3.15/0.99  --out_options                           all
% 3.15/0.99  --tptp_safe_out                         true
% 3.15/0.99  --problem_path                          ""
% 3.15/0.99  --include_path                          ""
% 3.15/0.99  --clausifier                            res/vclausify_rel
% 3.15/0.99  --clausifier_options                    --mode clausify
% 3.15/0.99  --stdin                                 false
% 3.15/0.99  --stats_out                             all
% 3.15/0.99  
% 3.15/0.99  ------ General Options
% 3.15/0.99  
% 3.15/0.99  --fof                                   false
% 3.15/0.99  --time_out_real                         305.
% 3.15/0.99  --time_out_virtual                      -1.
% 3.15/0.99  --symbol_type_check                     false
% 3.15/0.99  --clausify_out                          false
% 3.15/0.99  --sig_cnt_out                           false
% 3.15/0.99  --trig_cnt_out                          false
% 3.15/0.99  --trig_cnt_out_tolerance                1.
% 3.15/0.99  --trig_cnt_out_sk_spl                   false
% 3.15/0.99  --abstr_cl_out                          false
% 3.15/0.99  
% 3.15/0.99  ------ Global Options
% 3.15/0.99  
% 3.15/0.99  --schedule                              default
% 3.15/0.99  --add_important_lit                     false
% 3.15/0.99  --prop_solver_per_cl                    1000
% 3.15/0.99  --min_unsat_core                        false
% 3.15/0.99  --soft_assumptions                      false
% 3.15/0.99  --soft_lemma_size                       3
% 3.15/0.99  --prop_impl_unit_size                   0
% 3.15/0.99  --prop_impl_unit                        []
% 3.15/0.99  --share_sel_clauses                     true
% 3.15/0.99  --reset_solvers                         false
% 3.15/0.99  --bc_imp_inh                            [conj_cone]
% 3.15/0.99  --conj_cone_tolerance                   3.
% 3.15/0.99  --extra_neg_conj                        none
% 3.15/0.99  --large_theory_mode                     true
% 3.15/0.99  --prolific_symb_bound                   200
% 3.15/0.99  --lt_threshold                          2000
% 3.15/0.99  --clause_weak_htbl                      true
% 3.15/0.99  --gc_record_bc_elim                     false
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing Options
% 3.15/0.99  
% 3.15/0.99  --preprocessing_flag                    true
% 3.15/0.99  --time_out_prep_mult                    0.1
% 3.15/0.99  --splitting_mode                        input
% 3.15/0.99  --splitting_grd                         true
% 3.15/0.99  --splitting_cvd                         false
% 3.15/0.99  --splitting_cvd_svl                     false
% 3.15/0.99  --splitting_nvd                         32
% 3.15/0.99  --sub_typing                            true
% 3.15/0.99  --prep_gs_sim                           true
% 3.15/0.99  --prep_unflatten                        true
% 3.15/0.99  --prep_res_sim                          true
% 3.15/0.99  --prep_upred                            true
% 3.15/0.99  --prep_sem_filter                       exhaustive
% 3.15/0.99  --prep_sem_filter_out                   false
% 3.15/0.99  --pred_elim                             true
% 3.15/0.99  --res_sim_input                         true
% 3.15/0.99  --eq_ax_congr_red                       true
% 3.15/0.99  --pure_diseq_elim                       true
% 3.15/0.99  --brand_transform                       false
% 3.15/0.99  --non_eq_to_eq                          false
% 3.15/0.99  --prep_def_merge                        true
% 3.15/0.99  --prep_def_merge_prop_impl              false
% 3.15/0.99  --prep_def_merge_mbd                    true
% 3.15/0.99  --prep_def_merge_tr_red                 false
% 3.15/0.99  --prep_def_merge_tr_cl                  false
% 3.15/0.99  --smt_preprocessing                     true
% 3.15/0.99  --smt_ac_axioms                         fast
% 3.15/0.99  --preprocessed_out                      false
% 3.15/0.99  --preprocessed_stats                    false
% 3.15/0.99  
% 3.15/0.99  ------ Abstraction refinement Options
% 3.15/0.99  
% 3.15/0.99  --abstr_ref                             []
% 3.15/0.99  --abstr_ref_prep                        false
% 3.15/0.99  --abstr_ref_until_sat                   false
% 3.15/0.99  --abstr_ref_sig_restrict                funpre
% 3.15/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/0.99  --abstr_ref_under                       []
% 3.15/0.99  
% 3.15/0.99  ------ SAT Options
% 3.15/0.99  
% 3.15/0.99  --sat_mode                              false
% 3.15/0.99  --sat_fm_restart_options                ""
% 3.15/0.99  --sat_gr_def                            false
% 3.15/0.99  --sat_epr_types                         true
% 3.15/0.99  --sat_non_cyclic_types                  false
% 3.15/0.99  --sat_finite_models                     false
% 3.15/0.99  --sat_fm_lemmas                         false
% 3.15/0.99  --sat_fm_prep                           false
% 3.15/0.99  --sat_fm_uc_incr                        true
% 3.15/0.99  --sat_out_model                         small
% 3.15/0.99  --sat_out_clauses                       false
% 3.15/0.99  
% 3.15/0.99  ------ QBF Options
% 3.15/0.99  
% 3.15/0.99  --qbf_mode                              false
% 3.15/0.99  --qbf_elim_univ                         false
% 3.15/0.99  --qbf_dom_inst                          none
% 3.15/0.99  --qbf_dom_pre_inst                      false
% 3.15/0.99  --qbf_sk_in                             false
% 3.15/0.99  --qbf_pred_elim                         true
% 3.15/0.99  --qbf_split                             512
% 3.15/0.99  
% 3.15/0.99  ------ BMC1 Options
% 3.15/0.99  
% 3.15/0.99  --bmc1_incremental                      false
% 3.15/0.99  --bmc1_axioms                           reachable_all
% 3.15/0.99  --bmc1_min_bound                        0
% 3.15/0.99  --bmc1_max_bound                        -1
% 3.15/0.99  --bmc1_max_bound_default                -1
% 3.15/0.99  --bmc1_symbol_reachability              true
% 3.15/0.99  --bmc1_property_lemmas                  false
% 3.15/0.99  --bmc1_k_induction                      false
% 3.15/0.99  --bmc1_non_equiv_states                 false
% 3.15/0.99  --bmc1_deadlock                         false
% 3.15/0.99  --bmc1_ucm                              false
% 3.15/0.99  --bmc1_add_unsat_core                   none
% 3.15/0.99  --bmc1_unsat_core_children              false
% 3.15/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/0.99  --bmc1_out_stat                         full
% 3.15/0.99  --bmc1_ground_init                      false
% 3.15/0.99  --bmc1_pre_inst_next_state              false
% 3.15/0.99  --bmc1_pre_inst_state                   false
% 3.15/0.99  --bmc1_pre_inst_reach_state             false
% 3.15/0.99  --bmc1_out_unsat_core                   false
% 3.15/0.99  --bmc1_aig_witness_out                  false
% 3.15/0.99  --bmc1_verbose                          false
% 3.15/0.99  --bmc1_dump_clauses_tptp                false
% 3.15/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.15/0.99  --bmc1_dump_file                        -
% 3.15/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.15/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.15/0.99  --bmc1_ucm_extend_mode                  1
% 3.15/0.99  --bmc1_ucm_init_mode                    2
% 3.15/0.99  --bmc1_ucm_cone_mode                    none
% 3.15/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.15/0.99  --bmc1_ucm_relax_model                  4
% 3.15/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.15/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/0.99  --bmc1_ucm_layered_model                none
% 3.15/0.99  --bmc1_ucm_max_lemma_size               10
% 3.15/0.99  
% 3.15/0.99  ------ AIG Options
% 3.15/0.99  
% 3.15/0.99  --aig_mode                              false
% 3.15/0.99  
% 3.15/0.99  ------ Instantiation Options
% 3.15/0.99  
% 3.15/0.99  --instantiation_flag                    true
% 3.15/0.99  --inst_sos_flag                         false
% 3.15/0.99  --inst_sos_phase                        true
% 3.15/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/0.99  --inst_lit_sel_side                     none
% 3.15/0.99  --inst_solver_per_active                1400
% 3.15/0.99  --inst_solver_calls_frac                1.
% 3.15/0.99  --inst_passive_queue_type               priority_queues
% 3.15/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/0.99  --inst_passive_queues_freq              [25;2]
% 3.15/0.99  --inst_dismatching                      true
% 3.15/0.99  --inst_eager_unprocessed_to_passive     true
% 3.15/0.99  --inst_prop_sim_given                   true
% 3.15/0.99  --inst_prop_sim_new                     false
% 3.15/0.99  --inst_subs_new                         false
% 3.15/0.99  --inst_eq_res_simp                      false
% 3.15/0.99  --inst_subs_given                       false
% 3.15/0.99  --inst_orphan_elimination               true
% 3.15/0.99  --inst_learning_loop_flag               true
% 3.15/0.99  --inst_learning_start                   3000
% 3.15/0.99  --inst_learning_factor                  2
% 3.15/0.99  --inst_start_prop_sim_after_learn       3
% 3.15/0.99  --inst_sel_renew                        solver
% 3.15/0.99  --inst_lit_activity_flag                true
% 3.15/0.99  --inst_restr_to_given                   false
% 3.15/0.99  --inst_activity_threshold               500
% 3.15/0.99  --inst_out_proof                        true
% 3.15/0.99  
% 3.15/0.99  ------ Resolution Options
% 3.15/0.99  
% 3.15/0.99  --resolution_flag                       false
% 3.15/0.99  --res_lit_sel                           adaptive
% 3.15/0.99  --res_lit_sel_side                      none
% 3.15/0.99  --res_ordering                          kbo
% 3.15/0.99  --res_to_prop_solver                    active
% 3.15/0.99  --res_prop_simpl_new                    false
% 3.15/0.99  --res_prop_simpl_given                  true
% 3.15/0.99  --res_passive_queue_type                priority_queues
% 3.15/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/0.99  --res_passive_queues_freq               [15;5]
% 3.15/0.99  --res_forward_subs                      full
% 3.15/0.99  --res_backward_subs                     full
% 3.15/0.99  --res_forward_subs_resolution           true
% 3.15/0.99  --res_backward_subs_resolution          true
% 3.15/0.99  --res_orphan_elimination                true
% 3.15/0.99  --res_time_limit                        2.
% 3.15/0.99  --res_out_proof                         true
% 3.15/0.99  
% 3.15/0.99  ------ Superposition Options
% 3.15/0.99  
% 3.15/0.99  --superposition_flag                    true
% 3.15/0.99  --sup_passive_queue_type                priority_queues
% 3.15/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.15/0.99  --demod_completeness_check              fast
% 3.15/0.99  --demod_use_ground                      true
% 3.15/0.99  --sup_to_prop_solver                    passive
% 3.15/0.99  --sup_prop_simpl_new                    true
% 3.15/0.99  --sup_prop_simpl_given                  true
% 3.15/0.99  --sup_fun_splitting                     false
% 3.15/0.99  --sup_smt_interval                      50000
% 3.15/0.99  
% 3.15/0.99  ------ Superposition Simplification Setup
% 3.15/0.99  
% 3.15/0.99  --sup_indices_passive                   []
% 3.15/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_full_bw                           [BwDemod]
% 3.15/0.99  --sup_immed_triv                        [TrivRules]
% 3.15/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_immed_bw_main                     []
% 3.15/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/0.99  
% 3.15/0.99  ------ Combination Options
% 3.15/0.99  
% 3.15/0.99  --comb_res_mult                         3
% 3.15/0.99  --comb_sup_mult                         2
% 3.15/0.99  --comb_inst_mult                        10
% 3.15/0.99  
% 3.15/0.99  ------ Debug Options
% 3.15/0.99  
% 3.15/0.99  --dbg_backtrace                         false
% 3.15/0.99  --dbg_dump_prop_clauses                 false
% 3.15/0.99  --dbg_dump_prop_clauses_file            -
% 3.15/0.99  --dbg_out_stat                          false
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  ------ Proving...
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  % SZS status Theorem for theBenchmark.p
% 3.15/0.99  
% 3.15/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.15/0.99  
% 3.15/0.99  fof(f16,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f37,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f16])).
% 3.15/0.99  
% 3.15/0.99  fof(f38,plain,(
% 3.15/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(flattening,[],[f37])).
% 3.15/0.99  
% 3.15/0.99  fof(f47,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(nnf_transformation,[],[f38])).
% 3.15/0.99  
% 3.15/0.99  fof(f69,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f47])).
% 3.15/0.99  
% 3.15/0.99  fof(f21,conjecture,(
% 3.15/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f22,negated_conjecture,(
% 3.15/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.15/0.99    inference(negated_conjecture,[],[f21])).
% 3.15/0.99  
% 3.15/0.99  fof(f43,plain,(
% 3.15/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.15/0.99    inference(ennf_transformation,[],[f22])).
% 3.15/0.99  
% 3.15/0.99  fof(f44,plain,(
% 3.15/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.15/0.99    inference(flattening,[],[f43])).
% 3.15/0.99  
% 3.15/0.99  fof(f48,plain,(
% 3.15/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.15/0.99    introduced(choice_axiom,[])).
% 3.15/0.99  
% 3.15/0.99  fof(f49,plain,(
% 3.15/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.15/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48])).
% 3.15/0.99  
% 3.15/0.99  fof(f84,plain,(
% 3.15/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.15/0.99    inference(cnf_transformation,[],[f49])).
% 3.15/0.99  
% 3.15/0.99  fof(f85,plain,(
% 3.15/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.15/0.99    inference(cnf_transformation,[],[f49])).
% 3.15/0.99  
% 3.15/0.99  fof(f14,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f35,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f14])).
% 3.15/0.99  
% 3.15/0.99  fof(f67,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f35])).
% 3.15/0.99  
% 3.15/0.99  fof(f11,axiom,(
% 3.15/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f31,plain,(
% 3.15/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/0.99    inference(ennf_transformation,[],[f11])).
% 3.15/0.99  
% 3.15/0.99  fof(f32,plain,(
% 3.15/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/0.99    inference(flattening,[],[f31])).
% 3.15/0.99  
% 3.15/0.99  fof(f64,plain,(
% 3.15/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f32])).
% 3.15/0.99  
% 3.15/0.99  fof(f86,plain,(
% 3.15/0.99    v2_funct_1(sK2)),
% 3.15/0.99    inference(cnf_transformation,[],[f49])).
% 3.15/0.99  
% 3.15/0.99  fof(f83,plain,(
% 3.15/0.99    v1_funct_1(sK2)),
% 3.15/0.99    inference(cnf_transformation,[],[f49])).
% 3.15/0.99  
% 3.15/0.99  fof(f12,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f33,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f12])).
% 3.15/0.99  
% 3.15/0.99  fof(f65,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f33])).
% 3.15/0.99  
% 3.15/0.99  fof(f19,axiom,(
% 3.15/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f39,plain,(
% 3.15/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/0.99    inference(ennf_transformation,[],[f19])).
% 3.15/0.99  
% 3.15/0.99  fof(f40,plain,(
% 3.15/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/0.99    inference(flattening,[],[f39])).
% 3.15/0.99  
% 3.15/0.99  fof(f79,plain,(
% 3.15/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f40])).
% 3.15/0.99  
% 3.15/0.99  fof(f15,axiom,(
% 3.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f36,plain,(
% 3.15/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/0.99    inference(ennf_transformation,[],[f15])).
% 3.15/0.99  
% 3.15/0.99  fof(f68,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f36])).
% 3.15/0.99  
% 3.15/0.99  fof(f87,plain,(
% 3.15/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.15/0.99    inference(cnf_transformation,[],[f49])).
% 3.15/0.99  
% 3.15/0.99  fof(f63,plain,(
% 3.15/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f32])).
% 3.15/0.99  
% 3.15/0.99  fof(f10,axiom,(
% 3.15/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f29,plain,(
% 3.15/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/0.99    inference(ennf_transformation,[],[f10])).
% 3.15/0.99  
% 3.15/0.99  fof(f30,plain,(
% 3.15/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/0.99    inference(flattening,[],[f29])).
% 3.15/0.99  
% 3.15/0.99  fof(f62,plain,(
% 3.15/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f30])).
% 3.15/0.99  
% 3.15/0.99  fof(f61,plain,(
% 3.15/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f30])).
% 3.15/0.99  
% 3.15/0.99  fof(f78,plain,(
% 3.15/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f40])).
% 3.15/0.99  
% 3.15/0.99  fof(f88,plain,(
% 3.15/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.15/0.99    inference(cnf_transformation,[],[f49])).
% 3.15/0.99  
% 3.15/0.99  fof(f73,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f47])).
% 3.15/0.99  
% 3.15/0.99  fof(f95,plain,(
% 3.15/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.15/0.99    inference(equality_resolution,[],[f73])).
% 3.15/0.99  
% 3.15/0.99  fof(f2,axiom,(
% 3.15/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f51,plain,(
% 3.15/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f2])).
% 3.15/0.99  
% 3.15/0.99  fof(f20,axiom,(
% 3.15/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f41,plain,(
% 3.15/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.15/0.99    inference(ennf_transformation,[],[f20])).
% 3.15/0.99  
% 3.15/0.99  fof(f42,plain,(
% 3.15/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.15/0.99    inference(flattening,[],[f41])).
% 3.15/0.99  
% 3.15/0.99  fof(f82,plain,(
% 3.15/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f42])).
% 3.15/0.99  
% 3.15/0.99  fof(f1,axiom,(
% 3.15/0.99    v1_xboole_0(k1_xboole_0)),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f50,plain,(
% 3.15/0.99    v1_xboole_0(k1_xboole_0)),
% 3.15/0.99    inference(cnf_transformation,[],[f1])).
% 3.15/0.99  
% 3.15/0.99  fof(f3,axiom,(
% 3.15/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f25,plain,(
% 3.15/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.15/0.99    inference(ennf_transformation,[],[f3])).
% 3.15/0.99  
% 3.15/0.99  fof(f52,plain,(
% 3.15/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f25])).
% 3.15/0.99  
% 3.15/0.99  fof(f13,axiom,(
% 3.15/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f34,plain,(
% 3.15/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.15/0.99    inference(ennf_transformation,[],[f13])).
% 3.15/0.99  
% 3.15/0.99  fof(f66,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f34])).
% 3.15/0.99  
% 3.15/0.99  fof(f4,axiom,(
% 3.15/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/0.99  
% 3.15/0.99  fof(f45,plain,(
% 3.15/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.15/0.99    inference(nnf_transformation,[],[f4])).
% 3.15/0.99  
% 3.15/0.99  fof(f46,plain,(
% 3.15/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.15/0.99    inference(flattening,[],[f45])).
% 3.15/0.99  
% 3.15/0.99  fof(f54,plain,(
% 3.15/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.15/0.99    inference(cnf_transformation,[],[f46])).
% 3.15/0.99  
% 3.15/0.99  fof(f92,plain,(
% 3.15/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.15/0.99    inference(equality_resolution,[],[f54])).
% 3.15/0.99  
% 3.15/0.99  fof(f72,plain,(
% 3.15/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/0.99    inference(cnf_transformation,[],[f47])).
% 3.15/0.99  
% 3.15/0.99  fof(f96,plain,(
% 3.15/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.15/0.99    inference(equality_resolution,[],[f72])).
% 3.15/0.99  
% 3.15/0.99  fof(f53,plain,(
% 3.15/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.15/0.99    inference(cnf_transformation,[],[f46])).
% 3.15/0.99  
% 3.15/0.99  cnf(c_24,plain,
% 3.15/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.15/0.99      | k1_xboole_0 = X2 ),
% 3.15/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_36,negated_conjecture,
% 3.15/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.15/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_660,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.15/0.99      | sK0 != X1
% 3.15/0.99      | sK1 != X2
% 3.15/0.99      | sK2 != X0
% 3.15/0.99      | k1_xboole_0 = X2 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_661,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.15/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.15/0.99      | k1_xboole_0 = sK1 ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_660]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_35,negated_conjecture,
% 3.15/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.15/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_663,plain,
% 3.15/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_661,c_35]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1335,plain,
% 3.15/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_17,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1339,plain,
% 3.15/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3497,plain,
% 3.15/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1335,c_1339]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3520,plain,
% 3.15/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_663,c_3497]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_13,plain,
% 3.15/0.99      ( ~ v2_funct_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_34,negated_conjecture,
% 3.15/0.99      ( v2_funct_1(sK2) ),
% 3.15/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_410,plain,
% 3.15/0.99      ( ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.15/0.99      | sK2 != X0 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_411,plain,
% 3.15/0.99      ( ~ v1_relat_1(sK2)
% 3.15/0.99      | ~ v1_funct_1(sK2)
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_37,negated_conjecture,
% 3.15/0.99      ( v1_funct_1(sK2) ),
% 3.15/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_413,plain,
% 3.15/0.99      ( ~ v1_relat_1(sK2)
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_411,c_37]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1331,plain,
% 3.15/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.15/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_15,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | v1_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1664,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.15/0.99      | v1_relat_1(sK2) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1668,plain,
% 3.15/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_1331,c_37,c_35,c_411,c_1664]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_26,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1336,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.15/0.99      | v1_relat_1(X0) != iProver_top
% 3.15/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_4891,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.15/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1668,c_1336]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_18,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1338,plain,
% 3.15/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.15/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2872,plain,
% 3.15/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_1335,c_1338]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_33,negated_conjecture,
% 3.15/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.15/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2884,plain,
% 3.15/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_2872,c_33]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_14,plain,
% 3.15/0.99      ( ~ v2_funct_1(X0)
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_396,plain,
% 3.15/0.99      ( ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.15/0.99      | sK2 != X0 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_397,plain,
% 3.15/0.99      ( ~ v1_relat_1(sK2)
% 3.15/0.99      | ~ v1_funct_1(sK2)
% 3.15/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_399,plain,
% 3.15/0.99      ( ~ v1_relat_1(sK2)
% 3.15/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_397,c_37]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1332,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.15/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1672,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_1332,c_37,c_35,c_397,c_1664]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2952,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_2884,c_1672]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_4919,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.15/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_4891,c_2952]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_38,plain,
% 3.15/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_40,plain,
% 3.15/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1665,plain,
% 3.15/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.15/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_11,plain,
% 3.15/0.99      ( ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 3.15/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1743,plain,
% 3.15/0.99      ( ~ v1_relat_1(sK2)
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.15/0.99      | ~ v1_funct_1(sK2) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1744,plain,
% 3.15/0.99      ( v1_relat_1(sK2) != iProver_top
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.15/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_1743]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_12,plain,
% 3.15/0.99      ( ~ v1_relat_1(X0)
% 3.15/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.15/0.99      | ~ v1_funct_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1746,plain,
% 3.15/0.99      ( v1_relat_1(k2_funct_1(sK2))
% 3.15/0.99      | ~ v1_relat_1(sK2)
% 3.15/0.99      | ~ v1_funct_1(sK2) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1747,plain,
% 3.15/0.99      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.15/0.99      | v1_relat_1(sK2) != iProver_top
% 3.15/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_1746]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5549,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_4919,c_38,c_40,c_1665,c_1744,c_1747]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5557,plain,
% 3.15/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_5549,c_1339]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5571,plain,
% 3.15/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_5557,c_2952]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5780,plain,
% 3.15/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_3520,c_5571]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_27,plain,
% 3.15/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_32,negated_conjecture,
% 3.15/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.15/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.15/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.15/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_671,plain,
% 3.15/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.15/0.99      | k2_funct_1(sK2) != X0
% 3.15/0.99      | k1_relat_1(X0) != sK1
% 3.15/0.99      | k2_relat_1(X0) != sK0 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_672,plain,
% 3.15/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.15/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.15/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.15/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_671]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_684,plain,
% 3.15/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.15/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.15/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.15/0.99      inference(forward_subsumption_resolution,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_672,c_15]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1320,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_673,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.15/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1970,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.15/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_1320,c_38,c_40,c_673,c_1665,c_1744,c_1747]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1971,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.15/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.15/0.99      inference(renaming,[status(thm)],[c_1970]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1974,plain,
% 3.15/0.99      ( k1_relat_1(sK2) != sK0
% 3.15/0.99      | k2_relat_1(sK2) != sK1
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_1971,c_1668,c_1672]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2950,plain,
% 3.15/0.99      ( k1_relat_1(sK2) != sK0
% 3.15/0.99      | sK1 != sK1
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_2884,c_1974]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2962,plain,
% 3.15/0.99      ( k1_relat_1(sK2) != sK0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.15/0.99      inference(equality_resolution_simp,[status(thm)],[c_2950]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3632,plain,
% 3.15/0.99      ( sK1 = k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_3520,c_2962]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5554,plain,
% 3.15/0.99      ( sK1 = k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_3520,c_5549]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6604,plain,
% 3.15/0.99      ( sK1 = k1_xboole_0 ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_5780,c_3632,c_5554]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6609,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6604,c_5549]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_20,plain,
% 3.15/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.15/0.99      | k1_xboole_0 = X1
% 3.15/0.99      | k1_xboole_0 = X0 ),
% 3.15/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_464,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.15/0.99      | ~ v1_relat_1(X2)
% 3.15/0.99      | ~ v1_funct_1(X2)
% 3.15/0.99      | X2 != X0
% 3.15/0.99      | k1_relat_1(X2) != X1
% 3.15/0.99      | k2_relat_1(X2) != k1_xboole_0
% 3.15/0.99      | k1_xboole_0 = X1
% 3.15/0.99      | k1_xboole_0 = X0 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_465,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.15/0.99      | k1_xboole_0 = X0
% 3.15/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_464]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1,plain,
% 3.15/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_29,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.15/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_368,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | X1 != X2
% 3.15/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_29]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_369,plain,
% 3.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.15/0.99      | ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_481,plain,
% 3.15/0.99      ( ~ v1_relat_1(X0)
% 3.15/0.99      | ~ v1_funct_1(X0)
% 3.15/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.15/0.99      | k1_xboole_0 = X0
% 3.15/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.15/0.99      inference(forward_subsumption_resolution,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_465,c_369]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1329,plain,
% 3.15/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.15/0.99      | k1_xboole_0 = X0
% 3.15/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.15/0.99      | v1_relat_1(X0) != iProver_top
% 3.15/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3358,plain,
% 3.15/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.15/0.99      | sK1 != k1_xboole_0
% 3.15/0.99      | sK2 = k1_xboole_0
% 3.15/0.99      | v1_relat_1(sK2) != iProver_top
% 3.15/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_2884,c_1329]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_0,plain,
% 3.15/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_798,plain,
% 3.15/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.15/0.99      theory(equality) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1819,plain,
% 3.15/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_798]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1821,plain,
% 3.15/0.99      ( v1_xboole_0(sK1)
% 3.15/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.15/0.99      | sK1 != k1_xboole_0 ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_1819]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2,plain,
% 3.15/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.15/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2189,plain,
% 3.15/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2191,plain,
% 3.15/0.99      ( ~ v1_xboole_0(sK2)
% 3.15/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.15/0.99      | sK2 = k1_xboole_0 ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_2189]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_16,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/0.99      | ~ v1_xboole_0(X2)
% 3.15/0.99      | v1_xboole_0(X0) ),
% 3.15/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2139,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.15/0.99      | ~ v1_xboole_0(X1)
% 3.15/0.99      | v1_xboole_0(sK2) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3212,plain,
% 3.15/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.15/0.99      | ~ v1_xboole_0(sK1)
% 3.15/0.99      | v1_xboole_0(sK2) ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_2139]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3648,plain,
% 3.15/0.99      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_3358,c_35,c_0,c_1821,c_2191,c_3212]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6622,plain,
% 3.15/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6604,c_3648]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6709,plain,
% 3.15/0.99      ( sK2 = k1_xboole_0 ),
% 3.15/0.99      inference(equality_resolution_simp,[status(thm)],[c_6622]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6798,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_6609,c_6709]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_4,plain,
% 3.15/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.15/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6800,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6798,c_4]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_3499,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.15/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_4,c_1339]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6960,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 3.15/0.99      inference(superposition,[status(thm)],[c_6800,c_3499]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6628,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6604,c_2952]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6716,plain,
% 3.15/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6709,c_6628]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_7816,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.15/0.99      inference(light_normalisation,[status(thm)],[c_6960,c_6716]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_21,plain,
% 3.15/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.15/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.15/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_561,plain,
% 3.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.15/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.15/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.15/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.15/0.99      | k2_funct_1(sK2) != X0
% 3.15/0.99      | sK0 != X1
% 3.15/0.99      | sK1 != k1_xboole_0 ),
% 3.15/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_562,plain,
% 3.15/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.15/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.15/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.15/0.99      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.15/0.99      | sK1 != k1_xboole_0 ),
% 3.15/0.99      inference(unflattening,[status(thm)],[c_561]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1325,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.15/0.99      | sK1 != k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.15/0.99      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_1557,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.15/0.99      | sK1 != k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.15/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_1325,c_4]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2063,plain,
% 3.15/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.15/0.99      | sK1 != k1_xboole_0
% 3.15/0.99      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.15/0.99      inference(global_propositional_subsumption,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_1557,c_38,c_40,c_1665,c_1744]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_2064,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.15/0.99      | sK1 != k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.15/0.99      inference(renaming,[status(thm)],[c_2063]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6631,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.15/0.99      | k1_xboole_0 != k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6604,c_2064]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6668,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.15/0.99      inference(equality_resolution_simp,[status(thm)],[c_6631]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6672,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6668,c_4]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6718,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.15/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_6709,c_6672]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_6802,plain,
% 3.15/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.15/0.99      inference(backward_subsumption_resolution,
% 3.15/0.99                [status(thm)],
% 3.15/0.99                [c_6800,c_6718]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_7819,plain,
% 3.15/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.15/0.99      inference(demodulation,[status(thm)],[c_7816,c_6802]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_108,plain,
% 3.15/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_5,plain,
% 3.15/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.15/0.99      | k1_xboole_0 = X1
% 3.15/0.99      | k1_xboole_0 = X0 ),
% 3.15/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(c_107,plain,
% 3.15/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.15/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.15/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.15/0.99  
% 3.15/0.99  cnf(contradiction,plain,
% 3.15/0.99      ( $false ),
% 3.15/0.99      inference(minisat,[status(thm)],[c_7819,c_108,c_107]) ).
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.15/0.99  
% 3.15/0.99  ------                               Statistics
% 3.15/0.99  
% 3.15/0.99  ------ General
% 3.15/0.99  
% 3.15/0.99  abstr_ref_over_cycles:                  0
% 3.15/0.99  abstr_ref_under_cycles:                 0
% 3.15/0.99  gc_basic_clause_elim:                   0
% 3.15/0.99  forced_gc_time:                         0
% 3.15/0.99  parsing_time:                           0.01
% 3.15/0.99  unif_index_cands_time:                  0.
% 3.15/0.99  unif_index_add_time:                    0.
% 3.15/0.99  orderings_time:                         0.
% 3.15/0.99  out_proof_time:                         0.015
% 3.15/0.99  total_time:                             0.24
% 3.15/0.99  num_of_symbols:                         50
% 3.15/0.99  num_of_terms:                           5693
% 3.15/0.99  
% 3.15/0.99  ------ Preprocessing
% 3.15/0.99  
% 3.15/0.99  num_of_splits:                          0
% 3.15/0.99  num_of_split_atoms:                     0
% 3.15/0.99  num_of_reused_defs:                     0
% 3.15/0.99  num_eq_ax_congr_red:                    5
% 3.15/0.99  num_of_sem_filtered_clauses:            1
% 3.15/0.99  num_of_subtypes:                        0
% 3.15/0.99  monotx_restored_types:                  0
% 3.15/0.99  sat_num_of_epr_types:                   0
% 3.15/0.99  sat_num_of_non_cyclic_types:            0
% 3.15/0.99  sat_guarded_non_collapsed_types:        0
% 3.15/0.99  num_pure_diseq_elim:                    0
% 3.15/0.99  simp_replaced_by:                       0
% 3.15/0.99  res_preprocessed:                       139
% 3.15/0.99  prep_upred:                             0
% 3.15/0.99  prep_unflattend:                        55
% 3.15/0.99  smt_new_axioms:                         0
% 3.15/0.99  pred_elim_cands:                        7
% 3.15/0.99  pred_elim:                              3
% 3.15/0.99  pred_elim_cl:                           -2
% 3.15/0.99  pred_elim_cycles:                       4
% 3.15/0.99  merged_defs:                            0
% 3.15/0.99  merged_defs_ncl:                        0
% 3.15/0.99  bin_hyper_res:                          0
% 3.15/0.99  prep_cycles:                            3
% 3.15/0.99  pred_elim_time:                         0.01
% 3.15/0.99  splitting_time:                         0.
% 3.15/0.99  sem_filter_time:                        0.
% 3.15/0.99  monotx_time:                            0.
% 3.15/0.99  subtype_inf_time:                       0.
% 3.15/0.99  
% 3.15/0.99  ------ Problem properties
% 3.15/0.99  
% 3.15/0.99  clauses:                                38
% 3.15/0.99  conjectures:                            3
% 3.15/0.99  epr:                                    3
% 3.15/0.99  horn:                                   32
% 3.15/0.99  ground:                                 15
% 3.15/0.99  unary:                                  10
% 3.15/0.99  binary:                                 6
% 3.15/0.99  lits:                                   107
% 3.15/0.99  lits_eq:                                47
% 3.15/0.99  fd_pure:                                0
% 3.15/0.99  fd_pseudo:                              0
% 3.15/0.99  fd_cond:                                3
% 3.15/0.99  fd_pseudo_cond:                         1
% 3.15/0.99  ac_symbols:                             0
% 3.15/0.99  
% 3.15/0.99  ------ Propositional Solver
% 3.15/0.99  
% 3.15/0.99  prop_solver_calls:                      24
% 3.15/0.99  prop_fast_solver_calls:                 1187
% 3.15/0.99  smt_solver_calls:                       0
% 3.15/0.99  smt_fast_solver_calls:                  0
% 3.15/0.99  prop_num_of_clauses:                    2801
% 3.15/0.99  prop_preprocess_simplified:             8184
% 3.15/0.99  prop_fo_subsumed:                       49
% 3.15/0.99  prop_solver_time:                       0.
% 3.15/0.99  smt_solver_time:                        0.
% 3.15/0.99  smt_fast_solver_time:                   0.
% 3.15/0.99  prop_fast_solver_time:                  0.
% 3.15/0.99  prop_unsat_core_time:                   0.
% 3.15/0.99  
% 3.15/0.99  ------ QBF
% 3.15/0.99  
% 3.15/0.99  qbf_q_res:                              0
% 3.15/0.99  qbf_num_tautologies:                    0
% 3.15/0.99  qbf_prep_cycles:                        0
% 3.15/0.99  
% 3.15/0.99  ------ BMC1
% 3.15/0.99  
% 3.15/0.99  bmc1_current_bound:                     -1
% 3.15/0.99  bmc1_last_solved_bound:                 -1
% 3.15/0.99  bmc1_unsat_core_size:                   -1
% 3.15/0.99  bmc1_unsat_core_parents_size:           -1
% 3.15/0.99  bmc1_merge_next_fun:                    0
% 3.15/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.15/0.99  
% 3.15/0.99  ------ Instantiation
% 3.15/0.99  
% 3.15/0.99  inst_num_of_clauses:                    1030
% 3.15/0.99  inst_num_in_passive:                    598
% 3.15/0.99  inst_num_in_active:                     356
% 3.15/0.99  inst_num_in_unprocessed:                77
% 3.15/0.99  inst_num_of_loops:                      540
% 3.15/0.99  inst_num_of_learning_restarts:          0
% 3.15/0.99  inst_num_moves_active_passive:          182
% 3.15/0.99  inst_lit_activity:                      0
% 3.15/0.99  inst_lit_activity_moves:                0
% 3.15/0.99  inst_num_tautologies:                   0
% 3.15/0.99  inst_num_prop_implied:                  0
% 3.15/0.99  inst_num_existing_simplified:           0
% 3.15/0.99  inst_num_eq_res_simplified:             0
% 3.15/0.99  inst_num_child_elim:                    0
% 3.15/0.99  inst_num_of_dismatching_blockings:      391
% 3.15/0.99  inst_num_of_non_proper_insts:           946
% 3.15/0.99  inst_num_of_duplicates:                 0
% 3.15/0.99  inst_inst_num_from_inst_to_res:         0
% 3.15/0.99  inst_dismatching_checking_time:         0.
% 3.15/0.99  
% 3.15/0.99  ------ Resolution
% 3.15/0.99  
% 3.15/0.99  res_num_of_clauses:                     0
% 3.15/0.99  res_num_in_passive:                     0
% 3.15/0.99  res_num_in_active:                      0
% 3.15/0.99  res_num_of_loops:                       142
% 3.15/0.99  res_forward_subset_subsumed:            36
% 3.15/0.99  res_backward_subset_subsumed:           2
% 3.15/0.99  res_forward_subsumed:                   0
% 3.15/0.99  res_backward_subsumed:                  0
% 3.15/0.99  res_forward_subsumption_resolution:     6
% 3.15/0.99  res_backward_subsumption_resolution:    0
% 3.15/0.99  res_clause_to_clause_subsumption:       300
% 3.15/0.99  res_orphan_elimination:                 0
% 3.15/0.99  res_tautology_del:                      72
% 3.15/0.99  res_num_eq_res_simplified:              0
% 3.15/0.99  res_num_sel_changes:                    0
% 3.15/0.99  res_moves_from_active_to_pass:          0
% 3.15/0.99  
% 3.15/0.99  ------ Superposition
% 3.15/0.99  
% 3.15/0.99  sup_time_total:                         0.
% 3.15/0.99  sup_time_generating:                    0.
% 3.15/0.99  sup_time_sim_full:                      0.
% 3.15/0.99  sup_time_sim_immed:                     0.
% 3.15/0.99  
% 3.15/0.99  sup_num_of_clauses:                     90
% 3.15/0.99  sup_num_in_active:                      58
% 3.15/0.99  sup_num_in_passive:                     32
% 3.15/0.99  sup_num_of_loops:                       107
% 3.15/0.99  sup_fw_superposition:                   88
% 3.15/0.99  sup_bw_superposition:                   47
% 3.15/0.99  sup_immediate_simplified:               118
% 3.15/0.99  sup_given_eliminated:                   0
% 3.15/0.99  comparisons_done:                       0
% 3.15/0.99  comparisons_avoided:                    16
% 3.15/0.99  
% 3.15/0.99  ------ Simplifications
% 3.15/0.99  
% 3.15/0.99  
% 3.15/0.99  sim_fw_subset_subsumed:                 23
% 3.15/0.99  sim_bw_subset_subsumed:                 5
% 3.15/0.99  sim_fw_subsumed:                        21
% 3.15/0.99  sim_bw_subsumed:                        4
% 3.15/0.99  sim_fw_subsumption_res:                 2
% 3.15/0.99  sim_bw_subsumption_res:                 4
% 3.15/0.99  sim_tautology_del:                      6
% 3.15/0.99  sim_eq_tautology_del:                   12
% 3.15/0.99  sim_eq_res_simp:                        7
% 3.15/0.99  sim_fw_demodulated:                     32
% 3.15/0.99  sim_bw_demodulated:                     59
% 3.15/0.99  sim_light_normalised:                   43
% 3.15/0.99  sim_joinable_taut:                      0
% 3.15/0.99  sim_joinable_simp:                      0
% 3.15/0.99  sim_ac_normalised:                      0
% 3.15/0.99  sim_smt_subsumption:                    0
% 3.15/0.99  
%------------------------------------------------------------------------------
