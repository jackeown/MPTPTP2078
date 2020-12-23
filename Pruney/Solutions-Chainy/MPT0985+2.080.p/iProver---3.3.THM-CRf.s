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
% DateTime   : Thu Dec  3 12:02:36 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  196 (4293 expanded)
%              Number of clauses        :  125 (1331 expanded)
%              Number of leaves         :   16 ( 833 expanded)
%              Depth                    :   26
%              Number of atoms          :  588 (23277 expanded)
%              Number of equality atoms :  281 (4706 expanded)
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
    inference(ennf_transformation,[],[f16])).

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

fof(f45,plain,(
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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f46])).

fof(f80,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_661,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_34])).

cnf(c_1712,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1716,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4068,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1712,c_1716])).

cnf(c_4261,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_661,c_4068])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1715,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3203,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1712,c_1715])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3215,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3203,c_32])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_428,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_429,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_431,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_36])).

cnf(c_1710,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1996,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2009,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_36,c_34,c_429,c_1996])).

cnf(c_3239,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3215,c_2009])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1713,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3321,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3239,c_1713])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_442,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_443,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_445,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_36])).

cnf(c_1709,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_2005,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1709,c_36,c_34,c_443,c_1996])).

cnf(c_3322,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3321,c_2005])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1975,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1976,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1978,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1979,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1978])).

cnf(c_1997,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(c_3915,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3322,c_37,c_39,c_1976,c_1979,c_1997])).

cnf(c_4266,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_3915])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_669,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_670,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_682,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_670,c_17])).

cnf(c_1699,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_671,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_2083,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1699,c_37,c_39,c_671,c_1976,c_1979,c_1997])).

cnf(c_2084,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2083])).

cnf(c_2087,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2084,c_2005,c_2009])).

cnf(c_3238,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3215,c_2087])).

cnf(c_3242,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3238])).

cnf(c_4267,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_3242])).

cnf(c_4280,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4266,c_4267])).

cnf(c_4422,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_3915])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4497,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4422,c_5])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_587,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_1703,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_1897,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1703,c_5])).

cnf(c_2265,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1897,c_37,c_39,c_1976,c_1997])).

cnf(c_2266,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2265])).

cnf(c_4431,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_2266])).

cnf(c_4464,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4431])).

cnf(c_4468,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4464,c_5])).

cnf(c_4500,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4497,c_4468])).

cnf(c_4428,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4280,c_3215])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_relat_1(X2) != k1_xboole_0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_518,c_17])).

cnf(c_1706,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1876,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1706,c_4])).

cnf(c_5642,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4428,c_1876])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2330,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2333,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2330])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2338,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2339,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_2341,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2339])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2687,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2688,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2687])).

cnf(c_2690,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2688])).

cnf(c_4437,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_1712])).

cnf(c_4442,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4437,c_4])).

cnf(c_5814,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5642,c_2333,c_2341,c_2690,c_4442])).

cnf(c_1721,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4726,plain,
    ( r1_tarski(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4497,c_1721])).

cnf(c_6723,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4726,c_5814])).

cnf(c_1726,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6726,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6723,c_1726])).

cnf(c_1724,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7278,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6726,c_1724])).

cnf(c_7409,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4500,c_5814,c_7278])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1723,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4064,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1723,c_1716])).

cnf(c_7410,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7409,c_4064])).

cnf(c_5675,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X0)
    | k1_relat_1(X1) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5677,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5675])).

cnf(c_5360,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5362,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5360])).

cnf(c_1986,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1990,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1986])).

cnf(c_1985,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_11])).

cnf(c_464,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_7412,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(grounding,[status(thm)],[c_1986:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_7413,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_relat_1(k1_xboole_0) ),
    inference(grounding,[status(thm)],[c_1985:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7410,c_5677,c_5362,c_1990,c_7412,c_7413,c_464])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:41:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.05/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/0.98  
% 3.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/0.98  
% 3.05/0.98  ------  iProver source info
% 3.05/0.98  
% 3.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/0.98  git: non_committed_changes: false
% 3.05/0.98  git: last_make_outside_of_git: false
% 3.05/0.98  
% 3.05/0.98  ------ 
% 3.05/0.98  
% 3.05/0.98  ------ Input Options
% 3.05/0.98  
% 3.05/0.98  --out_options                           all
% 3.05/0.98  --tptp_safe_out                         true
% 3.05/0.98  --problem_path                          ""
% 3.05/0.98  --include_path                          ""
% 3.05/0.98  --clausifier                            res/vclausify_rel
% 3.05/0.98  --clausifier_options                    --mode clausify
% 3.05/0.98  --stdin                                 false
% 3.05/0.98  --stats_out                             all
% 3.05/0.98  
% 3.05/0.98  ------ General Options
% 3.05/0.98  
% 3.05/0.98  --fof                                   false
% 3.05/0.98  --time_out_real                         305.
% 3.05/0.98  --time_out_virtual                      -1.
% 3.05/0.98  --symbol_type_check                     false
% 3.05/0.98  --clausify_out                          false
% 3.05/0.98  --sig_cnt_out                           false
% 3.05/0.98  --trig_cnt_out                          false
% 3.05/0.98  --trig_cnt_out_tolerance                1.
% 3.05/0.98  --trig_cnt_out_sk_spl                   false
% 3.05/0.98  --abstr_cl_out                          false
% 3.05/0.98  
% 3.05/0.98  ------ Global Options
% 3.05/0.98  
% 3.05/0.98  --schedule                              default
% 3.05/0.98  --add_important_lit                     false
% 3.05/0.98  --prop_solver_per_cl                    1000
% 3.05/0.98  --min_unsat_core                        false
% 3.05/0.98  --soft_assumptions                      false
% 3.05/0.98  --soft_lemma_size                       3
% 3.05/0.98  --prop_impl_unit_size                   0
% 3.05/0.98  --prop_impl_unit                        []
% 3.05/0.98  --share_sel_clauses                     true
% 3.05/0.98  --reset_solvers                         false
% 3.05/0.98  --bc_imp_inh                            [conj_cone]
% 3.05/0.98  --conj_cone_tolerance                   3.
% 3.05/0.98  --extra_neg_conj                        none
% 3.05/0.98  --large_theory_mode                     true
% 3.05/0.98  --prolific_symb_bound                   200
% 3.05/0.98  --lt_threshold                          2000
% 3.05/0.98  --clause_weak_htbl                      true
% 3.05/0.98  --gc_record_bc_elim                     false
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing Options
% 3.05/0.98  
% 3.05/0.98  --preprocessing_flag                    true
% 3.05/0.98  --time_out_prep_mult                    0.1
% 3.05/0.98  --splitting_mode                        input
% 3.05/0.98  --splitting_grd                         true
% 3.05/0.98  --splitting_cvd                         false
% 3.05/0.98  --splitting_cvd_svl                     false
% 3.05/0.98  --splitting_nvd                         32
% 3.05/0.98  --sub_typing                            true
% 3.05/0.98  --prep_gs_sim                           true
% 3.05/0.98  --prep_unflatten                        true
% 3.05/0.98  --prep_res_sim                          true
% 3.05/0.98  --prep_upred                            true
% 3.05/0.98  --prep_sem_filter                       exhaustive
% 3.05/0.98  --prep_sem_filter_out                   false
% 3.05/0.98  --pred_elim                             true
% 3.05/0.98  --res_sim_input                         true
% 3.05/0.98  --eq_ax_congr_red                       true
% 3.05/0.98  --pure_diseq_elim                       true
% 3.05/0.98  --brand_transform                       false
% 3.05/0.98  --non_eq_to_eq                          false
% 3.05/0.98  --prep_def_merge                        true
% 3.05/0.98  --prep_def_merge_prop_impl              false
% 3.05/0.98  --prep_def_merge_mbd                    true
% 3.05/0.98  --prep_def_merge_tr_red                 false
% 3.05/0.98  --prep_def_merge_tr_cl                  false
% 3.05/0.98  --smt_preprocessing                     true
% 3.05/0.98  --smt_ac_axioms                         fast
% 3.05/0.98  --preprocessed_out                      false
% 3.05/0.98  --preprocessed_stats                    false
% 3.05/0.98  
% 3.05/0.98  ------ Abstraction refinement Options
% 3.05/0.98  
% 3.05/0.98  --abstr_ref                             []
% 3.05/0.98  --abstr_ref_prep                        false
% 3.05/0.98  --abstr_ref_until_sat                   false
% 3.05/0.98  --abstr_ref_sig_restrict                funpre
% 3.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.98  --abstr_ref_under                       []
% 3.05/0.98  
% 3.05/0.98  ------ SAT Options
% 3.05/0.98  
% 3.05/0.98  --sat_mode                              false
% 3.05/0.98  --sat_fm_restart_options                ""
% 3.05/0.98  --sat_gr_def                            false
% 3.05/0.98  --sat_epr_types                         true
% 3.05/0.98  --sat_non_cyclic_types                  false
% 3.05/0.98  --sat_finite_models                     false
% 3.05/0.98  --sat_fm_lemmas                         false
% 3.05/0.98  --sat_fm_prep                           false
% 3.05/0.98  --sat_fm_uc_incr                        true
% 3.05/0.98  --sat_out_model                         small
% 3.05/0.98  --sat_out_clauses                       false
% 3.05/0.98  
% 3.05/0.98  ------ QBF Options
% 3.05/0.98  
% 3.05/0.98  --qbf_mode                              false
% 3.05/0.98  --qbf_elim_univ                         false
% 3.05/0.98  --qbf_dom_inst                          none
% 3.05/0.98  --qbf_dom_pre_inst                      false
% 3.05/0.98  --qbf_sk_in                             false
% 3.05/0.98  --qbf_pred_elim                         true
% 3.05/0.98  --qbf_split                             512
% 3.05/0.98  
% 3.05/0.98  ------ BMC1 Options
% 3.05/0.98  
% 3.05/0.98  --bmc1_incremental                      false
% 3.05/0.98  --bmc1_axioms                           reachable_all
% 3.05/0.98  --bmc1_min_bound                        0
% 3.05/0.98  --bmc1_max_bound                        -1
% 3.05/0.98  --bmc1_max_bound_default                -1
% 3.05/0.98  --bmc1_symbol_reachability              true
% 3.05/0.98  --bmc1_property_lemmas                  false
% 3.05/0.98  --bmc1_k_induction                      false
% 3.05/0.98  --bmc1_non_equiv_states                 false
% 3.05/0.98  --bmc1_deadlock                         false
% 3.05/0.98  --bmc1_ucm                              false
% 3.05/0.98  --bmc1_add_unsat_core                   none
% 3.05/0.99  --bmc1_unsat_core_children              false
% 3.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.99  --bmc1_out_stat                         full
% 3.05/0.99  --bmc1_ground_init                      false
% 3.05/0.99  --bmc1_pre_inst_next_state              false
% 3.05/0.99  --bmc1_pre_inst_state                   false
% 3.05/0.99  --bmc1_pre_inst_reach_state             false
% 3.05/0.99  --bmc1_out_unsat_core                   false
% 3.05/0.99  --bmc1_aig_witness_out                  false
% 3.05/0.99  --bmc1_verbose                          false
% 3.05/0.99  --bmc1_dump_clauses_tptp                false
% 3.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.99  --bmc1_dump_file                        -
% 3.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.99  --bmc1_ucm_extend_mode                  1
% 3.05/0.99  --bmc1_ucm_init_mode                    2
% 3.05/0.99  --bmc1_ucm_cone_mode                    none
% 3.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.99  --bmc1_ucm_relax_model                  4
% 3.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.99  --bmc1_ucm_layered_model                none
% 3.05/0.99  --bmc1_ucm_max_lemma_size               10
% 3.05/0.99  
% 3.05/0.99  ------ AIG Options
% 3.05/0.99  
% 3.05/0.99  --aig_mode                              false
% 3.05/0.99  
% 3.05/0.99  ------ Instantiation Options
% 3.05/0.99  
% 3.05/0.99  --instantiation_flag                    true
% 3.05/0.99  --inst_sos_flag                         false
% 3.05/0.99  --inst_sos_phase                        true
% 3.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel_side                     num_symb
% 3.05/0.99  --inst_solver_per_active                1400
% 3.05/0.99  --inst_solver_calls_frac                1.
% 3.05/0.99  --inst_passive_queue_type               priority_queues
% 3.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.99  --inst_passive_queues_freq              [25;2]
% 3.05/0.99  --inst_dismatching                      true
% 3.05/0.99  --inst_eager_unprocessed_to_passive     true
% 3.05/0.99  --inst_prop_sim_given                   true
% 3.05/0.99  --inst_prop_sim_new                     false
% 3.05/0.99  --inst_subs_new                         false
% 3.05/0.99  --inst_eq_res_simp                      false
% 3.05/0.99  --inst_subs_given                       false
% 3.05/0.99  --inst_orphan_elimination               true
% 3.05/0.99  --inst_learning_loop_flag               true
% 3.05/0.99  --inst_learning_start                   3000
% 3.05/0.99  --inst_learning_factor                  2
% 3.05/0.99  --inst_start_prop_sim_after_learn       3
% 3.05/0.99  --inst_sel_renew                        solver
% 3.05/0.99  --inst_lit_activity_flag                true
% 3.05/0.99  --inst_restr_to_given                   false
% 3.05/0.99  --inst_activity_threshold               500
% 3.05/0.99  --inst_out_proof                        true
% 3.05/0.99  
% 3.05/0.99  ------ Resolution Options
% 3.05/0.99  
% 3.05/0.99  --resolution_flag                       true
% 3.05/0.99  --res_lit_sel                           adaptive
% 3.05/0.99  --res_lit_sel_side                      none
% 3.05/0.99  --res_ordering                          kbo
% 3.05/0.99  --res_to_prop_solver                    active
% 3.05/0.99  --res_prop_simpl_new                    false
% 3.05/0.99  --res_prop_simpl_given                  true
% 3.05/0.99  --res_passive_queue_type                priority_queues
% 3.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.99  --res_passive_queues_freq               [15;5]
% 3.05/0.99  --res_forward_subs                      full
% 3.05/0.99  --res_backward_subs                     full
% 3.05/0.99  --res_forward_subs_resolution           true
% 3.05/0.99  --res_backward_subs_resolution          true
% 3.05/0.99  --res_orphan_elimination                true
% 3.05/0.99  --res_time_limit                        2.
% 3.05/0.99  --res_out_proof                         true
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Options
% 3.05/0.99  
% 3.05/0.99  --superposition_flag                    true
% 3.05/0.99  --sup_passive_queue_type                priority_queues
% 3.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.99  --demod_completeness_check              fast
% 3.05/0.99  --demod_use_ground                      true
% 3.05/0.99  --sup_to_prop_solver                    passive
% 3.05/0.99  --sup_prop_simpl_new                    true
% 3.05/0.99  --sup_prop_simpl_given                  true
% 3.05/0.99  --sup_fun_splitting                     false
% 3.05/0.99  --sup_smt_interval                      50000
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Simplification Setup
% 3.05/0.99  
% 3.05/0.99  --sup_indices_passive                   []
% 3.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_full_bw                           [BwDemod]
% 3.05/0.99  --sup_immed_triv                        [TrivRules]
% 3.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_immed_bw_main                     []
% 3.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  
% 3.05/0.99  ------ Combination Options
% 3.05/0.99  
% 3.05/0.99  --comb_res_mult                         3
% 3.05/0.99  --comb_sup_mult                         2
% 3.05/0.99  --comb_inst_mult                        10
% 3.05/0.99  
% 3.05/0.99  ------ Debug Options
% 3.05/0.99  
% 3.05/0.99  --dbg_backtrace                         false
% 3.05/0.99  --dbg_dump_prop_clauses                 false
% 3.05/0.99  --dbg_dump_prop_clauses_file            -
% 3.05/0.99  --dbg_out_stat                          false
% 3.05/0.99  ------ Parsing...
% 3.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/0.99  ------ Proving...
% 3.05/0.99  ------ Problem Properties 
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  clauses                                 34
% 3.05/0.99  conjectures                             3
% 3.05/0.99  EPR                                     4
% 3.05/0.99  Horn                                    29
% 3.05/0.99  unary                                   9
% 3.05/0.99  binary                                  9
% 3.05/0.99  lits                                    88
% 3.05/0.99  lits eq                                 36
% 3.05/0.99  fd_pure                                 0
% 3.05/0.99  fd_pseudo                               0
% 3.05/0.99  fd_cond                                 2
% 3.05/0.99  fd_pseudo_cond                          1
% 3.05/0.99  AC symbols                              0
% 3.05/0.99  
% 3.05/0.99  ------ Schedule dynamic 5 is on 
% 3.05/0.99  
% 3.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  ------ 
% 3.05/0.99  Current options:
% 3.05/0.99  ------ 
% 3.05/0.99  
% 3.05/0.99  ------ Input Options
% 3.05/0.99  
% 3.05/0.99  --out_options                           all
% 3.05/0.99  --tptp_safe_out                         true
% 3.05/0.99  --problem_path                          ""
% 3.05/0.99  --include_path                          ""
% 3.05/0.99  --clausifier                            res/vclausify_rel
% 3.05/0.99  --clausifier_options                    --mode clausify
% 3.05/0.99  --stdin                                 false
% 3.05/0.99  --stats_out                             all
% 3.05/0.99  
% 3.05/0.99  ------ General Options
% 3.05/0.99  
% 3.05/0.99  --fof                                   false
% 3.05/0.99  --time_out_real                         305.
% 3.05/0.99  --time_out_virtual                      -1.
% 3.05/0.99  --symbol_type_check                     false
% 3.05/0.99  --clausify_out                          false
% 3.05/0.99  --sig_cnt_out                           false
% 3.05/0.99  --trig_cnt_out                          false
% 3.05/0.99  --trig_cnt_out_tolerance                1.
% 3.05/0.99  --trig_cnt_out_sk_spl                   false
% 3.05/0.99  --abstr_cl_out                          false
% 3.05/0.99  
% 3.05/0.99  ------ Global Options
% 3.05/0.99  
% 3.05/0.99  --schedule                              default
% 3.05/0.99  --add_important_lit                     false
% 3.05/0.99  --prop_solver_per_cl                    1000
% 3.05/0.99  --min_unsat_core                        false
% 3.05/0.99  --soft_assumptions                      false
% 3.05/0.99  --soft_lemma_size                       3
% 3.05/0.99  --prop_impl_unit_size                   0
% 3.05/0.99  --prop_impl_unit                        []
% 3.05/0.99  --share_sel_clauses                     true
% 3.05/0.99  --reset_solvers                         false
% 3.05/0.99  --bc_imp_inh                            [conj_cone]
% 3.05/0.99  --conj_cone_tolerance                   3.
% 3.05/0.99  --extra_neg_conj                        none
% 3.05/0.99  --large_theory_mode                     true
% 3.05/0.99  --prolific_symb_bound                   200
% 3.05/0.99  --lt_threshold                          2000
% 3.05/0.99  --clause_weak_htbl                      true
% 3.05/0.99  --gc_record_bc_elim                     false
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing Options
% 3.05/0.99  
% 3.05/0.99  --preprocessing_flag                    true
% 3.05/0.99  --time_out_prep_mult                    0.1
% 3.05/0.99  --splitting_mode                        input
% 3.05/0.99  --splitting_grd                         true
% 3.05/0.99  --splitting_cvd                         false
% 3.05/0.99  --splitting_cvd_svl                     false
% 3.05/0.99  --splitting_nvd                         32
% 3.05/0.99  --sub_typing                            true
% 3.05/0.99  --prep_gs_sim                           true
% 3.05/0.99  --prep_unflatten                        true
% 3.05/0.99  --prep_res_sim                          true
% 3.05/0.99  --prep_upred                            true
% 3.05/0.99  --prep_sem_filter                       exhaustive
% 3.05/0.99  --prep_sem_filter_out                   false
% 3.05/0.99  --pred_elim                             true
% 3.05/0.99  --res_sim_input                         true
% 3.05/0.99  --eq_ax_congr_red                       true
% 3.05/0.99  --pure_diseq_elim                       true
% 3.05/0.99  --brand_transform                       false
% 3.05/0.99  --non_eq_to_eq                          false
% 3.05/0.99  --prep_def_merge                        true
% 3.05/0.99  --prep_def_merge_prop_impl              false
% 3.05/0.99  --prep_def_merge_mbd                    true
% 3.05/0.99  --prep_def_merge_tr_red                 false
% 3.05/0.99  --prep_def_merge_tr_cl                  false
% 3.05/0.99  --smt_preprocessing                     true
% 3.05/0.99  --smt_ac_axioms                         fast
% 3.05/0.99  --preprocessed_out                      false
% 3.05/0.99  --preprocessed_stats                    false
% 3.05/0.99  
% 3.05/0.99  ------ Abstraction refinement Options
% 3.05/0.99  
% 3.05/0.99  --abstr_ref                             []
% 3.05/0.99  --abstr_ref_prep                        false
% 3.05/0.99  --abstr_ref_until_sat                   false
% 3.05/0.99  --abstr_ref_sig_restrict                funpre
% 3.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.99  --abstr_ref_under                       []
% 3.05/0.99  
% 3.05/0.99  ------ SAT Options
% 3.05/0.99  
% 3.05/0.99  --sat_mode                              false
% 3.05/0.99  --sat_fm_restart_options                ""
% 3.05/0.99  --sat_gr_def                            false
% 3.05/0.99  --sat_epr_types                         true
% 3.05/0.99  --sat_non_cyclic_types                  false
% 3.05/0.99  --sat_finite_models                     false
% 3.05/0.99  --sat_fm_lemmas                         false
% 3.05/0.99  --sat_fm_prep                           false
% 3.05/0.99  --sat_fm_uc_incr                        true
% 3.05/0.99  --sat_out_model                         small
% 3.05/0.99  --sat_out_clauses                       false
% 3.05/0.99  
% 3.05/0.99  ------ QBF Options
% 3.05/0.99  
% 3.05/0.99  --qbf_mode                              false
% 3.05/0.99  --qbf_elim_univ                         false
% 3.05/0.99  --qbf_dom_inst                          none
% 3.05/0.99  --qbf_dom_pre_inst                      false
% 3.05/0.99  --qbf_sk_in                             false
% 3.05/0.99  --qbf_pred_elim                         true
% 3.05/0.99  --qbf_split                             512
% 3.05/0.99  
% 3.05/0.99  ------ BMC1 Options
% 3.05/0.99  
% 3.05/0.99  --bmc1_incremental                      false
% 3.05/0.99  --bmc1_axioms                           reachable_all
% 3.05/0.99  --bmc1_min_bound                        0
% 3.05/0.99  --bmc1_max_bound                        -1
% 3.05/0.99  --bmc1_max_bound_default                -1
% 3.05/0.99  --bmc1_symbol_reachability              true
% 3.05/0.99  --bmc1_property_lemmas                  false
% 3.05/0.99  --bmc1_k_induction                      false
% 3.05/0.99  --bmc1_non_equiv_states                 false
% 3.05/0.99  --bmc1_deadlock                         false
% 3.05/0.99  --bmc1_ucm                              false
% 3.05/0.99  --bmc1_add_unsat_core                   none
% 3.05/0.99  --bmc1_unsat_core_children              false
% 3.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.99  --bmc1_out_stat                         full
% 3.05/0.99  --bmc1_ground_init                      false
% 3.05/0.99  --bmc1_pre_inst_next_state              false
% 3.05/0.99  --bmc1_pre_inst_state                   false
% 3.05/0.99  --bmc1_pre_inst_reach_state             false
% 3.05/0.99  --bmc1_out_unsat_core                   false
% 3.05/0.99  --bmc1_aig_witness_out                  false
% 3.05/0.99  --bmc1_verbose                          false
% 3.05/0.99  --bmc1_dump_clauses_tptp                false
% 3.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.99  --bmc1_dump_file                        -
% 3.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.99  --bmc1_ucm_extend_mode                  1
% 3.05/0.99  --bmc1_ucm_init_mode                    2
% 3.05/0.99  --bmc1_ucm_cone_mode                    none
% 3.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.99  --bmc1_ucm_relax_model                  4
% 3.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.99  --bmc1_ucm_layered_model                none
% 3.05/0.99  --bmc1_ucm_max_lemma_size               10
% 3.05/0.99  
% 3.05/0.99  ------ AIG Options
% 3.05/0.99  
% 3.05/0.99  --aig_mode                              false
% 3.05/0.99  
% 3.05/0.99  ------ Instantiation Options
% 3.05/0.99  
% 3.05/0.99  --instantiation_flag                    true
% 3.05/0.99  --inst_sos_flag                         false
% 3.05/0.99  --inst_sos_phase                        true
% 3.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel_side                     none
% 3.05/0.99  --inst_solver_per_active                1400
% 3.05/0.99  --inst_solver_calls_frac                1.
% 3.05/0.99  --inst_passive_queue_type               priority_queues
% 3.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.99  --inst_passive_queues_freq              [25;2]
% 3.05/0.99  --inst_dismatching                      true
% 3.05/0.99  --inst_eager_unprocessed_to_passive     true
% 3.05/0.99  --inst_prop_sim_given                   true
% 3.05/0.99  --inst_prop_sim_new                     false
% 3.05/0.99  --inst_subs_new                         false
% 3.05/0.99  --inst_eq_res_simp                      false
% 3.05/0.99  --inst_subs_given                       false
% 3.05/0.99  --inst_orphan_elimination               true
% 3.05/0.99  --inst_learning_loop_flag               true
% 3.05/0.99  --inst_learning_start                   3000
% 3.05/0.99  --inst_learning_factor                  2
% 3.05/0.99  --inst_start_prop_sim_after_learn       3
% 3.05/0.99  --inst_sel_renew                        solver
% 3.05/0.99  --inst_lit_activity_flag                true
% 3.05/0.99  --inst_restr_to_given                   false
% 3.05/0.99  --inst_activity_threshold               500
% 3.05/0.99  --inst_out_proof                        true
% 3.05/0.99  
% 3.05/0.99  ------ Resolution Options
% 3.05/0.99  
% 3.05/0.99  --resolution_flag                       false
% 3.05/0.99  --res_lit_sel                           adaptive
% 3.05/0.99  --res_lit_sel_side                      none
% 3.05/0.99  --res_ordering                          kbo
% 3.05/0.99  --res_to_prop_solver                    active
% 3.05/0.99  --res_prop_simpl_new                    false
% 3.05/0.99  --res_prop_simpl_given                  true
% 3.05/0.99  --res_passive_queue_type                priority_queues
% 3.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.99  --res_passive_queues_freq               [15;5]
% 3.05/0.99  --res_forward_subs                      full
% 3.05/0.99  --res_backward_subs                     full
% 3.05/0.99  --res_forward_subs_resolution           true
% 3.05/0.99  --res_backward_subs_resolution          true
% 3.05/0.99  --res_orphan_elimination                true
% 3.05/0.99  --res_time_limit                        2.
% 3.05/0.99  --res_out_proof                         true
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Options
% 3.05/0.99  
% 3.05/0.99  --superposition_flag                    true
% 3.05/0.99  --sup_passive_queue_type                priority_queues
% 3.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.99  --demod_completeness_check              fast
% 3.05/0.99  --demod_use_ground                      true
% 3.05/0.99  --sup_to_prop_solver                    passive
% 3.05/0.99  --sup_prop_simpl_new                    true
% 3.05/0.99  --sup_prop_simpl_given                  true
% 3.05/0.99  --sup_fun_splitting                     false
% 3.05/0.99  --sup_smt_interval                      50000
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Simplification Setup
% 3.05/0.99  
% 3.05/0.99  --sup_indices_passive                   []
% 3.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_full_bw                           [BwDemod]
% 3.05/0.99  --sup_immed_triv                        [TrivRules]
% 3.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_immed_bw_main                     []
% 3.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  
% 3.05/0.99  ------ Combination Options
% 3.05/0.99  
% 3.05/0.99  --comb_res_mult                         3
% 3.05/0.99  --comb_sup_mult                         2
% 3.05/0.99  --comb_inst_mult                        10
% 3.05/0.99  
% 3.05/0.99  ------ Debug Options
% 3.05/0.99  
% 3.05/0.99  --dbg_backtrace                         false
% 3.05/0.99  --dbg_dump_prop_clauses                 false
% 3.05/0.99  --dbg_dump_prop_clauses_file            -
% 3.05/0.99  --dbg_out_stat                          false
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  ------ Proving...
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  % SZS status Theorem for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  fof(f16,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f33,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f16])).
% 3.05/0.99  
% 3.05/0.99  fof(f34,plain,(
% 3.05/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(flattening,[],[f33])).
% 3.05/0.99  
% 3.05/0.99  fof(f45,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(nnf_transformation,[],[f34])).
% 3.05/0.99  
% 3.05/0.99  fof(f70,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f45])).
% 3.05/0.99  
% 3.05/0.99  fof(f18,conjecture,(
% 3.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f19,negated_conjecture,(
% 3.05/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.05/0.99    inference(negated_conjecture,[],[f18])).
% 3.05/0.99  
% 3.05/0.99  fof(f37,plain,(
% 3.05/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.05/0.99    inference(ennf_transformation,[],[f19])).
% 3.05/0.99  
% 3.05/0.99  fof(f38,plain,(
% 3.05/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.05/0.99    inference(flattening,[],[f37])).
% 3.05/0.99  
% 3.05/0.99  fof(f46,plain,(
% 3.05/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f47,plain,(
% 3.05/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f46])).
% 3.05/0.99  
% 3.05/0.99  fof(f80,plain,(
% 3.05/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f81,plain,(
% 3.05/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f13,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f29,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f13])).
% 3.05/0.99  
% 3.05/0.99  fof(f67,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f29])).
% 3.05/0.99  
% 3.05/0.99  fof(f14,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f30,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f14])).
% 3.05/0.99  
% 3.05/0.99  fof(f68,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f30])).
% 3.05/0.99  
% 3.05/0.99  fof(f83,plain,(
% 3.05/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f10,axiom,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f25,plain,(
% 3.05/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f10])).
% 3.05/0.99  
% 3.05/0.99  fof(f26,plain,(
% 3.05/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/0.99    inference(flattening,[],[f25])).
% 3.05/0.99  
% 3.05/0.99  fof(f63,plain,(
% 3.05/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f26])).
% 3.05/0.99  
% 3.05/0.99  fof(f82,plain,(
% 3.05/0.99    v2_funct_1(sK2)),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f79,plain,(
% 3.05/0.99    v1_funct_1(sK2)),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f11,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f27,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f11])).
% 3.05/0.99  
% 3.05/0.99  fof(f65,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f27])).
% 3.05/0.99  
% 3.05/0.99  fof(f17,axiom,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f35,plain,(
% 3.05/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f17])).
% 3.05/0.99  
% 3.05/0.99  fof(f36,plain,(
% 3.05/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/0.99    inference(flattening,[],[f35])).
% 3.05/0.99  
% 3.05/0.99  fof(f78,plain,(
% 3.05/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f36])).
% 3.05/0.99  
% 3.05/0.99  fof(f64,plain,(
% 3.05/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f26])).
% 3.05/0.99  
% 3.05/0.99  fof(f9,axiom,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f23,plain,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f9])).
% 3.05/0.99  
% 3.05/0.99  fof(f24,plain,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/0.99    inference(flattening,[],[f23])).
% 3.05/0.99  
% 3.05/0.99  fof(f62,plain,(
% 3.05/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f24])).
% 3.05/0.99  
% 3.05/0.99  fof(f61,plain,(
% 3.05/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f24])).
% 3.05/0.99  
% 3.05/0.99  fof(f77,plain,(
% 3.05/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f36])).
% 3.05/0.99  
% 3.05/0.99  fof(f84,plain,(
% 3.05/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f3,axiom,(
% 3.05/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f41,plain,(
% 3.05/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.05/0.99    inference(nnf_transformation,[],[f3])).
% 3.05/0.99  
% 3.05/0.99  fof(f42,plain,(
% 3.05/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.05/0.99    inference(flattening,[],[f41])).
% 3.05/0.99  
% 3.05/0.99  fof(f53,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.05/0.99    inference(cnf_transformation,[],[f42])).
% 3.05/0.99  
% 3.05/0.99  fof(f88,plain,(
% 3.05/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.05/0.99    inference(equality_resolution,[],[f53])).
% 3.05/0.99  
% 3.05/0.99  fof(f73,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f45])).
% 3.05/0.99  
% 3.05/0.99  fof(f92,plain,(
% 3.05/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.05/0.99    inference(equality_resolution,[],[f73])).
% 3.05/0.99  
% 3.05/0.99  fof(f74,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f45])).
% 3.05/0.99  
% 3.05/0.99  fof(f91,plain,(
% 3.05/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.05/0.99    inference(equality_resolution,[],[f74])).
% 3.05/0.99  
% 3.05/0.99  fof(f54,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.05/0.99    inference(cnf_transformation,[],[f42])).
% 3.05/0.99  
% 3.05/0.99  fof(f87,plain,(
% 3.05/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.05/0.99    inference(equality_resolution,[],[f54])).
% 3.05/0.99  
% 3.05/0.99  fof(f2,axiom,(
% 3.05/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f51,plain,(
% 3.05/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f2])).
% 3.05/0.99  
% 3.05/0.99  fof(f1,axiom,(
% 3.05/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f39,plain,(
% 3.05/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/0.99    inference(nnf_transformation,[],[f1])).
% 3.05/0.99  
% 3.05/0.99  fof(f40,plain,(
% 3.05/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/0.99    inference(flattening,[],[f39])).
% 3.05/0.99  
% 3.05/0.99  fof(f50,plain,(
% 3.05/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f40])).
% 3.05/0.99  
% 3.05/0.99  fof(f5,axiom,(
% 3.05/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f43,plain,(
% 3.05/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.05/0.99    inference(nnf_transformation,[],[f5])).
% 3.05/0.99  
% 3.05/0.99  fof(f56,plain,(
% 3.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f43])).
% 3.05/0.99  
% 3.05/0.99  fof(f4,axiom,(
% 3.05/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f55,plain,(
% 3.05/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f4])).
% 3.05/0.99  
% 3.05/0.99  fof(f12,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f20,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.05/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.05/0.99  
% 3.05/0.99  fof(f28,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f20])).
% 3.05/0.99  
% 3.05/0.99  fof(f66,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f28])).
% 3.05/0.99  
% 3.05/0.99  fof(f7,axiom,(
% 3.05/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f22,plain,(
% 3.05/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.05/0.99    inference(ennf_transformation,[],[f7])).
% 3.05/0.99  
% 3.05/0.99  fof(f44,plain,(
% 3.05/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.05/0.99    inference(nnf_transformation,[],[f22])).
% 3.05/0.99  
% 3.05/0.99  fof(f58,plain,(
% 3.05/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f44])).
% 3.05/0.99  
% 3.05/0.99  cnf(c_27,plain,
% 3.05/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.05/0.99      | k1_xboole_0 = X2 ),
% 3.05/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_35,negated_conjecture,
% 3.05/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.05/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_658,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.05/0.99      | sK0 != X1
% 3.05/0.99      | sK1 != X2
% 3.05/0.99      | sK2 != X0
% 3.05/0.99      | k1_xboole_0 = X2 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_659,plain,
% 3.05/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.05/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.05/0.99      | k1_xboole_0 = sK1 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_658]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_34,negated_conjecture,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.05/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_661,plain,
% 3.05/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_659,c_34]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1712,plain,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_19,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1716,plain,
% 3.05/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4068,plain,
% 3.05/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_1712,c_1716]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4261,plain,
% 3.05/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_661,c_4068]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_20,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1715,plain,
% 3.05/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3203,plain,
% 3.05/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_1712,c_1715]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_32,negated_conjecture,
% 3.05/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.05/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3215,plain,
% 3.05/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_3203,c_32]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_16,plain,
% 3.05/0.99      ( ~ v2_funct_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_33,negated_conjecture,
% 3.05/0.99      ( v2_funct_1(sK2) ),
% 3.05/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_428,plain,
% 3.05/0.99      ( ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.05/0.99      | sK2 != X0 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_429,plain,
% 3.05/0.99      ( ~ v1_funct_1(sK2)
% 3.05/0.99      | ~ v1_relat_1(sK2)
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_428]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_36,negated_conjecture,
% 3.05/0.99      ( v1_funct_1(sK2) ),
% 3.05/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_431,plain,
% 3.05/0.99      ( ~ v1_relat_1(sK2)
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_429,c_36]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1710,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.05/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_17,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | v1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1996,plain,
% 3.05/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.05/0.99      | v1_relat_1(sK2) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2009,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1710,c_36,c_34,c_429,c_1996]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3239,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_3215,c_2009]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_28,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1713,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top
% 3.05/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3321,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.05/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_3239,c_1713]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_15,plain,
% 3.05/0.99      ( ~ v2_funct_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_442,plain,
% 3.05/0.99      ( ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.05/0.99      | sK2 != X0 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_33]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_443,plain,
% 3.05/0.99      ( ~ v1_funct_1(sK2)
% 3.05/0.99      | ~ v1_relat_1(sK2)
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_442]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_445,plain,
% 3.05/0.99      ( ~ v1_relat_1(sK2)
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_443,c_36]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1709,plain,
% 3.05/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.05/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2005,plain,
% 3.05/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1709,c_36,c_34,c_443,c_1996]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3322,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.05/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_3321,c_2005]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_37,plain,
% 3.05/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_39,plain,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_13,plain,
% 3.05/0.99      ( ~ v1_funct_1(X0)
% 3.05/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.05/0.99      | ~ v1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1975,plain,
% 3.05/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.05/0.99      | ~ v1_funct_1(sK2)
% 3.05/0.99      | ~ v1_relat_1(sK2) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1976,plain,
% 3.05/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.05/0.99      | v1_funct_1(sK2) != iProver_top
% 3.05/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_14,plain,
% 3.05/0.99      ( ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.05/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1978,plain,
% 3.05/0.99      ( ~ v1_funct_1(sK2)
% 3.05/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.05/0.99      | ~ v1_relat_1(sK2) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1979,plain,
% 3.05/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.05/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.05/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1978]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1997,plain,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.05/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1996]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3915,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_3322,c_37,c_39,c_1976,c_1979,c_1997]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4266,plain,
% 3.05/0.99      ( sK1 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_4261,c_3915]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_29,plain,
% 3.05/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_31,negated_conjecture,
% 3.05/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.05/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.05/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_669,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | k2_relat_1(X0) != sK0
% 3.05/0.99      | k2_funct_1(sK2) != X0
% 3.05/0.99      | k1_relat_1(X0) != sK1 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_670,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.05/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_669]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_682,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_670,c_17]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1699,plain,
% 3.05/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_671,plain,
% 3.05/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.05/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2083,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1699,c_37,c_39,c_671,c_1976,c_1979,c_1997]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2084,plain,
% 3.05/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.05/0.99      inference(renaming,[status(thm)],[c_2083]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2087,plain,
% 3.05/0.99      ( k2_relat_1(sK2) != sK1
% 3.05/0.99      | k1_relat_1(sK2) != sK0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_2084,c_2005,c_2009]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3238,plain,
% 3.05/0.99      ( k1_relat_1(sK2) != sK0
% 3.05/0.99      | sK1 != sK1
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_3215,c_2087]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3242,plain,
% 3.05/0.99      ( k1_relat_1(sK2) != sK0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_3238]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4267,plain,
% 3.05/0.99      ( sK1 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_4261,c_3242]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4280,plain,
% 3.05/0.99      ( sK1 = k1_xboole_0 ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_4266,c_4267]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4422,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4280,c_3915]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5,plain,
% 3.05/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4497,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4422,c_5]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_24,plain,
% 3.05/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.05/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_586,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.05/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.05/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.05/0.99      | k2_funct_1(sK2) != X0
% 3.05/0.99      | sK0 != X1
% 3.05/0.99      | sK1 != k1_xboole_0 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_587,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.05/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.05/0.99      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.05/0.99      | sK1 != k1_xboole_0 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_586]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1703,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.05/0.99      | sK1 != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1897,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.05/0.99      | sK1 != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_1703,c_5]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2265,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/0.99      | sK1 != k1_xboole_0
% 3.05/0.99      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1897,c_37,c_39,c_1976,c_1997]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2266,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.05/0.99      | sK1 != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(renaming,[status(thm)],[c_2265]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4431,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4280,c_2266]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4464,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_4431]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4468,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4464,c_5]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4500,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.05/0.99      inference(backward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_4497,c_4468]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4428,plain,
% 3.05/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4280,c_3215]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_23,plain,
% 3.05/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.05/0.99      | k1_xboole_0 = X1
% 3.05/0.99      | k1_xboole_0 = X0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_517,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.05/0.99      | ~ v1_funct_1(X2)
% 3.05/0.99      | ~ v1_relat_1(X2)
% 3.05/0.99      | X2 != X0
% 3.05/0.99      | k2_relat_1(X2) != k1_xboole_0
% 3.05/0.99      | k1_relat_1(X2) != X1
% 3.05/0.99      | k1_xboole_0 = X1
% 3.05/0.99      | k1_xboole_0 = X0 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_518,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_517]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_534,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_518,c_17]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1706,plain,
% 3.05/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4,plain,
% 3.05/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1876,plain,
% 3.05/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_relat_1(X0) = k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_1706,c_4]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5642,plain,
% 3.05/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.05/0.99      | sK2 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_4428,c_1876]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3,plain,
% 3.05/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2330,plain,
% 3.05/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2333,plain,
% 3.05/0.99      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2330]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_0,plain,
% 3.05/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.05/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2338,plain,
% 3.05/0.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2339,plain,
% 3.05/0.99      ( sK2 = X0
% 3.05/0.99      | r1_tarski(X0,sK2) != iProver_top
% 3.05/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2338]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2341,plain,
% 3.05/0.99      ( sK2 = k1_xboole_0
% 3.05/0.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.05/0.99      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2339]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_9,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.05/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2687,plain,
% 3.05/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2688,plain,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.05/0.99      | r1_tarski(sK2,X0) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2687]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2690,plain,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2688]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4437,plain,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4280,c_1712]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4442,plain,
% 3.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4437,c_4]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5814,plain,
% 3.05/0.99      ( sK2 = k1_xboole_0 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_5642,c_2333,c_2341,c_2690,c_4442]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1721,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.05/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4726,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_4497,c_1721]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_6723,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_4726,c_5814]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1726,plain,
% 3.05/0.99      ( X0 = X1
% 3.05/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.05/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_6726,plain,
% 3.05/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.05/0.99      | r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_6723,c_1726]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1724,plain,
% 3.05/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_7278,plain,
% 3.05/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_6726,c_1724]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_7409,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_4500,c_5814,c_7278]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_7,plain,
% 3.05/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.05/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1723,plain,
% 3.05/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4064,plain,
% 3.05/0.99      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_1723,c_1716]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_7410,plain,
% 3.05/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_7409,c_4064]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5675,plain,
% 3.05/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.05/0.99      | ~ r1_tarski(k1_relat_1(X1),X0)
% 3.05/0.99      | k1_relat_1(X1) = X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5677,plain,
% 3.05/0.99      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 3.05/0.99      | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
% 3.05/0.99      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_5675]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5360,plain,
% 3.05/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5362,plain,
% 3.05/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_5360]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1986,plain,
% 3.05/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1990,plain,
% 3.05/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_1986]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1985,plain,
% 3.05/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.05/0.99      | v1_relat_1(k1_xboole_0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_18,plain,
% 3.05/0.99      ( v4_relat_1(X0,X1)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.05/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_11,plain,
% 3.05/0.99      ( ~ v4_relat_1(X0,X1)
% 3.05/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.05/0.99      | ~ v1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_462,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.05/0.99      | ~ v1_relat_1(X0) ),
% 3.05/0.99      inference(resolution,[status(thm)],[c_18,c_11]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_464,plain,
% 3.05/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.05/0.99      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 3.05/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_462]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_7412,plain,
% 3.05/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 3.05/0.99      inference(grounding,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1986:[bind(X1,$fot(k1_xboole_0)),
% 3.05/0.99                 bind(X0,$fot(k1_xboole_0))]]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_7413,plain,
% 3.05/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.05/0.99      | v1_relat_1(k1_xboole_0) ),
% 3.05/0.99      inference(grounding,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1985:[bind(X1,$fot(k1_xboole_0)),
% 3.05/0.99                 bind(X0,$fot(k1_xboole_0))]]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(contradiction,plain,
% 3.05/0.99      ( $false ),
% 3.05/0.99      inference(minisat,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_7410,c_5677,c_5362,c_1990,c_7412,c_7413,c_464]) ).
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  ------                               Statistics
% 3.05/0.99  
% 3.05/0.99  ------ General
% 3.05/0.99  
% 3.05/0.99  abstr_ref_over_cycles:                  0
% 3.05/0.99  abstr_ref_under_cycles:                 0
% 3.05/0.99  gc_basic_clause_elim:                   0
% 3.05/0.99  forced_gc_time:                         0
% 3.05/0.99  parsing_time:                           0.009
% 3.05/0.99  unif_index_cands_time:                  0.
% 3.05/0.99  unif_index_add_time:                    0.
% 3.05/0.99  orderings_time:                         0.
% 3.05/0.99  out_proof_time:                         0.009
% 3.05/0.99  total_time:                             0.218
% 3.05/0.99  num_of_symbols:                         49
% 3.05/0.99  num_of_terms:                           6077
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing
% 3.05/0.99  
% 3.05/0.99  num_of_splits:                          0
% 3.05/0.99  num_of_split_atoms:                     0
% 3.05/0.99  num_of_reused_defs:                     0
% 3.05/0.99  num_eq_ax_congr_red:                    7
% 3.05/0.99  num_of_sem_filtered_clauses:            1
% 3.05/0.99  num_of_subtypes:                        0
% 3.05/0.99  monotx_restored_types:                  0
% 3.05/0.99  sat_num_of_epr_types:                   0
% 3.05/0.99  sat_num_of_non_cyclic_types:            0
% 3.05/0.99  sat_guarded_non_collapsed_types:        0
% 3.05/0.99  num_pure_diseq_elim:                    0
% 3.05/0.99  simp_replaced_by:                       0
% 3.05/0.99  res_preprocessed:                       164
% 3.05/0.99  prep_upred:                             0
% 3.05/0.99  prep_unflattend:                        43
% 3.05/0.99  smt_new_axioms:                         0
% 3.05/0.99  pred_elim_cands:                        4
% 3.05/0.99  pred_elim:                              3
% 3.05/0.99  pred_elim_cl:                           1
% 3.05/0.99  pred_elim_cycles:                       5
% 3.05/0.99  merged_defs:                            8
% 3.05/0.99  merged_defs_ncl:                        0
% 3.05/0.99  bin_hyper_res:                          8
% 3.05/0.99  prep_cycles:                            4
% 3.05/0.99  pred_elim_time:                         0.008
% 3.05/0.99  splitting_time:                         0.
% 3.05/0.99  sem_filter_time:                        0.
% 3.05/0.99  monotx_time:                            0.
% 3.05/0.99  subtype_inf_time:                       0.
% 3.05/0.99  
% 3.05/0.99  ------ Problem properties
% 3.05/0.99  
% 3.05/0.99  clauses:                                34
% 3.05/0.99  conjectures:                            3
% 3.05/0.99  epr:                                    4
% 3.05/0.99  horn:                                   29
% 3.05/0.99  ground:                                 13
% 3.05/0.99  unary:                                  9
% 3.05/0.99  binary:                                 9
% 3.05/0.99  lits:                                   88
% 3.05/0.99  lits_eq:                                36
% 3.05/0.99  fd_pure:                                0
% 3.05/0.99  fd_pseudo:                              0
% 3.05/0.99  fd_cond:                                2
% 3.05/0.99  fd_pseudo_cond:                         1
% 3.05/0.99  ac_symbols:                             0
% 3.05/0.99  
% 3.05/0.99  ------ Propositional Solver
% 3.05/0.99  
% 3.05/0.99  prop_solver_calls:                      28
% 3.05/0.99  prop_fast_solver_calls:                 1172
% 3.05/0.99  smt_solver_calls:                       0
% 3.05/0.99  smt_fast_solver_calls:                  0
% 3.05/0.99  prop_num_of_clauses:                    2563
% 3.05/0.99  prop_preprocess_simplified:             8593
% 3.05/0.99  prop_fo_subsumed:                       28
% 3.05/0.99  prop_solver_time:                       0.
% 3.05/0.99  smt_solver_time:                        0.
% 3.05/0.99  smt_fast_solver_time:                   0.
% 3.05/0.99  prop_fast_solver_time:                  0.
% 3.05/0.99  prop_unsat_core_time:                   0.
% 3.05/0.99  
% 3.05/0.99  ------ QBF
% 3.05/0.99  
% 3.05/0.99  qbf_q_res:                              0
% 3.05/0.99  qbf_num_tautologies:                    0
% 3.05/0.99  qbf_prep_cycles:                        0
% 3.05/0.99  
% 3.05/0.99  ------ BMC1
% 3.05/0.99  
% 3.05/0.99  bmc1_current_bound:                     -1
% 3.05/0.99  bmc1_last_solved_bound:                 -1
% 3.05/0.99  bmc1_unsat_core_size:                   -1
% 3.05/0.99  bmc1_unsat_core_parents_size:           -1
% 3.05/0.99  bmc1_merge_next_fun:                    0
% 3.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.05/0.99  
% 3.05/0.99  ------ Instantiation
% 3.05/0.99  
% 3.05/0.99  inst_num_of_clauses:                    931
% 3.05/0.99  inst_num_in_passive:                    409
% 3.05/0.99  inst_num_in_active:                     395
% 3.05/0.99  inst_num_in_unprocessed:                128
% 3.05/0.99  inst_num_of_loops:                      530
% 3.05/0.99  inst_num_of_learning_restarts:          0
% 3.05/0.99  inst_num_moves_active_passive:          132
% 3.05/0.99  inst_lit_activity:                      0
% 3.05/0.99  inst_lit_activity_moves:                0
% 3.05/0.99  inst_num_tautologies:                   0
% 3.05/0.99  inst_num_prop_implied:                  0
% 3.05/0.99  inst_num_existing_simplified:           0
% 3.05/0.99  inst_num_eq_res_simplified:             0
% 3.05/0.99  inst_num_child_elim:                    0
% 3.05/0.99  inst_num_of_dismatching_blockings:      262
% 3.05/0.99  inst_num_of_non_proper_insts:           838
% 3.05/0.99  inst_num_of_duplicates:                 0
% 3.05/0.99  inst_inst_num_from_inst_to_res:         0
% 3.05/0.99  inst_dismatching_checking_time:         0.
% 3.05/0.99  
% 3.05/0.99  ------ Resolution
% 3.05/0.99  
% 3.05/0.99  res_num_of_clauses:                     0
% 3.05/0.99  res_num_in_passive:                     0
% 3.05/0.99  res_num_in_active:                      0
% 3.05/0.99  res_num_of_loops:                       168
% 3.05/0.99  res_forward_subset_subsumed:            48
% 3.05/0.99  res_backward_subset_subsumed:           4
% 3.05/0.99  res_forward_subsumed:                   0
% 3.05/0.99  res_backward_subsumed:                  0
% 3.05/0.99  res_forward_subsumption_resolution:     4
% 3.05/0.99  res_backward_subsumption_resolution:    0
% 3.05/0.99  res_clause_to_clause_subsumption:       419
% 3.05/0.99  res_orphan_elimination:                 0
% 3.05/0.99  res_tautology_del:                      82
% 3.05/0.99  res_num_eq_res_simplified:              0
% 3.05/0.99  res_num_sel_changes:                    0
% 3.05/0.99  res_moves_from_active_to_pass:          0
% 3.05/0.99  
% 3.05/0.99  ------ Superposition
% 3.05/0.99  
% 3.05/0.99  sup_time_total:                         0.
% 3.05/0.99  sup_time_generating:                    0.
% 3.05/0.99  sup_time_sim_full:                      0.
% 3.05/0.99  sup_time_sim_immed:                     0.
% 3.05/0.99  
% 3.05/0.99  sup_num_of_clauses:                     95
% 3.05/0.99  sup_num_in_active:                      52
% 3.05/0.99  sup_num_in_passive:                     43
% 3.05/0.99  sup_num_of_loops:                       105
% 3.05/0.99  sup_fw_superposition:                   86
% 3.05/0.99  sup_bw_superposition:                   78
% 3.05/0.99  sup_immediate_simplified:               73
% 3.05/0.99  sup_given_eliminated:                   2
% 3.05/0.99  comparisons_done:                       0
% 3.05/0.99  comparisons_avoided:                    11
% 3.05/0.99  
% 3.05/0.99  ------ Simplifications
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  sim_fw_subset_subsumed:                 22
% 3.05/0.99  sim_bw_subset_subsumed:                 4
% 3.05/0.99  sim_fw_subsumed:                        23
% 3.05/0.99  sim_bw_subsumed:                        5
% 3.05/0.99  sim_fw_subsumption_res:                 4
% 3.05/0.99  sim_bw_subsumption_res:                 3
% 3.05/0.99  sim_tautology_del:                      7
% 3.05/0.99  sim_eq_tautology_del:                   8
% 3.05/0.99  sim_eq_res_simp:                        3
% 3.05/0.99  sim_fw_demodulated:                     25
% 3.05/0.99  sim_bw_demodulated:                     50
% 3.05/0.99  sim_light_normalised:                   47
% 3.05/0.99  sim_joinable_taut:                      0
% 3.05/0.99  sim_joinable_simp:                      0
% 3.05/0.99  sim_ac_normalised:                      0
% 3.05/0.99  sim_smt_subsumption:                    0
% 3.05/0.99  
%------------------------------------------------------------------------------
