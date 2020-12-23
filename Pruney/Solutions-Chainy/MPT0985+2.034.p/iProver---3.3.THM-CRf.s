%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:26 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  214 (1581 expanded)
%              Number of clauses        :  132 ( 515 expanded)
%              Number of leaves         :   20 ( 303 expanded)
%              Depth                    :   24
%              Number of atoms          :  672 (8120 expanded)
%              Number of equality atoms :  267 (1437 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f69,plain,
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

fof(f70,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f54,f69])).

fof(f116,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f70])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f118,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f70])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f96,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f114,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f51])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f119,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f70])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f65])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f123,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1748,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1756,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3643,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1748,c_1756])).

cnf(c_44,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3646,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3643,c_44])).

cnf(c_26,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_45,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_566,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_45])).

cnf(c_567,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_569,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_48])).

cnf(c_1743,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1828,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1853,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_2170,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1743,c_48,c_46,c_567,c_1853])).

cnf(c_3654,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3646,c_2170])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1755,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1750,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4669,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1750])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_61,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32317,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | k2_relat_1(X0) = k1_xboole_0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4669,c_61])).

cnf(c_32318,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_32317])).

cnf(c_32323,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3654,c_32318])).

cnf(c_25,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_580,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_45])).

cnf(c_581,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_583,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_48])).

cnf(c_1742,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_2010,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_48,c_46,c_581,c_1853])).

cnf(c_32329,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32323,c_2010])).

cnf(c_32330,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32329,c_2010])).

cnf(c_49,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1820,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1821,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_1854,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1853])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2347,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2348,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2347])).

cnf(c_1754,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4014,plain,
    ( v1_funct_2(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2010,c_1754])).

cnf(c_4018,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4014,c_3654])).

cnf(c_4660,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2010,c_1755])).

cnf(c_4671,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4660,c_3654])).

cnf(c_5251,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4671,c_49,c_51,c_1821,c_1854,c_2348])).

cnf(c_5261,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5251,c_1750])).

cnf(c_32535,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32330,c_49,c_51,c_1821,c_1854,c_2348,c_4018,c_5261])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1752,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4668,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1752])).

cnf(c_31517,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4668,c_61])).

cnf(c_31524,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3654,c_31517])).

cnf(c_31539,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31524,c_2010])).

cnf(c_31540,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31539,c_2010])).

cnf(c_31947,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31540,c_49,c_51,c_1821,c_1854,c_2348])).

cnf(c_43,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1749,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_53,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2005,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1749,c_49,c_51,c_53,c_1821,c_1854])).

cnf(c_2006,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2005])).

cnf(c_31959,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_31947,c_2006])).

cnf(c_28,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_28,c_18])).

cnf(c_604,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_27])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_604])).

cnf(c_1741,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_2197,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1741])).

cnf(c_32099,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31959,c_2197])).

cnf(c_32100,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_32099])).

cnf(c_32539,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32535,c_32100])).

cnf(c_32587,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32539,c_2197])).

cnf(c_32644,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32587,c_5251])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_32656,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32644,c_11])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2571,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1741])).

cnf(c_5955,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_2571])).

cnf(c_6054,plain,
    ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3654,c_5955])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_136,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_33,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_31,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_540,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_33,c_31])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_33,c_31])).

cnf(c_545,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_544])).

cnf(c_1881,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_1882,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_1944,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1945,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top
    | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2013,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
    | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2017,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) = iProver_top
    | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2285,plain,
    ( r2_hidden(sK0(sK3),sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2286,plain,
    ( r2_hidden(sK0(sK3),sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2285])).

cnf(c_2364,plain,
    ( r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4))
    | v1_xboole_0(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2365,plain,
    ( r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4)) = iProver_top
    | v1_xboole_0(k2_funct_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_330,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_330])).

cnf(c_400,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_331])).

cnf(c_2669,plain,
    ( ~ r1_tarski(sK3,X0)
    | ~ r2_hidden(sK0(sK3),sK3)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_2670,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r2_hidden(sK0(sK3),sK3) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2669])).

cnf(c_2672,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK3),sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2670])).

cnf(c_2760,plain,
    ( ~ r1_tarski(k2_funct_1(sK4),X0)
    | ~ r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_2761,plain,
    ( r1_tarski(k2_funct_1(sK4),X0) != iProver_top
    | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2760])).

cnf(c_2763,plain,
    ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top
    | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2761])).

cnf(c_1773,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1775,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2687,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_1775])).

cnf(c_2572,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_2006])).

cnf(c_2795,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | v1_xboole_0(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2687,c_2572])).

cnf(c_4938,plain,
    ( ~ r1_tarski(k2_funct_1(sK4),X0)
    | ~ r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_4939,plain,
    ( r1_tarski(k2_funct_1(sK4),X0) != iProver_top
    | r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4938])).

cnf(c_4941,plain,
    ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4939])).

cnf(c_6283,plain,
    ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6054,c_49,c_51,c_136,c_1821,c_1854,c_1882,c_1945,c_2017,c_2286,c_2365,c_2672,c_2763,c_2795,c_4941])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4495,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0))
    | r1_tarski(k2_funct_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4496,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k2_funct_1(sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4495])).

cnf(c_4498,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_funct_1(sK4),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4496])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32656,c_6283,c_4498])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.67/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.52  
% 7.67/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.52  
% 7.67/1.52  ------  iProver source info
% 7.67/1.52  
% 7.67/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.52  git: non_committed_changes: false
% 7.67/1.52  git: last_make_outside_of_git: false
% 7.67/1.52  
% 7.67/1.52  ------ 
% 7.67/1.52  
% 7.67/1.52  ------ Input Options
% 7.67/1.52  
% 7.67/1.52  --out_options                           all
% 7.67/1.52  --tptp_safe_out                         true
% 7.67/1.52  --problem_path                          ""
% 7.67/1.52  --include_path                          ""
% 7.67/1.52  --clausifier                            res/vclausify_rel
% 7.67/1.52  --clausifier_options                    ""
% 7.67/1.52  --stdin                                 false
% 7.67/1.52  --stats_out                             all
% 7.67/1.52  
% 7.67/1.52  ------ General Options
% 7.67/1.52  
% 7.67/1.52  --fof                                   false
% 7.67/1.52  --time_out_real                         305.
% 7.67/1.52  --time_out_virtual                      -1.
% 7.67/1.52  --symbol_type_check                     false
% 7.67/1.52  --clausify_out                          false
% 7.67/1.52  --sig_cnt_out                           false
% 7.67/1.52  --trig_cnt_out                          false
% 7.67/1.52  --trig_cnt_out_tolerance                1.
% 7.67/1.52  --trig_cnt_out_sk_spl                   false
% 7.67/1.52  --abstr_cl_out                          false
% 7.67/1.52  
% 7.67/1.52  ------ Global Options
% 7.67/1.52  
% 7.67/1.52  --schedule                              default
% 7.67/1.52  --add_important_lit                     false
% 7.67/1.52  --prop_solver_per_cl                    1000
% 7.67/1.52  --min_unsat_core                        false
% 7.67/1.52  --soft_assumptions                      false
% 7.67/1.52  --soft_lemma_size                       3
% 7.67/1.52  --prop_impl_unit_size                   0
% 7.67/1.52  --prop_impl_unit                        []
% 7.67/1.52  --share_sel_clauses                     true
% 7.67/1.52  --reset_solvers                         false
% 7.67/1.52  --bc_imp_inh                            [conj_cone]
% 7.67/1.52  --conj_cone_tolerance                   3.
% 7.67/1.52  --extra_neg_conj                        none
% 7.67/1.52  --large_theory_mode                     true
% 7.67/1.52  --prolific_symb_bound                   200
% 7.67/1.52  --lt_threshold                          2000
% 7.67/1.52  --clause_weak_htbl                      true
% 7.67/1.52  --gc_record_bc_elim                     false
% 7.67/1.52  
% 7.67/1.52  ------ Preprocessing Options
% 7.67/1.52  
% 7.67/1.52  --preprocessing_flag                    true
% 7.67/1.52  --time_out_prep_mult                    0.1
% 7.67/1.52  --splitting_mode                        input
% 7.67/1.52  --splitting_grd                         true
% 7.67/1.52  --splitting_cvd                         false
% 7.67/1.52  --splitting_cvd_svl                     false
% 7.67/1.52  --splitting_nvd                         32
% 7.67/1.52  --sub_typing                            true
% 7.67/1.52  --prep_gs_sim                           true
% 7.67/1.52  --prep_unflatten                        true
% 7.67/1.52  --prep_res_sim                          true
% 7.67/1.52  --prep_upred                            true
% 7.67/1.52  --prep_sem_filter                       exhaustive
% 7.67/1.52  --prep_sem_filter_out                   false
% 7.67/1.52  --pred_elim                             true
% 7.67/1.52  --res_sim_input                         true
% 7.67/1.52  --eq_ax_congr_red                       true
% 7.67/1.52  --pure_diseq_elim                       true
% 7.67/1.52  --brand_transform                       false
% 7.67/1.52  --non_eq_to_eq                          false
% 7.67/1.52  --prep_def_merge                        true
% 7.67/1.52  --prep_def_merge_prop_impl              false
% 7.67/1.52  --prep_def_merge_mbd                    true
% 7.67/1.52  --prep_def_merge_tr_red                 false
% 7.67/1.52  --prep_def_merge_tr_cl                  false
% 7.67/1.52  --smt_preprocessing                     true
% 7.67/1.52  --smt_ac_axioms                         fast
% 7.67/1.52  --preprocessed_out                      false
% 7.67/1.52  --preprocessed_stats                    false
% 7.67/1.52  
% 7.67/1.52  ------ Abstraction refinement Options
% 7.67/1.52  
% 7.67/1.52  --abstr_ref                             []
% 7.67/1.52  --abstr_ref_prep                        false
% 7.67/1.52  --abstr_ref_until_sat                   false
% 7.67/1.52  --abstr_ref_sig_restrict                funpre
% 7.67/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.52  --abstr_ref_under                       []
% 7.67/1.52  
% 7.67/1.52  ------ SAT Options
% 7.67/1.52  
% 7.67/1.52  --sat_mode                              false
% 7.67/1.52  --sat_fm_restart_options                ""
% 7.67/1.52  --sat_gr_def                            false
% 7.67/1.52  --sat_epr_types                         true
% 7.67/1.52  --sat_non_cyclic_types                  false
% 7.67/1.52  --sat_finite_models                     false
% 7.67/1.52  --sat_fm_lemmas                         false
% 7.67/1.52  --sat_fm_prep                           false
% 7.67/1.52  --sat_fm_uc_incr                        true
% 7.67/1.52  --sat_out_model                         small
% 7.67/1.52  --sat_out_clauses                       false
% 7.67/1.52  
% 7.67/1.52  ------ QBF Options
% 7.67/1.52  
% 7.67/1.52  --qbf_mode                              false
% 7.67/1.52  --qbf_elim_univ                         false
% 7.67/1.52  --qbf_dom_inst                          none
% 7.67/1.52  --qbf_dom_pre_inst                      false
% 7.67/1.52  --qbf_sk_in                             false
% 7.67/1.52  --qbf_pred_elim                         true
% 7.67/1.52  --qbf_split                             512
% 7.67/1.52  
% 7.67/1.52  ------ BMC1 Options
% 7.67/1.52  
% 7.67/1.52  --bmc1_incremental                      false
% 7.67/1.52  --bmc1_axioms                           reachable_all
% 7.67/1.52  --bmc1_min_bound                        0
% 7.67/1.52  --bmc1_max_bound                        -1
% 7.67/1.52  --bmc1_max_bound_default                -1
% 7.67/1.52  --bmc1_symbol_reachability              true
% 7.67/1.52  --bmc1_property_lemmas                  false
% 7.67/1.52  --bmc1_k_induction                      false
% 7.67/1.52  --bmc1_non_equiv_states                 false
% 7.67/1.52  --bmc1_deadlock                         false
% 7.67/1.52  --bmc1_ucm                              false
% 7.67/1.52  --bmc1_add_unsat_core                   none
% 7.67/1.52  --bmc1_unsat_core_children              false
% 7.67/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.52  --bmc1_out_stat                         full
% 7.67/1.52  --bmc1_ground_init                      false
% 7.67/1.52  --bmc1_pre_inst_next_state              false
% 7.67/1.52  --bmc1_pre_inst_state                   false
% 7.67/1.52  --bmc1_pre_inst_reach_state             false
% 7.67/1.52  --bmc1_out_unsat_core                   false
% 7.67/1.52  --bmc1_aig_witness_out                  false
% 7.67/1.52  --bmc1_verbose                          false
% 7.67/1.52  --bmc1_dump_clauses_tptp                false
% 7.67/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.52  --bmc1_dump_file                        -
% 7.67/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.52  --bmc1_ucm_extend_mode                  1
% 7.67/1.52  --bmc1_ucm_init_mode                    2
% 7.67/1.52  --bmc1_ucm_cone_mode                    none
% 7.67/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.52  --bmc1_ucm_relax_model                  4
% 7.67/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.52  --bmc1_ucm_layered_model                none
% 7.67/1.52  --bmc1_ucm_max_lemma_size               10
% 7.67/1.52  
% 7.67/1.52  ------ AIG Options
% 7.67/1.52  
% 7.67/1.52  --aig_mode                              false
% 7.67/1.52  
% 7.67/1.52  ------ Instantiation Options
% 7.67/1.52  
% 7.67/1.52  --instantiation_flag                    true
% 7.67/1.52  --inst_sos_flag                         true
% 7.67/1.52  --inst_sos_phase                        true
% 7.67/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.52  --inst_lit_sel_side                     num_symb
% 7.67/1.52  --inst_solver_per_active                1400
% 7.67/1.52  --inst_solver_calls_frac                1.
% 7.67/1.52  --inst_passive_queue_type               priority_queues
% 7.67/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.52  --inst_passive_queues_freq              [25;2]
% 7.67/1.52  --inst_dismatching                      true
% 7.67/1.52  --inst_eager_unprocessed_to_passive     true
% 7.67/1.52  --inst_prop_sim_given                   true
% 7.67/1.52  --inst_prop_sim_new                     false
% 7.67/1.52  --inst_subs_new                         false
% 7.67/1.52  --inst_eq_res_simp                      false
% 7.67/1.52  --inst_subs_given                       false
% 7.67/1.52  --inst_orphan_elimination               true
% 7.67/1.52  --inst_learning_loop_flag               true
% 7.67/1.52  --inst_learning_start                   3000
% 7.67/1.52  --inst_learning_factor                  2
% 7.67/1.52  --inst_start_prop_sim_after_learn       3
% 7.67/1.52  --inst_sel_renew                        solver
% 7.67/1.52  --inst_lit_activity_flag                true
% 7.67/1.52  --inst_restr_to_given                   false
% 7.67/1.52  --inst_activity_threshold               500
% 7.67/1.52  --inst_out_proof                        true
% 7.67/1.52  
% 7.67/1.52  ------ Resolution Options
% 7.67/1.52  
% 7.67/1.52  --resolution_flag                       true
% 7.67/1.52  --res_lit_sel                           adaptive
% 7.67/1.52  --res_lit_sel_side                      none
% 7.67/1.52  --res_ordering                          kbo
% 7.67/1.52  --res_to_prop_solver                    active
% 7.67/1.52  --res_prop_simpl_new                    false
% 7.67/1.52  --res_prop_simpl_given                  true
% 7.67/1.52  --res_passive_queue_type                priority_queues
% 7.67/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.52  --res_passive_queues_freq               [15;5]
% 7.67/1.52  --res_forward_subs                      full
% 7.67/1.52  --res_backward_subs                     full
% 7.67/1.52  --res_forward_subs_resolution           true
% 7.67/1.52  --res_backward_subs_resolution          true
% 7.67/1.52  --res_orphan_elimination                true
% 7.67/1.52  --res_time_limit                        2.
% 7.67/1.52  --res_out_proof                         true
% 7.67/1.52  
% 7.67/1.52  ------ Superposition Options
% 7.67/1.52  
% 7.67/1.52  --superposition_flag                    true
% 7.67/1.52  --sup_passive_queue_type                priority_queues
% 7.67/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.52  --demod_completeness_check              fast
% 7.67/1.52  --demod_use_ground                      true
% 7.67/1.52  --sup_to_prop_solver                    passive
% 7.67/1.52  --sup_prop_simpl_new                    true
% 7.67/1.52  --sup_prop_simpl_given                  true
% 7.67/1.52  --sup_fun_splitting                     true
% 7.67/1.52  --sup_smt_interval                      50000
% 7.67/1.52  
% 7.67/1.52  ------ Superposition Simplification Setup
% 7.67/1.52  
% 7.67/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.52  --sup_immed_triv                        [TrivRules]
% 7.67/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.52  --sup_immed_bw_main                     []
% 7.67/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.52  --sup_input_bw                          []
% 7.67/1.52  
% 7.67/1.52  ------ Combination Options
% 7.67/1.52  
% 7.67/1.52  --comb_res_mult                         3
% 7.67/1.52  --comb_sup_mult                         2
% 7.67/1.52  --comb_inst_mult                        10
% 7.67/1.52  
% 7.67/1.52  ------ Debug Options
% 7.67/1.52  
% 7.67/1.52  --dbg_backtrace                         false
% 7.67/1.52  --dbg_dump_prop_clauses                 false
% 7.67/1.52  --dbg_dump_prop_clauses_file            -
% 7.67/1.52  --dbg_out_stat                          false
% 7.67/1.52  ------ Parsing...
% 7.67/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.52  
% 7.67/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.67/1.52  
% 7.67/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.52  
% 7.67/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.52  ------ Proving...
% 7.67/1.52  ------ Problem Properties 
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  clauses                                 40
% 7.67/1.52  conjectures                             5
% 7.67/1.52  EPR                                     10
% 7.67/1.52  Horn                                    35
% 7.67/1.52  unary                                   8
% 7.67/1.52  binary                                  15
% 7.67/1.52  lits                                    101
% 7.67/1.52  lits eq                                 16
% 7.67/1.52  fd_pure                                 0
% 7.67/1.52  fd_pseudo                               0
% 7.67/1.52  fd_cond                                 4
% 7.67/1.52  fd_pseudo_cond                          2
% 7.67/1.52  AC symbols                              0
% 7.67/1.52  
% 7.67/1.52  ------ Schedule dynamic 5 is on 
% 7.67/1.52  
% 7.67/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  ------ 
% 7.67/1.52  Current options:
% 7.67/1.52  ------ 
% 7.67/1.52  
% 7.67/1.52  ------ Input Options
% 7.67/1.52  
% 7.67/1.52  --out_options                           all
% 7.67/1.52  --tptp_safe_out                         true
% 7.67/1.52  --problem_path                          ""
% 7.67/1.52  --include_path                          ""
% 7.67/1.52  --clausifier                            res/vclausify_rel
% 7.67/1.52  --clausifier_options                    ""
% 7.67/1.52  --stdin                                 false
% 7.67/1.52  --stats_out                             all
% 7.67/1.52  
% 7.67/1.52  ------ General Options
% 7.67/1.52  
% 7.67/1.52  --fof                                   false
% 7.67/1.52  --time_out_real                         305.
% 7.67/1.52  --time_out_virtual                      -1.
% 7.67/1.52  --symbol_type_check                     false
% 7.67/1.52  --clausify_out                          false
% 7.67/1.52  --sig_cnt_out                           false
% 7.67/1.52  --trig_cnt_out                          false
% 7.67/1.52  --trig_cnt_out_tolerance                1.
% 7.67/1.52  --trig_cnt_out_sk_spl                   false
% 7.67/1.52  --abstr_cl_out                          false
% 7.67/1.52  
% 7.67/1.52  ------ Global Options
% 7.67/1.52  
% 7.67/1.52  --schedule                              default
% 7.67/1.52  --add_important_lit                     false
% 7.67/1.52  --prop_solver_per_cl                    1000
% 7.67/1.52  --min_unsat_core                        false
% 7.67/1.52  --soft_assumptions                      false
% 7.67/1.52  --soft_lemma_size                       3
% 7.67/1.52  --prop_impl_unit_size                   0
% 7.67/1.52  --prop_impl_unit                        []
% 7.67/1.52  --share_sel_clauses                     true
% 7.67/1.52  --reset_solvers                         false
% 7.67/1.52  --bc_imp_inh                            [conj_cone]
% 7.67/1.52  --conj_cone_tolerance                   3.
% 7.67/1.52  --extra_neg_conj                        none
% 7.67/1.52  --large_theory_mode                     true
% 7.67/1.52  --prolific_symb_bound                   200
% 7.67/1.52  --lt_threshold                          2000
% 7.67/1.52  --clause_weak_htbl                      true
% 7.67/1.52  --gc_record_bc_elim                     false
% 7.67/1.52  
% 7.67/1.52  ------ Preprocessing Options
% 7.67/1.52  
% 7.67/1.52  --preprocessing_flag                    true
% 7.67/1.52  --time_out_prep_mult                    0.1
% 7.67/1.52  --splitting_mode                        input
% 7.67/1.52  --splitting_grd                         true
% 7.67/1.52  --splitting_cvd                         false
% 7.67/1.52  --splitting_cvd_svl                     false
% 7.67/1.52  --splitting_nvd                         32
% 7.67/1.52  --sub_typing                            true
% 7.67/1.52  --prep_gs_sim                           true
% 7.67/1.52  --prep_unflatten                        true
% 7.67/1.52  --prep_res_sim                          true
% 7.67/1.52  --prep_upred                            true
% 7.67/1.52  --prep_sem_filter                       exhaustive
% 7.67/1.52  --prep_sem_filter_out                   false
% 7.67/1.52  --pred_elim                             true
% 7.67/1.52  --res_sim_input                         true
% 7.67/1.52  --eq_ax_congr_red                       true
% 7.67/1.52  --pure_diseq_elim                       true
% 7.67/1.52  --brand_transform                       false
% 7.67/1.52  --non_eq_to_eq                          false
% 7.67/1.52  --prep_def_merge                        true
% 7.67/1.52  --prep_def_merge_prop_impl              false
% 7.67/1.52  --prep_def_merge_mbd                    true
% 7.67/1.52  --prep_def_merge_tr_red                 false
% 7.67/1.52  --prep_def_merge_tr_cl                  false
% 7.67/1.52  --smt_preprocessing                     true
% 7.67/1.52  --smt_ac_axioms                         fast
% 7.67/1.52  --preprocessed_out                      false
% 7.67/1.52  --preprocessed_stats                    false
% 7.67/1.52  
% 7.67/1.52  ------ Abstraction refinement Options
% 7.67/1.52  
% 7.67/1.52  --abstr_ref                             []
% 7.67/1.52  --abstr_ref_prep                        false
% 7.67/1.52  --abstr_ref_until_sat                   false
% 7.67/1.52  --abstr_ref_sig_restrict                funpre
% 7.67/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.52  --abstr_ref_under                       []
% 7.67/1.52  
% 7.67/1.52  ------ SAT Options
% 7.67/1.52  
% 7.67/1.52  --sat_mode                              false
% 7.67/1.52  --sat_fm_restart_options                ""
% 7.67/1.52  --sat_gr_def                            false
% 7.67/1.52  --sat_epr_types                         true
% 7.67/1.52  --sat_non_cyclic_types                  false
% 7.67/1.52  --sat_finite_models                     false
% 7.67/1.52  --sat_fm_lemmas                         false
% 7.67/1.52  --sat_fm_prep                           false
% 7.67/1.52  --sat_fm_uc_incr                        true
% 7.67/1.52  --sat_out_model                         small
% 7.67/1.52  --sat_out_clauses                       false
% 7.67/1.52  
% 7.67/1.52  ------ QBF Options
% 7.67/1.52  
% 7.67/1.52  --qbf_mode                              false
% 7.67/1.52  --qbf_elim_univ                         false
% 7.67/1.52  --qbf_dom_inst                          none
% 7.67/1.52  --qbf_dom_pre_inst                      false
% 7.67/1.52  --qbf_sk_in                             false
% 7.67/1.52  --qbf_pred_elim                         true
% 7.67/1.52  --qbf_split                             512
% 7.67/1.52  
% 7.67/1.52  ------ BMC1 Options
% 7.67/1.52  
% 7.67/1.52  --bmc1_incremental                      false
% 7.67/1.52  --bmc1_axioms                           reachable_all
% 7.67/1.52  --bmc1_min_bound                        0
% 7.67/1.52  --bmc1_max_bound                        -1
% 7.67/1.52  --bmc1_max_bound_default                -1
% 7.67/1.52  --bmc1_symbol_reachability              true
% 7.67/1.52  --bmc1_property_lemmas                  false
% 7.67/1.52  --bmc1_k_induction                      false
% 7.67/1.52  --bmc1_non_equiv_states                 false
% 7.67/1.52  --bmc1_deadlock                         false
% 7.67/1.52  --bmc1_ucm                              false
% 7.67/1.52  --bmc1_add_unsat_core                   none
% 7.67/1.52  --bmc1_unsat_core_children              false
% 7.67/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.52  --bmc1_out_stat                         full
% 7.67/1.52  --bmc1_ground_init                      false
% 7.67/1.52  --bmc1_pre_inst_next_state              false
% 7.67/1.52  --bmc1_pre_inst_state                   false
% 7.67/1.52  --bmc1_pre_inst_reach_state             false
% 7.67/1.52  --bmc1_out_unsat_core                   false
% 7.67/1.52  --bmc1_aig_witness_out                  false
% 7.67/1.52  --bmc1_verbose                          false
% 7.67/1.52  --bmc1_dump_clauses_tptp                false
% 7.67/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.52  --bmc1_dump_file                        -
% 7.67/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.52  --bmc1_ucm_extend_mode                  1
% 7.67/1.52  --bmc1_ucm_init_mode                    2
% 7.67/1.52  --bmc1_ucm_cone_mode                    none
% 7.67/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.52  --bmc1_ucm_relax_model                  4
% 7.67/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.52  --bmc1_ucm_layered_model                none
% 7.67/1.52  --bmc1_ucm_max_lemma_size               10
% 7.67/1.52  
% 7.67/1.52  ------ AIG Options
% 7.67/1.52  
% 7.67/1.52  --aig_mode                              false
% 7.67/1.52  
% 7.67/1.52  ------ Instantiation Options
% 7.67/1.52  
% 7.67/1.52  --instantiation_flag                    true
% 7.67/1.52  --inst_sos_flag                         true
% 7.67/1.52  --inst_sos_phase                        true
% 7.67/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.52  --inst_lit_sel_side                     none
% 7.67/1.52  --inst_solver_per_active                1400
% 7.67/1.52  --inst_solver_calls_frac                1.
% 7.67/1.52  --inst_passive_queue_type               priority_queues
% 7.67/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.52  --inst_passive_queues_freq              [25;2]
% 7.67/1.52  --inst_dismatching                      true
% 7.67/1.52  --inst_eager_unprocessed_to_passive     true
% 7.67/1.52  --inst_prop_sim_given                   true
% 7.67/1.52  --inst_prop_sim_new                     false
% 7.67/1.52  --inst_subs_new                         false
% 7.67/1.52  --inst_eq_res_simp                      false
% 7.67/1.52  --inst_subs_given                       false
% 7.67/1.52  --inst_orphan_elimination               true
% 7.67/1.52  --inst_learning_loop_flag               true
% 7.67/1.52  --inst_learning_start                   3000
% 7.67/1.52  --inst_learning_factor                  2
% 7.67/1.52  --inst_start_prop_sim_after_learn       3
% 7.67/1.52  --inst_sel_renew                        solver
% 7.67/1.52  --inst_lit_activity_flag                true
% 7.67/1.52  --inst_restr_to_given                   false
% 7.67/1.52  --inst_activity_threshold               500
% 7.67/1.52  --inst_out_proof                        true
% 7.67/1.52  
% 7.67/1.52  ------ Resolution Options
% 7.67/1.52  
% 7.67/1.52  --resolution_flag                       false
% 7.67/1.52  --res_lit_sel                           adaptive
% 7.67/1.52  --res_lit_sel_side                      none
% 7.67/1.52  --res_ordering                          kbo
% 7.67/1.52  --res_to_prop_solver                    active
% 7.67/1.52  --res_prop_simpl_new                    false
% 7.67/1.52  --res_prop_simpl_given                  true
% 7.67/1.52  --res_passive_queue_type                priority_queues
% 7.67/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.52  --res_passive_queues_freq               [15;5]
% 7.67/1.52  --res_forward_subs                      full
% 7.67/1.52  --res_backward_subs                     full
% 7.67/1.52  --res_forward_subs_resolution           true
% 7.67/1.52  --res_backward_subs_resolution          true
% 7.67/1.52  --res_orphan_elimination                true
% 7.67/1.52  --res_time_limit                        2.
% 7.67/1.52  --res_out_proof                         true
% 7.67/1.52  
% 7.67/1.52  ------ Superposition Options
% 7.67/1.52  
% 7.67/1.52  --superposition_flag                    true
% 7.67/1.52  --sup_passive_queue_type                priority_queues
% 7.67/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.52  --demod_completeness_check              fast
% 7.67/1.52  --demod_use_ground                      true
% 7.67/1.52  --sup_to_prop_solver                    passive
% 7.67/1.52  --sup_prop_simpl_new                    true
% 7.67/1.52  --sup_prop_simpl_given                  true
% 7.67/1.52  --sup_fun_splitting                     true
% 7.67/1.52  --sup_smt_interval                      50000
% 7.67/1.52  
% 7.67/1.52  ------ Superposition Simplification Setup
% 7.67/1.52  
% 7.67/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.52  --sup_immed_triv                        [TrivRules]
% 7.67/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.52  --sup_immed_bw_main                     []
% 7.67/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.52  --sup_input_bw                          []
% 7.67/1.52  
% 7.67/1.52  ------ Combination Options
% 7.67/1.52  
% 7.67/1.52  --comb_res_mult                         3
% 7.67/1.52  --comb_sup_mult                         2
% 7.67/1.52  --comb_inst_mult                        10
% 7.67/1.52  
% 7.67/1.52  ------ Debug Options
% 7.67/1.52  
% 7.67/1.52  --dbg_backtrace                         false
% 7.67/1.52  --dbg_dump_prop_clauses                 false
% 7.67/1.52  --dbg_dump_prop_clauses_file            -
% 7.67/1.52  --dbg_out_stat                          false
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  ------ Proving...
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  % SZS status Theorem for theBenchmark.p
% 7.67/1.52  
% 7.67/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.52  
% 7.67/1.52  fof(f25,conjecture,(
% 7.67/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f26,negated_conjecture,(
% 7.67/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.67/1.52    inference(negated_conjecture,[],[f25])).
% 7.67/1.52  
% 7.67/1.52  fof(f53,plain,(
% 7.67/1.52    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.67/1.52    inference(ennf_transformation,[],[f26])).
% 7.67/1.52  
% 7.67/1.52  fof(f54,plain,(
% 7.67/1.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.67/1.52    inference(flattening,[],[f53])).
% 7.67/1.52  
% 7.67/1.52  fof(f69,plain,(
% 7.67/1.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 7.67/1.52    introduced(choice_axiom,[])).
% 7.67/1.52  
% 7.67/1.52  fof(f70,plain,(
% 7.67/1.52    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 7.67/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f54,f69])).
% 7.67/1.52  
% 7.67/1.52  fof(f116,plain,(
% 7.67/1.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 7.67/1.52    inference(cnf_transformation,[],[f70])).
% 7.67/1.52  
% 7.67/1.52  fof(f20,axiom,(
% 7.67/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f45,plain,(
% 7.67/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.52    inference(ennf_transformation,[],[f20])).
% 7.67/1.52  
% 7.67/1.52  fof(f101,plain,(
% 7.67/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.52    inference(cnf_transformation,[],[f45])).
% 7.67/1.52  
% 7.67/1.52  fof(f118,plain,(
% 7.67/1.52    k2_relset_1(sK2,sK3,sK4) = sK3),
% 7.67/1.52    inference(cnf_transformation,[],[f70])).
% 7.67/1.52  
% 7.67/1.52  fof(f16,axiom,(
% 7.67/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f40,plain,(
% 7.67/1.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.52    inference(ennf_transformation,[],[f16])).
% 7.67/1.52  
% 7.67/1.52  fof(f41,plain,(
% 7.67/1.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.52    inference(flattening,[],[f40])).
% 7.67/1.52  
% 7.67/1.52  fof(f96,plain,(
% 7.67/1.52    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f41])).
% 7.67/1.52  
% 7.67/1.52  fof(f117,plain,(
% 7.67/1.52    v2_funct_1(sK4)),
% 7.67/1.52    inference(cnf_transformation,[],[f70])).
% 7.67/1.52  
% 7.67/1.52  fof(f114,plain,(
% 7.67/1.52    v1_funct_1(sK4)),
% 7.67/1.52    inference(cnf_transformation,[],[f70])).
% 7.67/1.52  
% 7.67/1.52  fof(f17,axiom,(
% 7.67/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f42,plain,(
% 7.67/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.52    inference(ennf_transformation,[],[f17])).
% 7.67/1.52  
% 7.67/1.52  fof(f98,plain,(
% 7.67/1.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.52    inference(cnf_transformation,[],[f42])).
% 7.67/1.52  
% 7.67/1.52  fof(f23,axiom,(
% 7.67/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f49,plain,(
% 7.67/1.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.52    inference(ennf_transformation,[],[f23])).
% 7.67/1.52  
% 7.67/1.52  fof(f50,plain,(
% 7.67/1.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.52    inference(flattening,[],[f49])).
% 7.67/1.52  
% 7.67/1.52  fof(f107,plain,(
% 7.67/1.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f50])).
% 7.67/1.52  
% 7.67/1.52  fof(f24,axiom,(
% 7.67/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f51,plain,(
% 7.67/1.52    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.67/1.52    inference(ennf_transformation,[],[f24])).
% 7.67/1.52  
% 7.67/1.52  fof(f52,plain,(
% 7.67/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.67/1.52    inference(flattening,[],[f51])).
% 7.67/1.52  
% 7.67/1.52  fof(f110,plain,(
% 7.67/1.52    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f52])).
% 7.67/1.52  
% 7.67/1.52  fof(f106,plain,(
% 7.67/1.52    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f50])).
% 7.67/1.52  
% 7.67/1.52  fof(f97,plain,(
% 7.67/1.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f41])).
% 7.67/1.52  
% 7.67/1.52  fof(f14,axiom,(
% 7.67/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f36,plain,(
% 7.67/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.52    inference(ennf_transformation,[],[f14])).
% 7.67/1.52  
% 7.67/1.52  fof(f37,plain,(
% 7.67/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.52    inference(flattening,[],[f36])).
% 7.67/1.52  
% 7.67/1.52  fof(f94,plain,(
% 7.67/1.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f37])).
% 7.67/1.52  
% 7.67/1.52  fof(f93,plain,(
% 7.67/1.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f37])).
% 7.67/1.52  
% 7.67/1.52  fof(f112,plain,(
% 7.67/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f52])).
% 7.67/1.52  
% 7.67/1.52  fof(f119,plain,(
% 7.67/1.52    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 7.67/1.52    inference(cnf_transformation,[],[f70])).
% 7.67/1.52  
% 7.67/1.52  fof(f18,axiom,(
% 7.67/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f27,plain,(
% 7.67/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.67/1.52    inference(pure_predicate_removal,[],[f18])).
% 7.67/1.52  
% 7.67/1.52  fof(f43,plain,(
% 7.67/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.52    inference(ennf_transformation,[],[f27])).
% 7.67/1.52  
% 7.67/1.52  fof(f99,plain,(
% 7.67/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.52    inference(cnf_transformation,[],[f43])).
% 7.67/1.52  
% 7.67/1.52  fof(f10,axiom,(
% 7.67/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f32,plain,(
% 7.67/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.67/1.52    inference(ennf_transformation,[],[f10])).
% 7.67/1.52  
% 7.67/1.52  fof(f68,plain,(
% 7.67/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.67/1.52    inference(nnf_transformation,[],[f32])).
% 7.67/1.52  
% 7.67/1.52  fof(f88,plain,(
% 7.67/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f68])).
% 7.67/1.52  
% 7.67/1.52  fof(f7,axiom,(
% 7.67/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f65,plain,(
% 7.67/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.67/1.52    inference(nnf_transformation,[],[f7])).
% 7.67/1.52  
% 7.67/1.52  fof(f66,plain,(
% 7.67/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.67/1.52    inference(flattening,[],[f65])).
% 7.67/1.52  
% 7.67/1.52  fof(f84,plain,(
% 7.67/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.67/1.52    inference(cnf_transformation,[],[f66])).
% 7.67/1.52  
% 7.67/1.52  fof(f122,plain,(
% 7.67/1.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.67/1.52    inference(equality_resolution,[],[f84])).
% 7.67/1.52  
% 7.67/1.52  fof(f83,plain,(
% 7.67/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.67/1.52    inference(cnf_transformation,[],[f66])).
% 7.67/1.52  
% 7.67/1.52  fof(f123,plain,(
% 7.67/1.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.67/1.52    inference(equality_resolution,[],[f83])).
% 7.67/1.52  
% 7.67/1.52  fof(f8,axiom,(
% 7.67/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f67,plain,(
% 7.67/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.67/1.52    inference(nnf_transformation,[],[f8])).
% 7.67/1.52  
% 7.67/1.52  fof(f86,plain,(
% 7.67/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f67])).
% 7.67/1.52  
% 7.67/1.52  fof(f3,axiom,(
% 7.67/1.52    v1_xboole_0(k1_xboole_0)),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f76,plain,(
% 7.67/1.52    v1_xboole_0(k1_xboole_0)),
% 7.67/1.52    inference(cnf_transformation,[],[f3])).
% 7.67/1.52  
% 7.67/1.52  fof(f22,axiom,(
% 7.67/1.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f48,plain,(
% 7.67/1.52    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.67/1.52    inference(ennf_transformation,[],[f22])).
% 7.67/1.52  
% 7.67/1.52  fof(f104,plain,(
% 7.67/1.52    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f48])).
% 7.67/1.52  
% 7.67/1.52  fof(f21,axiom,(
% 7.67/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f46,plain,(
% 7.67/1.52    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.52    inference(ennf_transformation,[],[f21])).
% 7.67/1.52  
% 7.67/1.52  fof(f47,plain,(
% 7.67/1.52    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.52    inference(flattening,[],[f46])).
% 7.67/1.52  
% 7.67/1.52  fof(f103,plain,(
% 7.67/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.52    inference(cnf_transformation,[],[f47])).
% 7.67/1.52  
% 7.67/1.52  fof(f2,axiom,(
% 7.67/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f28,plain,(
% 7.67/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.67/1.52    inference(ennf_transformation,[],[f2])).
% 7.67/1.52  
% 7.67/1.52  fof(f59,plain,(
% 7.67/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.67/1.52    inference(nnf_transformation,[],[f28])).
% 7.67/1.52  
% 7.67/1.52  fof(f60,plain,(
% 7.67/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.67/1.52    inference(rectify,[],[f59])).
% 7.67/1.52  
% 7.67/1.52  fof(f61,plain,(
% 7.67/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.67/1.52    introduced(choice_axiom,[])).
% 7.67/1.52  
% 7.67/1.52  fof(f62,plain,(
% 7.67/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.67/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).
% 7.67/1.52  
% 7.67/1.52  fof(f74,plain,(
% 7.67/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f62])).
% 7.67/1.52  
% 7.67/1.52  fof(f1,axiom,(
% 7.67/1.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f55,plain,(
% 7.67/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.67/1.52    inference(nnf_transformation,[],[f1])).
% 7.67/1.52  
% 7.67/1.52  fof(f56,plain,(
% 7.67/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.67/1.52    inference(rectify,[],[f55])).
% 7.67/1.52  
% 7.67/1.52  fof(f57,plain,(
% 7.67/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.67/1.52    introduced(choice_axiom,[])).
% 7.67/1.52  
% 7.67/1.52  fof(f58,plain,(
% 7.67/1.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.67/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).
% 7.67/1.52  
% 7.67/1.52  fof(f72,plain,(
% 7.67/1.52    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f58])).
% 7.67/1.52  
% 7.67/1.52  fof(f9,axiom,(
% 7.67/1.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.67/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.52  
% 7.67/1.52  fof(f31,plain,(
% 7.67/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.67/1.52    inference(ennf_transformation,[],[f9])).
% 7.67/1.52  
% 7.67/1.52  fof(f87,plain,(
% 7.67/1.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f31])).
% 7.67/1.52  
% 7.67/1.52  fof(f71,plain,(
% 7.67/1.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.67/1.52    inference(cnf_transformation,[],[f58])).
% 7.67/1.52  
% 7.67/1.52  fof(f85,plain,(
% 7.67/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.67/1.52    inference(cnf_transformation,[],[f67])).
% 7.67/1.52  
% 7.67/1.52  cnf(c_46,negated_conjecture,
% 7.67/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.67/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1748,plain,
% 7.67/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_30,plain,
% 7.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1756,plain,
% 7.67/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.67/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_3643,plain,
% 7.67/1.52      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_1748,c_1756]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_44,negated_conjecture,
% 7.67/1.52      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 7.67/1.52      inference(cnf_transformation,[],[f118]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_3646,plain,
% 7.67/1.52      ( k2_relat_1(sK4) = sK3 ),
% 7.67/1.52      inference(light_normalisation,[status(thm)],[c_3643,c_44]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_26,plain,
% 7.67/1.52      ( ~ v2_funct_1(X0)
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_relat_1(X0)
% 7.67/1.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_45,negated_conjecture,
% 7.67/1.52      ( v2_funct_1(sK4) ),
% 7.67/1.52      inference(cnf_transformation,[],[f117]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_566,plain,
% 7.67/1.52      ( ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_relat_1(X0)
% 7.67/1.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.67/1.52      | sK4 != X0 ),
% 7.67/1.52      inference(resolution_lifted,[status(thm)],[c_26,c_45]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_567,plain,
% 7.67/1.52      ( ~ v1_funct_1(sK4)
% 7.67/1.52      | ~ v1_relat_1(sK4)
% 7.67/1.52      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 7.67/1.52      inference(unflattening,[status(thm)],[c_566]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_48,negated_conjecture,
% 7.67/1.52      ( v1_funct_1(sK4) ),
% 7.67/1.52      inference(cnf_transformation,[],[f114]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_569,plain,
% 7.67/1.52      ( ~ v1_relat_1(sK4)
% 7.67/1.52      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_567,c_48]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1743,plain,
% 7.67/1.52      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 7.67/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_27,plain,
% 7.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | v1_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1828,plain,
% 7.67/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.67/1.52      | v1_relat_1(sK4) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_27]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1853,plain,
% 7.67/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.67/1.52      | v1_relat_1(sK4) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_1828]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2170,plain,
% 7.67/1.52      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_1743,c_48,c_46,c_567,c_1853]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_3654,plain,
% 7.67/1.52      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 7.67/1.52      inference(demodulation,[status(thm)],[c_3646,c_2170]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_34,plain,
% 7.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f107]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1755,plain,
% 7.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_40,plain,
% 7.67/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.67/1.52      | v1_funct_2(X0,X1,X3)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | ~ r1_tarski(X2,X3)
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | k1_xboole_0 = X2 ),
% 7.67/1.52      inference(cnf_transformation,[],[f110]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1750,plain,
% 7.67/1.52      ( k1_xboole_0 = X0
% 7.67/1.52      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.67/1.52      | v1_funct_2(X1,X2,X3) = iProver_top
% 7.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.67/1.52      | r1_tarski(X0,X3) != iProver_top
% 7.67/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4669,plain,
% 7.67/1.52      ( k2_relat_1(X0) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 7.67/1.52      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 7.67/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_1755,c_1750]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_35,plain,
% 7.67/1.52      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f106]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_61,plain,
% 7.67/1.52      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32317,plain,
% 7.67/1.52      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 7.67/1.52      | k2_relat_1(X0) = k1_xboole_0
% 7.67/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_4669,c_61]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32318,plain,
% 7.67/1.52      ( k2_relat_1(X0) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 7.67/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(renaming,[status(thm)],[c_32317]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32323,plain,
% 7.67/1.52      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 7.67/1.52      | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_3654,c_32318]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_25,plain,
% 7.67/1.52      ( ~ v2_funct_1(X0)
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_relat_1(X0)
% 7.67/1.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_580,plain,
% 7.67/1.52      ( ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_relat_1(X0)
% 7.67/1.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.67/1.52      | sK4 != X0 ),
% 7.67/1.52      inference(resolution_lifted,[status(thm)],[c_25,c_45]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_581,plain,
% 7.67/1.52      ( ~ v1_funct_1(sK4)
% 7.67/1.52      | ~ v1_relat_1(sK4)
% 7.67/1.52      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 7.67/1.52      inference(unflattening,[status(thm)],[c_580]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_583,plain,
% 7.67/1.52      ( ~ v1_relat_1(sK4)
% 7.67/1.52      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_581,c_48]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1742,plain,
% 7.67/1.52      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 7.67/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2010,plain,
% 7.67/1.52      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_1742,c_48,c_46,c_581,c_1853]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32329,plain,
% 7.67/1.52      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(light_normalisation,[status(thm)],[c_32323,c_2010]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32330,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(demodulation,[status(thm)],[c_32329,c_2010]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_49,plain,
% 7.67/1.52      ( v1_funct_1(sK4) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_51,plain,
% 7.67/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_22,plain,
% 7.67/1.52      ( ~ v1_funct_1(X0)
% 7.67/1.52      | v1_funct_1(k2_funct_1(X0))
% 7.67/1.52      | ~ v1_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1820,plain,
% 7.67/1.52      ( v1_funct_1(k2_funct_1(sK4))
% 7.67/1.52      | ~ v1_funct_1(sK4)
% 7.67/1.52      | ~ v1_relat_1(sK4) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_22]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1821,plain,
% 7.67/1.52      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 7.67/1.52      | v1_funct_1(sK4) != iProver_top
% 7.67/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1854,plain,
% 7.67/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.67/1.52      | v1_relat_1(sK4) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1853]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_23,plain,
% 7.67/1.52      ( ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_relat_1(X0)
% 7.67/1.52      | v1_relat_1(k2_funct_1(X0)) ),
% 7.67/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2347,plain,
% 7.67/1.52      ( ~ v1_funct_1(sK4)
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4))
% 7.67/1.52      | ~ v1_relat_1(sK4) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_23]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2348,plain,
% 7.67/1.52      ( v1_funct_1(sK4) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 7.67/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_2347]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1754,plain,
% 7.67/1.52      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4014,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) = iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_2010,c_1754]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4018,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(light_normalisation,[status(thm)],[c_4014,c_3654]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4660,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_2010,c_1755]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4671,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(light_normalisation,[status(thm)],[c_4660,c_3654]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_5251,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_4671,c_49,c_51,c_1821,c_1854,c_2348]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_5261,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_5251,c_1750]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32535,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_32330,c_49,c_51,c_1821,c_1854,c_2348,c_4018,c_5261]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_38,plain,
% 7.67/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.67/1.52      | ~ r1_tarski(X2,X3)
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | k1_xboole_0 = X2 ),
% 7.67/1.52      inference(cnf_transformation,[],[f112]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1752,plain,
% 7.67/1.52      ( k1_xboole_0 = X0
% 7.67/1.52      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.67/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.67/1.52      | r1_tarski(X0,X3) != iProver_top
% 7.67/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4668,plain,
% 7.67/1.52      ( k2_relat_1(X0) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 7.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.67/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_1755,c_1752]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_31517,plain,
% 7.67/1.52      ( k2_relat_1(X0) = k1_xboole_0
% 7.67/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.67/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.67/1.52      | v1_funct_1(X0) != iProver_top
% 7.67/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_4668,c_61]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_31524,plain,
% 7.67/1.52      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 7.67/1.52      | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_3654,c_31517]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_31539,plain,
% 7.67/1.52      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(light_normalisation,[status(thm)],[c_31524,c_2010]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_31540,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(demodulation,[status(thm)],[c_31539,c_2010]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_31947,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_31540,c_49,c_51,c_1821,c_1854,c_2348]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_43,negated_conjecture,
% 7.67/1.52      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 7.67/1.52      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.67/1.52      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 7.67/1.52      inference(cnf_transformation,[],[f119]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1749,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_53,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2005,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_1749,c_49,c_51,c_53,c_1821,c_1854]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2006,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 7.67/1.52      inference(renaming,[status(thm)],[c_2005]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_31959,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_31947,c_2006]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_28,plain,
% 7.67/1.52      ( v4_relat_1(X0,X1)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.67/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_18,plain,
% 7.67/1.52      ( ~ v4_relat_1(X0,X1)
% 7.67/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.67/1.52      | ~ v1_relat_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_600,plain,
% 7.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.67/1.52      | ~ v1_relat_1(X0) ),
% 7.67/1.52      inference(resolution,[status(thm)],[c_28,c_18]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_604,plain,
% 7.67/1.52      ( r1_tarski(k1_relat_1(X0),X1)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_600,c_27]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_605,plain,
% 7.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.67/1.52      inference(renaming,[status(thm)],[c_604]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1741,plain,
% 7.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2197,plain,
% 7.67/1.52      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_1748,c_1741]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32099,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 7.67/1.52      | k1_relat_1(sK4) = k1_xboole_0 ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_31959,c_2197]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32100,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
% 7.67/1.52      inference(renaming,[status(thm)],[c_32099]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32539,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0
% 7.67/1.52      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_32535,c_32100]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32587,plain,
% 7.67/1.52      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_32539,c_2197]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32644,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 7.67/1.52      inference(demodulation,[status(thm)],[c_32587,c_5251]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_11,plain,
% 7.67/1.52      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.67/1.52      inference(cnf_transformation,[],[f122]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_32656,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.67/1.52      inference(demodulation,[status(thm)],[c_32644,c_11]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_12,plain,
% 7.67/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.67/1.52      inference(cnf_transformation,[],[f123]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_14,plain,
% 7.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.67/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1766,plain,
% 7.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.67/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2571,plain,
% 7.67/1.52      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_1766,c_1741]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_5955,plain,
% 7.67/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.67/1.52      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_12,c_2571]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_6054,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top
% 7.67/1.52      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_3654,c_5955]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_5,plain,
% 7.67/1.52      ( v1_xboole_0(k1_xboole_0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_136,plain,
% 7.67/1.52      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_33,plain,
% 7.67/1.52      ( v1_partfun1(X0,X1)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | ~ v1_xboole_0(X1) ),
% 7.67/1.52      inference(cnf_transformation,[],[f104]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_31,plain,
% 7.67/1.52      ( v1_funct_2(X0,X1,X2)
% 7.67/1.52      | ~ v1_partfun1(X0,X1)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | ~ v1_funct_1(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_540,plain,
% 7.67/1.52      ( v1_funct_2(X0,X1,X2)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_xboole_0(X1) ),
% 7.67/1.52      inference(resolution,[status(thm)],[c_33,c_31]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_544,plain,
% 7.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | v1_funct_2(X0,X1,X2)
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_xboole_0(X1) ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_540,c_33,c_31]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_545,plain,
% 7.67/1.52      ( v1_funct_2(X0,X1,X2)
% 7.67/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.52      | ~ v1_funct_1(X0)
% 7.67/1.52      | ~ v1_xboole_0(X1) ),
% 7.67/1.52      inference(renaming,[status(thm)],[c_544]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1881,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 7.67/1.52      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.67/1.52      | ~ v1_funct_1(k2_funct_1(sK4))
% 7.67/1.52      | ~ v1_xboole_0(sK3) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_545]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1882,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) = iProver_top
% 7.67/1.52      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.67/1.52      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_xboole_0(sK3) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1944,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 7.67/1.52      | ~ r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_14]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1945,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top
% 7.67/1.52      | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_3,plain,
% 7.67/1.52      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2013,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
% 7.67/1.52      | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2017,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) = iProver_top
% 7.67/1.52      | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_0,plain,
% 7.67/1.52      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.67/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2285,plain,
% 7.67/1.52      ( r2_hidden(sK0(sK3),sK3) | v1_xboole_0(sK3) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2286,plain,
% 7.67/1.52      ( r2_hidden(sK0(sK3),sK3) = iProver_top
% 7.67/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_2285]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2364,plain,
% 7.67/1.52      ( r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4))
% 7.67/1.52      | v1_xboole_0(k2_funct_1(sK4)) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2365,plain,
% 7.67/1.52      ( r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4)) = iProver_top
% 7.67/1.52      | v1_xboole_0(k2_funct_1(sK4)) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_2364]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_16,plain,
% 7.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.67/1.52      | ~ r2_hidden(X2,X0)
% 7.67/1.52      | ~ v1_xboole_0(X1) ),
% 7.67/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_330,plain,
% 7.67/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.67/1.52      inference(prop_impl,[status(thm)],[c_14]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_331,plain,
% 7.67/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.67/1.52      inference(renaming,[status(thm)],[c_330]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_400,plain,
% 7.67/1.52      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 7.67/1.52      inference(bin_hyper_res,[status(thm)],[c_16,c_331]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2669,plain,
% 7.67/1.52      ( ~ r1_tarski(sK3,X0)
% 7.67/1.52      | ~ r2_hidden(sK0(sK3),sK3)
% 7.67/1.52      | ~ v1_xboole_0(X0) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_400]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2670,plain,
% 7.67/1.52      ( r1_tarski(sK3,X0) != iProver_top
% 7.67/1.52      | r2_hidden(sK0(sK3),sK3) != iProver_top
% 7.67/1.52      | v1_xboole_0(X0) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_2669]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2672,plain,
% 7.67/1.52      ( r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.67/1.52      | r2_hidden(sK0(sK3),sK3) != iProver_top
% 7.67/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_2670]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2760,plain,
% 7.67/1.52      ( ~ r1_tarski(k2_funct_1(sK4),X0)
% 7.67/1.52      | ~ r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4))
% 7.67/1.52      | ~ v1_xboole_0(X0) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_400]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2761,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),X0) != iProver_top
% 7.67/1.52      | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_xboole_0(X0) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_2760]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2763,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top
% 7.67/1.52      | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_2761]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1773,plain,
% 7.67/1.52      ( r1_tarski(X0,X1) = iProver_top
% 7.67/1.52      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1,plain,
% 7.67/1.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.67/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_1775,plain,
% 7.67/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.67/1.52      | v1_xboole_0(X1) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2687,plain,
% 7.67/1.52      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_1773,c_1775]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2572,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 7.67/1.52      | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_1766,c_2006]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_2795,plain,
% 7.67/1.52      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 7.67/1.52      | v1_xboole_0(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.52      inference(superposition,[status(thm)],[c_2687,c_2572]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4938,plain,
% 7.67/1.52      ( ~ r1_tarski(k2_funct_1(sK4),X0)
% 7.67/1.52      | ~ r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4))
% 7.67/1.52      | ~ v1_xboole_0(X0) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_400]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4939,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),X0) != iProver_top
% 7.67/1.52      | r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_xboole_0(X0) != iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_4938]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4941,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top
% 7.67/1.52      | r2_hidden(sK0(k2_funct_1(sK4)),k2_funct_1(sK4)) != iProver_top
% 7.67/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_4939]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_6283,plain,
% 7.67/1.52      ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top ),
% 7.67/1.52      inference(global_propositional_subsumption,
% 7.67/1.52                [status(thm)],
% 7.67/1.52                [c_6054,c_49,c_51,c_136,c_1821,c_1854,c_1882,c_1945,
% 7.67/1.52                 c_2017,c_2286,c_2365,c_2672,c_2763,c_2795,c_4941]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_15,plain,
% 7.67/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.67/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4495,plain,
% 7.67/1.52      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0))
% 7.67/1.52      | r1_tarski(k2_funct_1(sK4),X0) ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_15]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4496,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0)) != iProver_top
% 7.67/1.52      | r1_tarski(k2_funct_1(sK4),X0) = iProver_top ),
% 7.67/1.52      inference(predicate_to_equality,[status(thm)],[c_4495]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(c_4498,plain,
% 7.67/1.52      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.67/1.52      | r1_tarski(k2_funct_1(sK4),k1_xboole_0) = iProver_top ),
% 7.67/1.52      inference(instantiation,[status(thm)],[c_4496]) ).
% 7.67/1.52  
% 7.67/1.52  cnf(contradiction,plain,
% 7.67/1.52      ( $false ),
% 7.67/1.52      inference(minisat,[status(thm)],[c_32656,c_6283,c_4498]) ).
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.52  
% 7.67/1.52  ------                               Statistics
% 7.67/1.52  
% 7.67/1.52  ------ General
% 7.67/1.52  
% 7.67/1.52  abstr_ref_over_cycles:                  0
% 7.67/1.52  abstr_ref_under_cycles:                 0
% 7.67/1.52  gc_basic_clause_elim:                   0
% 7.67/1.52  forced_gc_time:                         0
% 7.67/1.52  parsing_time:                           0.011
% 7.67/1.52  unif_index_cands_time:                  0.
% 7.67/1.52  unif_index_add_time:                    0.
% 7.67/1.52  orderings_time:                         0.
% 7.67/1.52  out_proof_time:                         0.017
% 7.67/1.52  total_time:                             0.883
% 7.67/1.52  num_of_symbols:                         56
% 7.67/1.52  num_of_terms:                           30146
% 7.67/1.52  
% 7.67/1.52  ------ Preprocessing
% 7.67/1.52  
% 7.67/1.52  num_of_splits:                          0
% 7.67/1.52  num_of_split_atoms:                     0
% 7.67/1.52  num_of_reused_defs:                     0
% 7.67/1.52  num_eq_ax_congr_red:                    31
% 7.67/1.52  num_of_sem_filtered_clauses:            1
% 7.67/1.52  num_of_subtypes:                        0
% 7.67/1.52  monotx_restored_types:                  0
% 7.67/1.52  sat_num_of_epr_types:                   0
% 7.67/1.52  sat_num_of_non_cyclic_types:            0
% 7.67/1.52  sat_guarded_non_collapsed_types:        0
% 7.67/1.52  num_pure_diseq_elim:                    0
% 7.67/1.52  simp_replaced_by:                       0
% 7.67/1.52  res_preprocessed:                       197
% 7.67/1.52  prep_upred:                             0
% 7.67/1.52  prep_unflattend:                        2
% 7.67/1.52  smt_new_axioms:                         0
% 7.67/1.52  pred_elim_cands:                        7
% 7.67/1.52  pred_elim:                              3
% 7.67/1.52  pred_elim_cl:                           4
% 7.67/1.52  pred_elim_cycles:                       5
% 7.67/1.52  merged_defs:                            8
% 7.67/1.52  merged_defs_ncl:                        0
% 7.67/1.52  bin_hyper_res:                          9
% 7.67/1.52  prep_cycles:                            4
% 7.67/1.52  pred_elim_time:                         0.003
% 7.67/1.52  splitting_time:                         0.
% 7.67/1.52  sem_filter_time:                        0.
% 7.67/1.52  monotx_time:                            0.
% 7.67/1.52  subtype_inf_time:                       0.
% 7.67/1.52  
% 7.67/1.52  ------ Problem properties
% 7.67/1.52  
% 7.67/1.52  clauses:                                40
% 7.67/1.52  conjectures:                            5
% 7.67/1.52  epr:                                    10
% 7.67/1.52  horn:                                   35
% 7.67/1.52  ground:                                 8
% 7.67/1.52  unary:                                  8
% 7.67/1.52  binary:                                 15
% 7.67/1.52  lits:                                   101
% 7.67/1.52  lits_eq:                                16
% 7.67/1.52  fd_pure:                                0
% 7.67/1.52  fd_pseudo:                              0
% 7.67/1.52  fd_cond:                                4
% 7.67/1.52  fd_pseudo_cond:                         2
% 7.67/1.52  ac_symbols:                             0
% 7.67/1.52  
% 7.67/1.52  ------ Propositional Solver
% 7.67/1.52  
% 7.67/1.52  prop_solver_calls:                      36
% 7.67/1.52  prop_fast_solver_calls:                 2285
% 7.67/1.52  smt_solver_calls:                       0
% 7.67/1.52  smt_fast_solver_calls:                  0
% 7.67/1.52  prop_num_of_clauses:                    14095
% 7.67/1.52  prop_preprocess_simplified:             22894
% 7.67/1.52  prop_fo_subsumed:                       107
% 7.67/1.52  prop_solver_time:                       0.
% 7.67/1.52  smt_solver_time:                        0.
% 7.67/1.52  smt_fast_solver_time:                   0.
% 7.67/1.52  prop_fast_solver_time:                  0.
% 7.67/1.52  prop_unsat_core_time:                   0.001
% 7.67/1.52  
% 7.67/1.52  ------ QBF
% 7.67/1.52  
% 7.67/1.52  qbf_q_res:                              0
% 7.67/1.52  qbf_num_tautologies:                    0
% 7.67/1.52  qbf_prep_cycles:                        0
% 7.67/1.52  
% 7.67/1.52  ------ BMC1
% 7.67/1.52  
% 7.67/1.52  bmc1_current_bound:                     -1
% 7.67/1.52  bmc1_last_solved_bound:                 -1
% 7.67/1.52  bmc1_unsat_core_size:                   -1
% 7.67/1.52  bmc1_unsat_core_parents_size:           -1
% 7.67/1.52  bmc1_merge_next_fun:                    0
% 7.67/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.52  
% 7.67/1.52  ------ Instantiation
% 7.67/1.52  
% 7.67/1.52  inst_num_of_clauses:                    3227
% 7.67/1.52  inst_num_in_passive:                    1438
% 7.67/1.52  inst_num_in_active:                     1365
% 7.67/1.52  inst_num_in_unprocessed:                427
% 7.67/1.52  inst_num_of_loops:                      2040
% 7.67/1.52  inst_num_of_learning_restarts:          0
% 7.67/1.52  inst_num_moves_active_passive:          668
% 7.67/1.52  inst_lit_activity:                      0
% 7.67/1.52  inst_lit_activity_moves:                0
% 7.67/1.52  inst_num_tautologies:                   0
% 7.67/1.52  inst_num_prop_implied:                  0
% 7.67/1.52  inst_num_existing_simplified:           0
% 7.67/1.52  inst_num_eq_res_simplified:             0
% 7.67/1.52  inst_num_child_elim:                    0
% 7.67/1.52  inst_num_of_dismatching_blockings:      2212
% 7.67/1.52  inst_num_of_non_proper_insts:           5400
% 7.67/1.52  inst_num_of_duplicates:                 0
% 7.67/1.52  inst_inst_num_from_inst_to_res:         0
% 7.67/1.52  inst_dismatching_checking_time:         0.
% 7.67/1.52  
% 7.67/1.52  ------ Resolution
% 7.67/1.52  
% 7.67/1.52  res_num_of_clauses:                     0
% 7.67/1.52  res_num_in_passive:                     0
% 7.67/1.52  res_num_in_active:                      0
% 7.67/1.52  res_num_of_loops:                       201
% 7.67/1.52  res_forward_subset_subsumed:            184
% 7.67/1.52  res_backward_subset_subsumed:           6
% 7.67/1.52  res_forward_subsumed:                   0
% 7.67/1.52  res_backward_subsumed:                  0
% 7.67/1.52  res_forward_subsumption_resolution:     0
% 7.67/1.52  res_backward_subsumption_resolution:    0
% 7.67/1.52  res_clause_to_clause_subsumption:       3377
% 7.67/1.52  res_orphan_elimination:                 0
% 7.67/1.52  res_tautology_del:                      362
% 7.67/1.52  res_num_eq_res_simplified:              0
% 7.67/1.52  res_num_sel_changes:                    0
% 7.67/1.52  res_moves_from_active_to_pass:          0
% 7.67/1.52  
% 7.67/1.52  ------ Superposition
% 7.67/1.52  
% 7.67/1.52  sup_time_total:                         0.
% 7.67/1.52  sup_time_generating:                    0.
% 7.67/1.52  sup_time_sim_full:                      0.
% 7.67/1.52  sup_time_sim_immed:                     0.
% 7.67/1.52  
% 7.67/1.52  sup_num_of_clauses:                     1144
% 7.67/1.52  sup_num_in_active:                      269
% 7.67/1.52  sup_num_in_passive:                     875
% 7.67/1.52  sup_num_of_loops:                       406
% 7.67/1.52  sup_fw_superposition:                   1109
% 7.67/1.52  sup_bw_superposition:                   874
% 7.67/1.52  sup_immediate_simplified:               546
% 7.67/1.52  sup_given_eliminated:                   1
% 7.67/1.52  comparisons_done:                       0
% 7.67/1.52  comparisons_avoided:                    9
% 7.67/1.52  
% 7.67/1.52  ------ Simplifications
% 7.67/1.52  
% 7.67/1.52  
% 7.67/1.52  sim_fw_subset_subsumed:                 151
% 7.67/1.52  sim_bw_subset_subsumed:                 45
% 7.67/1.52  sim_fw_subsumed:                        71
% 7.67/1.52  sim_bw_subsumed:                        35
% 7.67/1.52  sim_fw_subsumption_res:                 0
% 7.67/1.52  sim_bw_subsumption_res:                 0
% 7.67/1.52  sim_tautology_del:                      30
% 7.67/1.52  sim_eq_tautology_del:                   129
% 7.67/1.52  sim_eq_res_simp:                        0
% 7.67/1.52  sim_fw_demodulated:                     183
% 7.67/1.52  sim_bw_demodulated:                     111
% 7.67/1.52  sim_light_normalised:                   233
% 7.67/1.52  sim_joinable_taut:                      0
% 7.67/1.52  sim_joinable_simp:                      0
% 7.67/1.52  sim_ac_normalised:                      0
% 7.67/1.52  sim_smt_subsumption:                    0
% 7.67/1.52  
%------------------------------------------------------------------------------
