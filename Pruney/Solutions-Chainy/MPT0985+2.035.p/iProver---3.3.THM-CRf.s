%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:26 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  195 (10504 expanded)
%              Number of clauses        :  142 (3774 expanded)
%              Number of leaves         :   15 (1922 expanded)
%              Depth                    :   33
%              Number of atoms          :  622 (54087 expanded)
%              Number of equality atoms :  290 (10003 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f32])).

fof(f36,plain,
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

fof(f37,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f61])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_343,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_344,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_346,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_29])).

cnf(c_732,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1140,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_1389,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1140,c_27,c_732,c_1310])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_745,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),k2_relat_1(X0_47))))
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1128,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),k2_relat_1(X0_47)))) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_1772,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1389,c_1128])).

cnf(c_737,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | k2_relset_1(X0_50,X1_50,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1127,plain,
    ( k2_relset_1(X0_50,X1_50,X0_47) = k2_relat_1(X0_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_1569,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1135,c_1127])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_738,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1570,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1569,c_738])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_329,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_330,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_332,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_29])).

cnf(c_733,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_1139,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_1341,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1139,c_27,c_733,c_1310])).

cnf(c_1572,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1570,c_1341])).

cnf(c_1791,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1772,c_1572])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_749,plain,
    ( ~ v1_funct_1(X0_47)
    | v1_funct_1(k2_funct_1(X0_47))
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_779,plain,
    ( v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(k2_funct_1(X0_47)) = iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_781,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_748,plain,
    ( ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X0_47)
    | v1_relat_1(k2_funct_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_782,plain,
    ( v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(k2_funct_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_784,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_1311,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_2278,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_30,c_32,c_781,c_784,c_1311])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_740,plain,
    ( ~ v1_funct_2(X0_47,X0_50,X1_50)
    | v1_funct_2(X0_47,X0_50,X2_50)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ r1_tarski(X1_50,X2_50)
    | ~ v1_funct_1(X0_47)
    | k1_xboole_0 = X1_50 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1133,plain,
    ( k1_xboole_0 = X0_50
    | v1_funct_2(X0_47,X1_50,X0_50) != iProver_top
    | v1_funct_2(X0_47,X1_50,X2_50) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | r1_tarski(X0_50,X2_50) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_2286,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0_50) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_1133])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_744,plain,
    ( v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47))
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1129,plain,
    ( v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47)) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_1870,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1389,c_1129])).

cnf(c_1874,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1870,c_1572])).

cnf(c_3419,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2286,c_30,c_32,c_781,c_784,c_1311,c_1874])).

cnf(c_3420,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0_50) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3419])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_742,plain,
    ( ~ v1_funct_2(X0_47,X0_50,X1_50)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X2_50)))
    | ~ r1_tarski(X1_50,X2_50)
    | ~ v1_funct_1(X0_47)
    | k1_xboole_0 = X1_50 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1131,plain,
    ( k1_xboole_0 = X0_50
    | v1_funct_2(X0_47,X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) = iProver_top
    | r1_tarski(X0_50,X2_50) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_2374,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_1131])).

cnf(c_3429,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) = iProver_top
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2374,c_30,c_32,c_781,c_784,c_1311,c_1874])).

cnf(c_3430,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3429])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_739,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1134,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_34,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1334,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1134,c_30,c_32,c_34,c_781,c_1311])).

cnf(c_1335,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1334])).

cnf(c_3438,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3430,c_1335])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_2])).

cnf(c_367,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_9])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_367])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | r1_tarski(k1_relat_1(X0_47),X0_50) ),
    inference(subtyping,[status(esa)],[c_368])).

cnf(c_1313,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1314,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_3577,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3438,c_32,c_1314])).

cnf(c_3578,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3577])).

cnf(c_3583,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3420,c_3578])).

cnf(c_3586,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3583,c_32,c_1314])).

cnf(c_3593,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3586,c_2278])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_751,plain,
    ( ~ v1_relat_1(X0_47)
    | k2_relat_1(X0_47) != k1_xboole_0
    | k1_relat_1(X0_47) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1122,plain,
    ( k2_relat_1(X0_47) != k1_xboole_0
    | k1_relat_1(X0_47) = k1_xboole_0
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_1464,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1389,c_1122])).

cnf(c_1465,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1464,c_1341])).

cnf(c_1715,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1465,c_30,c_32,c_784,c_1311])).

cnf(c_1716,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1715])).

cnf(c_1717,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1716,c_1570])).

cnf(c_3600,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3586,c_1717])).

cnf(c_3604,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3600])).

cnf(c_3623,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3593,c_3604])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_funct_2(X0,k1_xboole_0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_741,plain,
    ( ~ v1_funct_2(X0_47,k1_xboole_0,X0_50)
    | v1_funct_2(X0_47,k1_xboole_0,X1_50)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50)))
    | ~ r1_tarski(X0_50,X1_50)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1132,plain,
    ( v1_funct_2(X0_47,k1_xboole_0,X0_50) != iProver_top
    | v1_funct_2(X0_47,k1_xboole_0,X1_50) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) != iProver_top
    | r1_tarski(X0_50,X1_50) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_5560,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0_50) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3623,c_1132])).

cnf(c_755,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_772,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_756,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1537,plain,
    ( X0_50 != X1_50
    | X0_50 = k1_relat_1(sK2)
    | k1_relat_1(sK2) != X1_50 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1538,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_1607,plain,
    ( k2_relat_1(X0_47) = k2_relat_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_1609,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_1652,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_relat_1(X0_47)
    | k2_relat_1(X0_47) != X1_50 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1653,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1927,plain,
    ( X0_50 = k2_relat_1(k2_funct_1(sK2))
    | X0_50 != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1928,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_1610,plain,
    ( X0_50 != X1_50
    | k2_relat_1(X0_47) != X1_50
    | k2_relat_1(X0_47) = X0_50 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1896,plain,
    ( X0_50 != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = X0_50
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_2064,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2183,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_2186,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2183])).

cnf(c_1900,plain,
    ( X0_50 != k2_relat_1(X0_47)
    | k2_relat_1(X0_47) = X0_50
    | k2_relat_1(X0_47) != k2_relat_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_2216,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1900])).

cnf(c_762,plain,
    ( ~ v1_funct_2(X0_47,X0_50,X1_50)
    | v1_funct_2(X0_47,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_1399,plain,
    ( v1_funct_2(X0_47,X0_50,X1_50)
    | ~ v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47))
    | X1_50 != k2_relat_1(X0_47)
    | X0_50 != k1_relat_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1847,plain,
    ( v1_funct_2(X0_47,X0_50,k2_relat_1(X0_47))
    | ~ v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47))
    | X0_50 != k1_relat_1(X0_47)
    | k2_relat_1(X0_47) != k2_relat_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_2328,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_2336,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2328])).

cnf(c_2835,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0_50,X1_50)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | X1_50 != k2_relat_1(k2_funct_1(sK2))
    | X0_50 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_2836,plain,
    ( X0_50 != k2_relat_1(k2_funct_1(sK2))
    | X1_50 != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),X1_50,X0_50) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2835])).

cnf(c_2838,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2836])).

cnf(c_5641,plain,
    ( r1_tarski(k1_xboole_0,X0_50) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5560,c_30,c_27,c_32,c_772,c_781,c_784,c_733,c_732,c_1310,c_1311,c_1314,c_1465,c_1538,c_1609,c_1653,c_1928,c_2064,c_2186,c_2216,c_2336,c_2838,c_3583])).

cnf(c_5642,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0_50) = iProver_top
    | r1_tarski(k1_xboole_0,X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5641])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_743,plain,
    ( ~ v1_funct_2(X0_47,k1_xboole_0,X0_50)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50)))
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1_50)))
    | ~ r1_tarski(X0_50,X1_50)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1130,plain,
    ( v1_funct_2(X0_47,k1_xboole_0,X0_50) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1_50))) = iProver_top
    | r1_tarski(X0_50,X1_50) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_5559,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) = iProver_top
    | r1_tarski(k1_xboole_0,X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3623,c_1130])).

cnf(c_5648,plain,
    ( r1_tarski(k1_xboole_0,X0_50) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5559,c_30,c_27,c_32,c_772,c_781,c_784,c_733,c_732,c_1310,c_1311,c_1314,c_1465,c_1538,c_1609,c_1653,c_1928,c_2064,c_2186,c_2216,c_2336,c_2838,c_3583])).

cnf(c_5649,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) = iProver_top
    | r1_tarski(k1_xboole_0,X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5648])).

cnf(c_4163,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3604,c_1335])).

cnf(c_5662,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5649,c_4163])).

cnf(c_757,plain,
    ( ~ r1_tarski(X0_50,X1_50)
    | r1_tarski(X2_50,X1_50)
    | X2_50 != X0_50 ),
    theory(equality)).

cnf(c_1346,plain,
    ( r1_tarski(X0_50,sK0)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | X0_50 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_1347,plain,
    ( X0_50 != k1_relat_1(sK2)
    | r1_tarski(X0_50,sK0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1346])).

cnf(c_1349,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_5749,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5662,c_32,c_772,c_1314,c_1349,c_1538,c_3583])).

cnf(c_5754,plain,
    ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5642,c_5749])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5754,c_3583,c_1538,c_1349,c_1314,c_772,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.37/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.37/1.02  
% 0.37/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.37/1.02  
% 0.37/1.02  ------  iProver source info
% 0.37/1.02  
% 0.37/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.37/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.37/1.02  git: non_committed_changes: false
% 0.37/1.02  git: last_make_outside_of_git: false
% 0.37/1.02  
% 0.37/1.02  ------ 
% 0.37/1.02  
% 0.37/1.02  ------ Input Options
% 0.37/1.02  
% 0.37/1.02  --out_options                           all
% 0.37/1.02  --tptp_safe_out                         true
% 0.37/1.02  --problem_path                          ""
% 0.37/1.02  --include_path                          ""
% 0.37/1.02  --clausifier                            res/vclausify_rel
% 0.37/1.02  --clausifier_options                    --mode clausify
% 0.37/1.02  --stdin                                 false
% 0.37/1.02  --stats_out                             all
% 0.37/1.02  
% 0.37/1.02  ------ General Options
% 0.37/1.02  
% 0.37/1.02  --fof                                   false
% 0.37/1.02  --time_out_real                         305.
% 0.37/1.02  --time_out_virtual                      -1.
% 0.37/1.02  --symbol_type_check                     false
% 0.37/1.02  --clausify_out                          false
% 0.37/1.02  --sig_cnt_out                           false
% 0.37/1.02  --trig_cnt_out                          false
% 0.37/1.02  --trig_cnt_out_tolerance                1.
% 0.37/1.02  --trig_cnt_out_sk_spl                   false
% 0.37/1.02  --abstr_cl_out                          false
% 0.37/1.02  
% 0.37/1.02  ------ Global Options
% 0.37/1.02  
% 0.37/1.02  --schedule                              default
% 0.37/1.02  --add_important_lit                     false
% 0.37/1.02  --prop_solver_per_cl                    1000
% 0.37/1.02  --min_unsat_core                        false
% 0.37/1.02  --soft_assumptions                      false
% 0.37/1.02  --soft_lemma_size                       3
% 0.37/1.02  --prop_impl_unit_size                   0
% 0.37/1.02  --prop_impl_unit                        []
% 0.37/1.02  --share_sel_clauses                     true
% 0.37/1.02  --reset_solvers                         false
% 0.37/1.02  --bc_imp_inh                            [conj_cone]
% 0.37/1.02  --conj_cone_tolerance                   3.
% 0.37/1.02  --extra_neg_conj                        none
% 0.37/1.02  --large_theory_mode                     true
% 0.37/1.02  --prolific_symb_bound                   200
% 0.37/1.02  --lt_threshold                          2000
% 0.37/1.02  --clause_weak_htbl                      true
% 0.37/1.02  --gc_record_bc_elim                     false
% 0.37/1.02  
% 0.37/1.02  ------ Preprocessing Options
% 0.37/1.02  
% 0.37/1.02  --preprocessing_flag                    true
% 0.37/1.02  --time_out_prep_mult                    0.1
% 0.37/1.02  --splitting_mode                        input
% 0.37/1.02  --splitting_grd                         true
% 0.37/1.02  --splitting_cvd                         false
% 0.37/1.02  --splitting_cvd_svl                     false
% 0.37/1.02  --splitting_nvd                         32
% 0.37/1.02  --sub_typing                            true
% 0.37/1.02  --prep_gs_sim                           true
% 0.37/1.02  --prep_unflatten                        true
% 0.37/1.02  --prep_res_sim                          true
% 0.37/1.02  --prep_upred                            true
% 0.37/1.02  --prep_sem_filter                       exhaustive
% 0.37/1.02  --prep_sem_filter_out                   false
% 0.37/1.02  --pred_elim                             true
% 0.37/1.02  --res_sim_input                         true
% 0.37/1.02  --eq_ax_congr_red                       true
% 0.37/1.02  --pure_diseq_elim                       true
% 0.37/1.02  --brand_transform                       false
% 0.37/1.02  --non_eq_to_eq                          false
% 0.37/1.02  --prep_def_merge                        true
% 0.37/1.02  --prep_def_merge_prop_impl              false
% 0.37/1.02  --prep_def_merge_mbd                    true
% 0.37/1.02  --prep_def_merge_tr_red                 false
% 0.37/1.02  --prep_def_merge_tr_cl                  false
% 0.37/1.02  --smt_preprocessing                     true
% 0.37/1.02  --smt_ac_axioms                         fast
% 0.37/1.02  --preprocessed_out                      false
% 0.37/1.02  --preprocessed_stats                    false
% 0.37/1.02  
% 0.37/1.02  ------ Abstraction refinement Options
% 0.37/1.02  
% 0.37/1.02  --abstr_ref                             []
% 0.37/1.02  --abstr_ref_prep                        false
% 0.37/1.02  --abstr_ref_until_sat                   false
% 0.37/1.02  --abstr_ref_sig_restrict                funpre
% 0.37/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.02  --abstr_ref_under                       []
% 0.37/1.02  
% 0.37/1.02  ------ SAT Options
% 0.37/1.02  
% 0.37/1.02  --sat_mode                              false
% 0.37/1.02  --sat_fm_restart_options                ""
% 0.37/1.02  --sat_gr_def                            false
% 0.37/1.02  --sat_epr_types                         true
% 0.37/1.02  --sat_non_cyclic_types                  false
% 0.37/1.02  --sat_finite_models                     false
% 0.37/1.02  --sat_fm_lemmas                         false
% 0.37/1.02  --sat_fm_prep                           false
% 0.37/1.02  --sat_fm_uc_incr                        true
% 0.37/1.02  --sat_out_model                         small
% 0.37/1.02  --sat_out_clauses                       false
% 0.37/1.02  
% 0.37/1.02  ------ QBF Options
% 0.37/1.02  
% 0.37/1.02  --qbf_mode                              false
% 0.37/1.02  --qbf_elim_univ                         false
% 0.37/1.02  --qbf_dom_inst                          none
% 0.37/1.02  --qbf_dom_pre_inst                      false
% 0.37/1.02  --qbf_sk_in                             false
% 0.37/1.02  --qbf_pred_elim                         true
% 0.37/1.02  --qbf_split                             512
% 0.37/1.02  
% 0.37/1.02  ------ BMC1 Options
% 0.37/1.02  
% 0.37/1.02  --bmc1_incremental                      false
% 0.37/1.02  --bmc1_axioms                           reachable_all
% 0.37/1.02  --bmc1_min_bound                        0
% 0.37/1.02  --bmc1_max_bound                        -1
% 0.37/1.02  --bmc1_max_bound_default                -1
% 0.37/1.02  --bmc1_symbol_reachability              true
% 0.37/1.02  --bmc1_property_lemmas                  false
% 0.37/1.02  --bmc1_k_induction                      false
% 0.37/1.02  --bmc1_non_equiv_states                 false
% 0.37/1.02  --bmc1_deadlock                         false
% 0.37/1.02  --bmc1_ucm                              false
% 0.37/1.02  --bmc1_add_unsat_core                   none
% 0.37/1.02  --bmc1_unsat_core_children              false
% 0.37/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.02  --bmc1_out_stat                         full
% 0.37/1.02  --bmc1_ground_init                      false
% 0.37/1.02  --bmc1_pre_inst_next_state              false
% 0.37/1.02  --bmc1_pre_inst_state                   false
% 0.37/1.02  --bmc1_pre_inst_reach_state             false
% 0.37/1.02  --bmc1_out_unsat_core                   false
% 0.37/1.02  --bmc1_aig_witness_out                  false
% 0.37/1.02  --bmc1_verbose                          false
% 0.37/1.02  --bmc1_dump_clauses_tptp                false
% 0.37/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.02  --bmc1_dump_file                        -
% 0.37/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.02  --bmc1_ucm_extend_mode                  1
% 0.37/1.02  --bmc1_ucm_init_mode                    2
% 0.37/1.02  --bmc1_ucm_cone_mode                    none
% 0.37/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.02  --bmc1_ucm_relax_model                  4
% 0.37/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.02  --bmc1_ucm_layered_model                none
% 0.37/1.02  --bmc1_ucm_max_lemma_size               10
% 0.37/1.02  
% 0.37/1.02  ------ AIG Options
% 0.37/1.02  
% 0.37/1.02  --aig_mode                              false
% 0.37/1.02  
% 0.37/1.02  ------ Instantiation Options
% 0.37/1.02  
% 0.37/1.02  --instantiation_flag                    true
% 0.37/1.02  --inst_sos_flag                         false
% 0.37/1.02  --inst_sos_phase                        true
% 0.37/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.02  --inst_lit_sel_side                     num_symb
% 0.37/1.02  --inst_solver_per_active                1400
% 0.37/1.02  --inst_solver_calls_frac                1.
% 0.37/1.02  --inst_passive_queue_type               priority_queues
% 0.37/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.02  --inst_passive_queues_freq              [25;2]
% 0.37/1.02  --inst_dismatching                      true
% 0.37/1.02  --inst_eager_unprocessed_to_passive     true
% 0.37/1.02  --inst_prop_sim_given                   true
% 0.37/1.02  --inst_prop_sim_new                     false
% 0.37/1.02  --inst_subs_new                         false
% 0.37/1.02  --inst_eq_res_simp                      false
% 0.37/1.02  --inst_subs_given                       false
% 0.37/1.02  --inst_orphan_elimination               true
% 0.37/1.02  --inst_learning_loop_flag               true
% 0.37/1.02  --inst_learning_start                   3000
% 0.37/1.02  --inst_learning_factor                  2
% 0.37/1.02  --inst_start_prop_sim_after_learn       3
% 0.37/1.02  --inst_sel_renew                        solver
% 0.37/1.02  --inst_lit_activity_flag                true
% 0.37/1.02  --inst_restr_to_given                   false
% 0.37/1.02  --inst_activity_threshold               500
% 0.37/1.02  --inst_out_proof                        true
% 0.37/1.02  
% 0.37/1.02  ------ Resolution Options
% 0.37/1.02  
% 0.37/1.02  --resolution_flag                       true
% 0.37/1.02  --res_lit_sel                           adaptive
% 0.37/1.02  --res_lit_sel_side                      none
% 0.37/1.02  --res_ordering                          kbo
% 0.37/1.02  --res_to_prop_solver                    active
% 0.37/1.02  --res_prop_simpl_new                    false
% 0.37/1.02  --res_prop_simpl_given                  true
% 0.37/1.02  --res_passive_queue_type                priority_queues
% 0.37/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.02  --res_passive_queues_freq               [15;5]
% 0.37/1.02  --res_forward_subs                      full
% 0.37/1.02  --res_backward_subs                     full
% 0.37/1.02  --res_forward_subs_resolution           true
% 0.37/1.02  --res_backward_subs_resolution          true
% 0.37/1.02  --res_orphan_elimination                true
% 0.37/1.02  --res_time_limit                        2.
% 0.37/1.02  --res_out_proof                         true
% 0.37/1.02  
% 0.37/1.02  ------ Superposition Options
% 0.37/1.02  
% 0.37/1.02  --superposition_flag                    true
% 0.37/1.02  --sup_passive_queue_type                priority_queues
% 0.37/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.02  --demod_completeness_check              fast
% 0.37/1.02  --demod_use_ground                      true
% 0.37/1.02  --sup_to_prop_solver                    passive
% 0.37/1.02  --sup_prop_simpl_new                    true
% 0.37/1.02  --sup_prop_simpl_given                  true
% 0.37/1.02  --sup_fun_splitting                     false
% 0.37/1.02  --sup_smt_interval                      50000
% 0.37/1.02  
% 0.37/1.02  ------ Superposition Simplification Setup
% 0.37/1.02  
% 0.37/1.02  --sup_indices_passive                   []
% 0.37/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.02  --sup_full_bw                           [BwDemod]
% 0.37/1.02  --sup_immed_triv                        [TrivRules]
% 0.37/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.02  --sup_immed_bw_main                     []
% 0.37/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.02  
% 0.37/1.02  ------ Combination Options
% 0.37/1.02  
% 0.37/1.02  --comb_res_mult                         3
% 0.37/1.02  --comb_sup_mult                         2
% 0.37/1.02  --comb_inst_mult                        10
% 0.37/1.02  
% 0.37/1.02  ------ Debug Options
% 0.37/1.02  
% 0.37/1.02  --dbg_backtrace                         false
% 0.37/1.02  --dbg_dump_prop_clauses                 false
% 0.37/1.02  --dbg_dump_prop_clauses_file            -
% 0.37/1.02  --dbg_out_stat                          false
% 0.37/1.02  ------ Parsing...
% 0.37/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.37/1.02  
% 0.37/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.37/1.02  
% 0.37/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.37/1.02  
% 0.37/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.37/1.02  ------ Proving...
% 0.37/1.02  ------ Problem Properties 
% 0.37/1.02  
% 0.37/1.02  
% 0.37/1.02  clauses                                 21
% 0.37/1.02  conjectures                             5
% 0.37/1.02  EPR                                     2
% 0.37/1.02  Horn                                    19
% 0.37/1.02  unary                                   4
% 0.37/1.02  binary                                  5
% 0.37/1.02  lits                                    61
% 0.37/1.02  lits eq                                 10
% 0.37/1.02  fd_pure                                 0
% 0.37/1.02  fd_pseudo                               0
% 0.37/1.02  fd_cond                                 2
% 0.37/1.02  fd_pseudo_cond                          0
% 0.37/1.02  AC symbols                              0
% 0.37/1.02  
% 0.37/1.02  ------ Schedule dynamic 5 is on 
% 0.37/1.02  
% 0.37/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.37/1.02  
% 0.37/1.02  
% 0.37/1.02  ------ 
% 0.37/1.02  Current options:
% 0.37/1.02  ------ 
% 0.37/1.02  
% 0.37/1.02  ------ Input Options
% 0.37/1.02  
% 0.37/1.02  --out_options                           all
% 0.37/1.02  --tptp_safe_out                         true
% 0.37/1.02  --problem_path                          ""
% 0.37/1.02  --include_path                          ""
% 0.37/1.02  --clausifier                            res/vclausify_rel
% 0.37/1.02  --clausifier_options                    --mode clausify
% 0.37/1.02  --stdin                                 false
% 0.37/1.02  --stats_out                             all
% 0.37/1.02  
% 0.37/1.02  ------ General Options
% 0.37/1.02  
% 0.37/1.02  --fof                                   false
% 0.37/1.02  --time_out_real                         305.
% 0.37/1.02  --time_out_virtual                      -1.
% 0.37/1.02  --symbol_type_check                     false
% 0.37/1.02  --clausify_out                          false
% 0.37/1.02  --sig_cnt_out                           false
% 0.37/1.02  --trig_cnt_out                          false
% 0.37/1.02  --trig_cnt_out_tolerance                1.
% 0.37/1.02  --trig_cnt_out_sk_spl                   false
% 0.37/1.02  --abstr_cl_out                          false
% 0.37/1.02  
% 0.37/1.02  ------ Global Options
% 0.37/1.02  
% 0.37/1.02  --schedule                              default
% 0.37/1.02  --add_important_lit                     false
% 0.37/1.02  --prop_solver_per_cl                    1000
% 0.37/1.02  --min_unsat_core                        false
% 0.37/1.02  --soft_assumptions                      false
% 0.37/1.02  --soft_lemma_size                       3
% 0.37/1.02  --prop_impl_unit_size                   0
% 0.37/1.02  --prop_impl_unit                        []
% 0.37/1.02  --share_sel_clauses                     true
% 0.37/1.02  --reset_solvers                         false
% 0.37/1.02  --bc_imp_inh                            [conj_cone]
% 0.37/1.02  --conj_cone_tolerance                   3.
% 0.37/1.02  --extra_neg_conj                        none
% 0.37/1.02  --large_theory_mode                     true
% 0.37/1.02  --prolific_symb_bound                   200
% 0.37/1.02  --lt_threshold                          2000
% 0.37/1.02  --clause_weak_htbl                      true
% 0.37/1.02  --gc_record_bc_elim                     false
% 0.37/1.02  
% 0.37/1.02  ------ Preprocessing Options
% 0.37/1.02  
% 0.37/1.02  --preprocessing_flag                    true
% 0.37/1.02  --time_out_prep_mult                    0.1
% 0.37/1.02  --splitting_mode                        input
% 0.37/1.02  --splitting_grd                         true
% 0.37/1.02  --splitting_cvd                         false
% 0.37/1.02  --splitting_cvd_svl                     false
% 0.37/1.02  --splitting_nvd                         32
% 0.37/1.02  --sub_typing                            true
% 0.37/1.02  --prep_gs_sim                           true
% 0.37/1.02  --prep_unflatten                        true
% 0.37/1.02  --prep_res_sim                          true
% 0.37/1.02  --prep_upred                            true
% 0.37/1.02  --prep_sem_filter                       exhaustive
% 0.37/1.02  --prep_sem_filter_out                   false
% 0.37/1.02  --pred_elim                             true
% 0.37/1.02  --res_sim_input                         true
% 0.37/1.02  --eq_ax_congr_red                       true
% 0.37/1.02  --pure_diseq_elim                       true
% 0.37/1.02  --brand_transform                       false
% 0.37/1.02  --non_eq_to_eq                          false
% 0.37/1.02  --prep_def_merge                        true
% 0.37/1.02  --prep_def_merge_prop_impl              false
% 0.37/1.02  --prep_def_merge_mbd                    true
% 0.37/1.02  --prep_def_merge_tr_red                 false
% 0.37/1.02  --prep_def_merge_tr_cl                  false
% 0.37/1.02  --smt_preprocessing                     true
% 0.37/1.02  --smt_ac_axioms                         fast
% 0.37/1.02  --preprocessed_out                      false
% 0.37/1.02  --preprocessed_stats                    false
% 0.37/1.02  
% 0.37/1.02  ------ Abstraction refinement Options
% 0.37/1.02  
% 0.37/1.02  --abstr_ref                             []
% 0.37/1.02  --abstr_ref_prep                        false
% 0.37/1.02  --abstr_ref_until_sat                   false
% 0.37/1.02  --abstr_ref_sig_restrict                funpre
% 0.37/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.02  --abstr_ref_under                       []
% 0.37/1.02  
% 0.37/1.02  ------ SAT Options
% 0.37/1.02  
% 0.37/1.02  --sat_mode                              false
% 0.37/1.02  --sat_fm_restart_options                ""
% 0.37/1.02  --sat_gr_def                            false
% 0.37/1.02  --sat_epr_types                         true
% 0.37/1.02  --sat_non_cyclic_types                  false
% 0.37/1.02  --sat_finite_models                     false
% 0.37/1.02  --sat_fm_lemmas                         false
% 0.37/1.02  --sat_fm_prep                           false
% 0.37/1.02  --sat_fm_uc_incr                        true
% 0.37/1.02  --sat_out_model                         small
% 0.37/1.02  --sat_out_clauses                       false
% 0.37/1.02  
% 0.37/1.02  ------ QBF Options
% 0.37/1.02  
% 0.37/1.02  --qbf_mode                              false
% 0.37/1.02  --qbf_elim_univ                         false
% 0.37/1.02  --qbf_dom_inst                          none
% 0.37/1.02  --qbf_dom_pre_inst                      false
% 0.37/1.02  --qbf_sk_in                             false
% 0.37/1.02  --qbf_pred_elim                         true
% 0.37/1.02  --qbf_split                             512
% 0.37/1.02  
% 0.37/1.02  ------ BMC1 Options
% 0.37/1.02  
% 0.37/1.02  --bmc1_incremental                      false
% 0.37/1.02  --bmc1_axioms                           reachable_all
% 0.37/1.02  --bmc1_min_bound                        0
% 0.37/1.02  --bmc1_max_bound                        -1
% 0.37/1.02  --bmc1_max_bound_default                -1
% 0.37/1.02  --bmc1_symbol_reachability              true
% 0.37/1.02  --bmc1_property_lemmas                  false
% 0.37/1.02  --bmc1_k_induction                      false
% 0.37/1.02  --bmc1_non_equiv_states                 false
% 0.37/1.02  --bmc1_deadlock                         false
% 0.37/1.02  --bmc1_ucm                              false
% 0.37/1.02  --bmc1_add_unsat_core                   none
% 0.37/1.02  --bmc1_unsat_core_children              false
% 0.37/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.02  --bmc1_out_stat                         full
% 0.37/1.02  --bmc1_ground_init                      false
% 0.37/1.02  --bmc1_pre_inst_next_state              false
% 0.37/1.02  --bmc1_pre_inst_state                   false
% 0.37/1.02  --bmc1_pre_inst_reach_state             false
% 0.37/1.02  --bmc1_out_unsat_core                   false
% 0.37/1.02  --bmc1_aig_witness_out                  false
% 0.37/1.02  --bmc1_verbose                          false
% 0.37/1.02  --bmc1_dump_clauses_tptp                false
% 0.37/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.02  --bmc1_dump_file                        -
% 0.37/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.02  --bmc1_ucm_extend_mode                  1
% 0.37/1.02  --bmc1_ucm_init_mode                    2
% 0.37/1.02  --bmc1_ucm_cone_mode                    none
% 0.37/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.02  --bmc1_ucm_relax_model                  4
% 0.37/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.02  --bmc1_ucm_layered_model                none
% 0.37/1.02  --bmc1_ucm_max_lemma_size               10
% 0.37/1.02  
% 0.37/1.02  ------ AIG Options
% 0.37/1.02  
% 0.37/1.02  --aig_mode                              false
% 0.37/1.02  
% 0.37/1.02  ------ Instantiation Options
% 0.37/1.02  
% 0.37/1.02  --instantiation_flag                    true
% 0.37/1.02  --inst_sos_flag                         false
% 0.37/1.02  --inst_sos_phase                        true
% 0.37/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.02  --inst_lit_sel_side                     none
% 0.37/1.02  --inst_solver_per_active                1400
% 0.37/1.02  --inst_solver_calls_frac                1.
% 0.37/1.02  --inst_passive_queue_type               priority_queues
% 0.37/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.02  --inst_passive_queues_freq              [25;2]
% 0.37/1.02  --inst_dismatching                      true
% 0.37/1.02  --inst_eager_unprocessed_to_passive     true
% 0.37/1.02  --inst_prop_sim_given                   true
% 0.37/1.02  --inst_prop_sim_new                     false
% 0.37/1.02  --inst_subs_new                         false
% 0.37/1.02  --inst_eq_res_simp                      false
% 0.37/1.02  --inst_subs_given                       false
% 0.37/1.02  --inst_orphan_elimination               true
% 0.37/1.02  --inst_learning_loop_flag               true
% 0.37/1.02  --inst_learning_start                   3000
% 0.37/1.02  --inst_learning_factor                  2
% 0.37/1.02  --inst_start_prop_sim_after_learn       3
% 0.37/1.02  --inst_sel_renew                        solver
% 0.37/1.02  --inst_lit_activity_flag                true
% 0.37/1.02  --inst_restr_to_given                   false
% 0.37/1.02  --inst_activity_threshold               500
% 0.37/1.02  --inst_out_proof                        true
% 0.37/1.02  
% 0.37/1.02  ------ Resolution Options
% 0.37/1.02  
% 0.37/1.02  --resolution_flag                       false
% 0.37/1.02  --res_lit_sel                           adaptive
% 0.37/1.02  --res_lit_sel_side                      none
% 0.37/1.03  --res_ordering                          kbo
% 0.37/1.03  --res_to_prop_solver                    active
% 0.37/1.03  --res_prop_simpl_new                    false
% 0.37/1.03  --res_prop_simpl_given                  true
% 0.37/1.03  --res_passive_queue_type                priority_queues
% 0.37/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.03  --res_passive_queues_freq               [15;5]
% 0.37/1.03  --res_forward_subs                      full
% 0.37/1.03  --res_backward_subs                     full
% 0.37/1.03  --res_forward_subs_resolution           true
% 0.37/1.03  --res_backward_subs_resolution          true
% 0.37/1.03  --res_orphan_elimination                true
% 0.37/1.03  --res_time_limit                        2.
% 0.37/1.03  --res_out_proof                         true
% 0.37/1.03  
% 0.37/1.03  ------ Superposition Options
% 0.37/1.03  
% 0.37/1.03  --superposition_flag                    true
% 0.37/1.03  --sup_passive_queue_type                priority_queues
% 0.37/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.03  --demod_completeness_check              fast
% 0.37/1.03  --demod_use_ground                      true
% 0.37/1.03  --sup_to_prop_solver                    passive
% 0.37/1.03  --sup_prop_simpl_new                    true
% 0.37/1.03  --sup_prop_simpl_given                  true
% 0.37/1.03  --sup_fun_splitting                     false
% 0.37/1.03  --sup_smt_interval                      50000
% 0.37/1.03  
% 0.37/1.03  ------ Superposition Simplification Setup
% 0.37/1.03  
% 0.37/1.03  --sup_indices_passive                   []
% 0.37/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.03  --sup_full_bw                           [BwDemod]
% 0.37/1.03  --sup_immed_triv                        [TrivRules]
% 0.37/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.03  --sup_immed_bw_main                     []
% 0.37/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.03  
% 0.37/1.03  ------ Combination Options
% 0.37/1.03  
% 0.37/1.03  --comb_res_mult                         3
% 0.37/1.03  --comb_sup_mult                         2
% 0.37/1.03  --comb_inst_mult                        10
% 0.37/1.03  
% 0.37/1.03  ------ Debug Options
% 0.37/1.03  
% 0.37/1.03  --dbg_backtrace                         false
% 0.37/1.03  --dbg_dump_prop_clauses                 false
% 0.37/1.03  --dbg_dump_prop_clauses_file            -
% 0.37/1.03  --dbg_out_stat                          false
% 0.37/1.03  
% 0.37/1.03  
% 0.37/1.03  
% 0.37/1.03  
% 0.37/1.03  ------ Proving...
% 0.37/1.03  
% 0.37/1.03  
% 0.37/1.03  % SZS status Theorem for theBenchmark.p
% 0.37/1.03  
% 0.37/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.37/1.03  
% 0.37/1.03  fof(f5,axiom,(
% 0.37/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f20,plain,(
% 0.37/1.03    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/1.03    inference(ennf_transformation,[],[f5])).
% 0.37/1.03  
% 0.37/1.03  fof(f21,plain,(
% 0.37/1.03    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.03    inference(flattening,[],[f20])).
% 0.37/1.03  
% 0.37/1.03  fof(f46,plain,(
% 0.37/1.03    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f21])).
% 0.37/1.03  
% 0.37/1.03  fof(f13,conjecture,(
% 0.37/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f14,negated_conjecture,(
% 0.37/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.37/1.03    inference(negated_conjecture,[],[f13])).
% 0.37/1.03  
% 0.37/1.03  fof(f32,plain,(
% 0.37/1.03    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.37/1.03    inference(ennf_transformation,[],[f14])).
% 0.37/1.03  
% 0.37/1.03  fof(f33,plain,(
% 0.37/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.37/1.03    inference(flattening,[],[f32])).
% 0.37/1.03  
% 0.37/1.03  fof(f36,plain,(
% 0.37/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.37/1.03    introduced(choice_axiom,[])).
% 0.37/1.03  
% 0.37/1.03  fof(f37,plain,(
% 0.37/1.03    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.37/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).
% 0.37/1.03  
% 0.37/1.03  fof(f65,plain,(
% 0.37/1.03    v2_funct_1(sK2)),
% 0.37/1.03    inference(cnf_transformation,[],[f37])).
% 0.37/1.03  
% 0.37/1.03  fof(f62,plain,(
% 0.37/1.03    v1_funct_1(sK2)),
% 0.37/1.03    inference(cnf_transformation,[],[f37])).
% 0.37/1.03  
% 0.37/1.03  fof(f64,plain,(
% 0.37/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.37/1.03    inference(cnf_transformation,[],[f37])).
% 0.37/1.03  
% 0.37/1.03  fof(f6,axiom,(
% 0.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f22,plain,(
% 0.37/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.03    inference(ennf_transformation,[],[f6])).
% 0.37/1.03  
% 0.37/1.03  fof(f47,plain,(
% 0.37/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.03    inference(cnf_transformation,[],[f22])).
% 0.37/1.03  
% 0.37/1.03  fof(f11,axiom,(
% 0.37/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f28,plain,(
% 0.37/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/1.03    inference(ennf_transformation,[],[f11])).
% 0.37/1.03  
% 0.37/1.03  fof(f29,plain,(
% 0.37/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.03    inference(flattening,[],[f28])).
% 0.37/1.03  
% 0.37/1.03  fof(f55,plain,(
% 0.37/1.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f29])).
% 0.37/1.03  
% 0.37/1.03  fof(f8,axiom,(
% 0.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f24,plain,(
% 0.37/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.03    inference(ennf_transformation,[],[f8])).
% 0.37/1.03  
% 0.37/1.03  fof(f49,plain,(
% 0.37/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.03    inference(cnf_transformation,[],[f24])).
% 0.37/1.03  
% 0.37/1.03  fof(f66,plain,(
% 0.37/1.03    k2_relset_1(sK0,sK1,sK2) = sK1),
% 0.37/1.03    inference(cnf_transformation,[],[f37])).
% 0.37/1.03  
% 0.37/1.03  fof(f45,plain,(
% 0.37/1.03    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f21])).
% 0.37/1.03  
% 0.37/1.03  fof(f4,axiom,(
% 0.37/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f18,plain,(
% 0.37/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/1.03    inference(ennf_transformation,[],[f4])).
% 0.37/1.03  
% 0.37/1.03  fof(f19,plain,(
% 0.37/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.03    inference(flattening,[],[f18])).
% 0.37/1.03  
% 0.37/1.03  fof(f44,plain,(
% 0.37/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f19])).
% 0.37/1.03  
% 0.37/1.03  fof(f43,plain,(
% 0.37/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f19])).
% 0.37/1.03  
% 0.37/1.03  fof(f12,axiom,(
% 0.37/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f30,plain,(
% 0.37/1.03    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.37/1.03    inference(ennf_transformation,[],[f12])).
% 0.37/1.03  
% 0.37/1.03  fof(f31,plain,(
% 0.37/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.37/1.03    inference(flattening,[],[f30])).
% 0.37/1.03  
% 0.37/1.03  fof(f58,plain,(
% 0.37/1.03    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f31])).
% 0.37/1.03  
% 0.37/1.03  fof(f54,plain,(
% 0.37/1.03    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f29])).
% 0.37/1.03  
% 0.37/1.03  fof(f60,plain,(
% 0.37/1.03    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f31])).
% 0.37/1.03  
% 0.37/1.03  fof(f67,plain,(
% 0.37/1.03    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.37/1.03    inference(cnf_transformation,[],[f37])).
% 0.37/1.03  
% 0.37/1.03  fof(f7,axiom,(
% 0.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f15,plain,(
% 0.37/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.37/1.03    inference(pure_predicate_removal,[],[f7])).
% 0.37/1.03  
% 0.37/1.03  fof(f23,plain,(
% 0.37/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.03    inference(ennf_transformation,[],[f15])).
% 0.37/1.03  
% 0.37/1.03  fof(f48,plain,(
% 0.37/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.03    inference(cnf_transformation,[],[f23])).
% 0.37/1.03  
% 0.37/1.03  fof(f2,axiom,(
% 0.37/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f16,plain,(
% 0.37/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.37/1.03    inference(ennf_transformation,[],[f2])).
% 0.37/1.03  
% 0.37/1.03  fof(f34,plain,(
% 0.37/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.37/1.03    inference(nnf_transformation,[],[f16])).
% 0.37/1.03  
% 0.37/1.03  fof(f39,plain,(
% 0.37/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f34])).
% 0.37/1.03  
% 0.37/1.03  fof(f3,axiom,(
% 0.37/1.03    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.37/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.03  
% 0.37/1.03  fof(f17,plain,(
% 0.37/1.03    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.37/1.03    inference(ennf_transformation,[],[f3])).
% 0.37/1.03  
% 0.37/1.03  fof(f35,plain,(
% 0.37/1.03    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.37/1.03    inference(nnf_transformation,[],[f17])).
% 0.37/1.03  
% 0.37/1.03  fof(f42,plain,(
% 0.37/1.03    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f35])).
% 0.37/1.03  
% 0.37/1.03  fof(f59,plain,(
% 0.37/1.03    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f31])).
% 0.37/1.03  
% 0.37/1.03  fof(f69,plain,(
% 0.37/1.03    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 0.37/1.03    inference(equality_resolution,[],[f59])).
% 0.37/1.03  
% 0.37/1.03  fof(f61,plain,(
% 0.37/1.03    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.37/1.03    inference(cnf_transformation,[],[f31])).
% 0.37/1.03  
% 0.37/1.03  fof(f68,plain,(
% 0.37/1.03    ( ! [X2,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 0.37/1.03    inference(equality_resolution,[],[f61])).
% 0.37/1.03  
% 0.37/1.03  cnf(c_7,plain,
% 0.37/1.03      ( ~ v2_funct_1(X0)
% 0.37/1.03      | ~ v1_funct_1(X0)
% 0.37/1.03      | ~ v1_relat_1(X0)
% 0.37/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_26,negated_conjecture,
% 0.37/1.03      ( v2_funct_1(sK2) ),
% 0.37/1.03      inference(cnf_transformation,[],[f65]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_343,plain,
% 0.37/1.03      ( ~ v1_funct_1(X0)
% 0.37/1.03      | ~ v1_relat_1(X0)
% 0.37/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 0.37/1.03      | sK2 != X0 ),
% 0.37/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_344,plain,
% 0.37/1.03      ( ~ v1_funct_1(sK2)
% 0.37/1.03      | ~ v1_relat_1(sK2)
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 0.37/1.03      inference(unflattening,[status(thm)],[c_343]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_29,negated_conjecture,
% 0.37/1.03      ( v1_funct_1(sK2) ),
% 0.37/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_346,plain,
% 0.37/1.03      ( ~ v1_relat_1(sK2)
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_344,c_29]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_732,plain,
% 0.37/1.03      ( ~ v1_relat_1(sK2)
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_346]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1140,plain,
% 0.37/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 0.37/1.03      | v1_relat_1(sK2) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_27,negated_conjecture,
% 0.37/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.37/1.03      inference(cnf_transformation,[],[f64]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_9,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.03      | v1_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_747,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 0.37/1.03      | v1_relat_1(X0_47) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1310,plain,
% 0.37/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.37/1.03      | v1_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_747]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1389,plain,
% 0.37/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_1140,c_27,c_732,c_1310]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_15,plain,
% 0.37/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 0.37/1.03      | ~ v1_funct_1(X0)
% 0.37/1.03      | ~ v1_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_745,plain,
% 0.37/1.03      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),k2_relat_1(X0_47))))
% 0.37/1.03      | ~ v1_funct_1(X0_47)
% 0.37/1.03      | ~ v1_relat_1(X0_47) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1128,plain,
% 0.37/1.03      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_47),k2_relat_1(X0_47)))) = iProver_top
% 0.37/1.03      | v1_funct_1(X0_47) != iProver_top
% 0.37/1.03      | v1_relat_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1772,plain,
% 0.37/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_1389,c_1128]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_737,negated_conjecture,
% 0.37/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_27]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1135,plain,
% 0.37/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_11,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_746,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 0.37/1.03      | k2_relset_1(X0_50,X1_50,X0_47) = k2_relat_1(X0_47) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1127,plain,
% 0.37/1.03      ( k2_relset_1(X0_50,X1_50,X0_47) = k2_relat_1(X0_47)
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1569,plain,
% 0.37/1.03      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_1135,c_1127]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_25,negated_conjecture,
% 0.37/1.03      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 0.37/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_738,negated_conjecture,
% 0.37/1.03      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1570,plain,
% 0.37/1.03      ( k2_relat_1(sK2) = sK1 ),
% 0.37/1.03      inference(light_normalisation,[status(thm)],[c_1569,c_738]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_8,plain,
% 0.37/1.03      ( ~ v2_funct_1(X0)
% 0.37/1.03      | ~ v1_funct_1(X0)
% 0.37/1.03      | ~ v1_relat_1(X0)
% 0.37/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_329,plain,
% 0.37/1.03      ( ~ v1_funct_1(X0)
% 0.37/1.03      | ~ v1_relat_1(X0)
% 0.37/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 0.37/1.03      | sK2 != X0 ),
% 0.37/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_330,plain,
% 0.37/1.03      ( ~ v1_funct_1(sK2)
% 0.37/1.03      | ~ v1_relat_1(sK2)
% 0.37/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.37/1.03      inference(unflattening,[status(thm)],[c_329]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_332,plain,
% 0.37/1.03      ( ~ v1_relat_1(sK2)
% 0.37/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_330,c_29]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_733,plain,
% 0.37/1.03      ( ~ v1_relat_1(sK2)
% 0.37/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_332]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1139,plain,
% 0.37/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 0.37/1.03      | v1_relat_1(sK2) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1341,plain,
% 0.37/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_1139,c_27,c_733,c_1310]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1572,plain,
% 0.37/1.03      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 0.37/1.03      inference(demodulation,[status(thm)],[c_1570,c_1341]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1791,plain,
% 0.37/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(light_normalisation,[status(thm)],[c_1772,c_1572]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_30,plain,
% 0.37/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_32,plain,
% 0.37/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5,plain,
% 0.37/1.03      ( ~ v1_funct_1(X0)
% 0.37/1.03      | v1_funct_1(k2_funct_1(X0))
% 0.37/1.03      | ~ v1_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_749,plain,
% 0.37/1.03      ( ~ v1_funct_1(X0_47)
% 0.37/1.03      | v1_funct_1(k2_funct_1(X0_47))
% 0.37/1.03      | ~ v1_relat_1(X0_47) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_779,plain,
% 0.37/1.03      ( v1_funct_1(X0_47) != iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(X0_47)) = iProver_top
% 0.37/1.03      | v1_relat_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_781,plain,
% 0.37/1.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 0.37/1.03      | v1_funct_1(sK2) != iProver_top
% 0.37/1.03      | v1_relat_1(sK2) != iProver_top ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_779]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_6,plain,
% 0.37/1.03      ( ~ v1_funct_1(X0)
% 0.37/1.03      | ~ v1_relat_1(X0)
% 0.37/1.03      | v1_relat_1(k2_funct_1(X0)) ),
% 0.37/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_748,plain,
% 0.37/1.03      ( ~ v1_funct_1(X0_47)
% 0.37/1.03      | ~ v1_relat_1(X0_47)
% 0.37/1.03      | v1_relat_1(k2_funct_1(X0_47)) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_782,plain,
% 0.37/1.03      ( v1_funct_1(X0_47) != iProver_top
% 0.37/1.03      | v1_relat_1(X0_47) != iProver_top
% 0.37/1.03      | v1_relat_1(k2_funct_1(X0_47)) = iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_784,plain,
% 0.37/1.03      ( v1_funct_1(sK2) != iProver_top
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 0.37/1.03      | v1_relat_1(sK2) != iProver_top ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_782]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1311,plain,
% 0.37/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 0.37/1.03      | v1_relat_1(sK2) = iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2278,plain,
% 0.37/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_1791,c_30,c_32,c_781,c_784,c_1311]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_21,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.03      | v1_funct_2(X0,X1,X3)
% 0.37/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.03      | ~ r1_tarski(X2,X3)
% 0.37/1.03      | ~ v1_funct_1(X0)
% 0.37/1.03      | k1_xboole_0 = X2 ),
% 0.37/1.03      inference(cnf_transformation,[],[f58]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_740,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0_47,X0_50,X1_50)
% 0.37/1.03      | v1_funct_2(X0_47,X0_50,X2_50)
% 0.37/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 0.37/1.03      | ~ r1_tarski(X1_50,X2_50)
% 0.37/1.03      | ~ v1_funct_1(X0_47)
% 0.37/1.03      | k1_xboole_0 = X1_50 ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_21]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1133,plain,
% 0.37/1.03      ( k1_xboole_0 = X0_50
% 0.37/1.03      | v1_funct_2(X0_47,X1_50,X0_50) != iProver_top
% 0.37/1.03      | v1_funct_2(X0_47,X1_50,X2_50) = iProver_top
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 0.37/1.03      | r1_tarski(X0_50,X2_50) != iProver_top
% 0.37/1.03      | v1_funct_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2286,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,X0_50) = iProver_top
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_2278,c_1133]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_16,plain,
% 0.37/1.03      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 0.37/1.03      | ~ v1_funct_1(X0)
% 0.37/1.03      | ~ v1_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f54]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_744,plain,
% 0.37/1.03      ( v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47))
% 0.37/1.03      | ~ v1_funct_1(X0_47)
% 0.37/1.03      | ~ v1_relat_1(X0_47) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1129,plain,
% 0.37/1.03      ( v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47)) = iProver_top
% 0.37/1.03      | v1_funct_1(X0_47) != iProver_top
% 0.37/1.03      | v1_relat_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1870,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_1389,c_1129]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1874,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) = iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(light_normalisation,[status(thm)],[c_1870,c_1572]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3419,plain,
% 0.37/1.03      ( r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
% 0.37/1.03      | k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,X0_50) = iProver_top ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_2286,c_30,c_32,c_781,c_784,c_1311,c_1874]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3420,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,X0_50) = iProver_top
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_3419]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_19,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 0.37/1.03      | ~ r1_tarski(X2,X3)
% 0.37/1.03      | ~ v1_funct_1(X0)
% 0.37/1.03      | k1_xboole_0 = X2 ),
% 0.37/1.03      inference(cnf_transformation,[],[f60]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_742,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0_47,X0_50,X1_50)
% 0.37/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X2_50)))
% 0.37/1.03      | ~ r1_tarski(X1_50,X2_50)
% 0.37/1.03      | ~ v1_funct_1(X0_47)
% 0.37/1.03      | k1_xboole_0 = X1_50 ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_19]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1131,plain,
% 0.37/1.03      ( k1_xboole_0 = X0_50
% 0.37/1.03      | v1_funct_2(X0_47,X1_50,X0_50) != iProver_top
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) = iProver_top
% 0.37/1.03      | r1_tarski(X0_50,X2_50) != iProver_top
% 0.37/1.03      | v1_funct_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2374,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) = iProver_top
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_2278,c_1131]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3429,plain,
% 0.37/1.03      ( r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) = iProver_top
% 0.37/1.03      | k1_relat_1(sK2) = k1_xboole_0 ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_2374,c_30,c_32,c_781,c_784,c_1311,c_1874]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3430,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) = iProver_top
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_3429]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_24,negated_conjecture,
% 0.37/1.03      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 0.37/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.37/1.03      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 0.37/1.03      inference(cnf_transformation,[],[f67]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_739,negated_conjecture,
% 0.37/1.03      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 0.37/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.37/1.03      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_24]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1134,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_34,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1334,plain,
% 0.37/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_1134,c_30,c_32,c_34,c_781,c_1311]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1335,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_1334]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3438,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_3430,c_1335]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_10,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.03      | v4_relat_1(X0,X1) ),
% 0.37/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2,plain,
% 0.37/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 0.37/1.03      | ~ v4_relat_1(X0,X1)
% 0.37/1.03      | ~ v1_relat_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_363,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 0.37/1.03      | ~ v1_relat_1(X0) ),
% 0.37/1.03      inference(resolution,[status(thm)],[c_10,c_2]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_367,plain,
% 0.37/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 0.37/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_363,c_9]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_368,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.03      | r1_tarski(k1_relat_1(X0),X1) ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_367]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_731,plain,
% 0.37/1.03      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 0.37/1.03      | r1_tarski(k1_relat_1(X0_47),X0_50) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_368]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1313,plain,
% 0.37/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),sK0) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_731]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1314,plain,
% 0.37/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3577,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 0.37/1.03      | k1_relat_1(sK2) = k1_xboole_0 ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_3438,c_32,c_1314]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3578,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_3577]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3583,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_3420,c_3578]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3586,plain,
% 0.37/1.03      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_3583,c_32,c_1314]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3593,plain,
% 0.37/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 0.37/1.03      inference(demodulation,[status(thm)],[c_3586,c_2278]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3,plain,
% 0.37/1.03      ( ~ v1_relat_1(X0)
% 0.37/1.03      | k2_relat_1(X0) != k1_xboole_0
% 0.37/1.03      | k1_relat_1(X0) = k1_xboole_0 ),
% 0.37/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_751,plain,
% 0.37/1.03      ( ~ v1_relat_1(X0_47)
% 0.37/1.03      | k2_relat_1(X0_47) != k1_xboole_0
% 0.37/1.03      | k1_relat_1(X0_47) = k1_xboole_0 ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1122,plain,
% 0.37/1.03      ( k2_relat_1(X0_47) != k1_xboole_0
% 0.37/1.03      | k1_relat_1(X0_47) = k1_xboole_0
% 0.37/1.03      | v1_relat_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1464,plain,
% 0.37/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 0.37/1.03      | k1_relat_1(sK2) != k1_xboole_0
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_1389,c_1122]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1465,plain,
% 0.37/1.03      ( k2_relat_1(sK2) = k1_xboole_0
% 0.37/1.03      | k1_relat_1(sK2) != k1_xboole_0
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(demodulation,[status(thm)],[c_1464,c_1341]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1715,plain,
% 0.37/1.03      ( k1_relat_1(sK2) != k1_xboole_0 | k2_relat_1(sK2) = k1_xboole_0 ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_1465,c_30,c_32,c_784,c_1311]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1716,plain,
% 0.37/1.03      ( k2_relat_1(sK2) = k1_xboole_0 | k1_relat_1(sK2) != k1_xboole_0 ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_1715]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1717,plain,
% 0.37/1.03      ( k1_relat_1(sK2) != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 0.37/1.03      inference(demodulation,[status(thm)],[c_1716,c_1570]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3600,plain,
% 0.37/1.03      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 0.37/1.03      inference(demodulation,[status(thm)],[c_3586,c_1717]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3604,plain,
% 0.37/1.03      ( sK1 = k1_xboole_0 ),
% 0.37/1.03      inference(equality_resolution_simp,[status(thm)],[c_3600]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_3623,plain,
% 0.37/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 0.37/1.03      inference(light_normalisation,[status(thm)],[c_3593,c_3604]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_20,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.37/1.03      | v1_funct_2(X0,k1_xboole_0,X2)
% 0.37/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.37/1.03      | ~ r1_tarski(X1,X2)
% 0.37/1.03      | ~ v1_funct_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f69]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_741,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0_47,k1_xboole_0,X0_50)
% 0.37/1.03      | v1_funct_2(X0_47,k1_xboole_0,X1_50)
% 0.37/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50)))
% 0.37/1.03      | ~ r1_tarski(X0_50,X1_50)
% 0.37/1.03      | ~ v1_funct_1(X0_47) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1132,plain,
% 0.37/1.03      ( v1_funct_2(X0_47,k1_xboole_0,X0_50) != iProver_top
% 0.37/1.03      | v1_funct_2(X0_47,k1_xboole_0,X1_50) = iProver_top
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) != iProver_top
% 0.37/1.03      | r1_tarski(X0_50,X1_50) != iProver_top
% 0.37/1.03      | v1_funct_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5560,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0_50) = iProver_top
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
% 0.37/1.03      | r1_tarski(k1_xboole_0,X0_50) != iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_3623,c_1132]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_755,plain,( X0_50 = X0_50 ),theory(equality) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_772,plain,
% 0.37/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_755]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_756,plain,
% 0.37/1.03      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 0.37/1.03      theory(equality) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1537,plain,
% 0.37/1.03      ( X0_50 != X1_50
% 0.37/1.03      | X0_50 = k1_relat_1(sK2)
% 0.37/1.03      | k1_relat_1(sK2) != X1_50 ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_756]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1538,plain,
% 0.37/1.03      ( k1_relat_1(sK2) != k1_xboole_0
% 0.37/1.03      | k1_xboole_0 = k1_relat_1(sK2)
% 0.37/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1537]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1607,plain,
% 0.37/1.03      ( k2_relat_1(X0_47) = k2_relat_1(X0_47) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_755]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1609,plain,
% 0.37/1.03      ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1607]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1652,plain,
% 0.37/1.03      ( X0_50 != X1_50
% 0.37/1.03      | X0_50 = k2_relat_1(X0_47)
% 0.37/1.03      | k2_relat_1(X0_47) != X1_50 ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_756]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1653,plain,
% 0.37/1.03      ( k2_relat_1(sK2) != k1_xboole_0
% 0.37/1.03      | k1_xboole_0 = k2_relat_1(sK2)
% 0.37/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1652]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1927,plain,
% 0.37/1.03      ( X0_50 = k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | X0_50 != k1_relat_1(sK2)
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1652]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1928,plain,
% 0.37/1.03      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 0.37/1.03      | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | k1_xboole_0 != k1_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1927]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1610,plain,
% 0.37/1.03      ( X0_50 != X1_50
% 0.37/1.03      | k2_relat_1(X0_47) != X1_50
% 0.37/1.03      | k2_relat_1(X0_47) = X0_50 ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_756]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1896,plain,
% 0.37/1.03      ( X0_50 != k1_relat_1(sK2)
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) = X0_50
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1610]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2064,plain,
% 0.37/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1896]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2183,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
% 0.37/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.37/1.03      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_744]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2186,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 0.37/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_2183]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1900,plain,
% 0.37/1.03      ( X0_50 != k2_relat_1(X0_47)
% 0.37/1.03      | k2_relat_1(X0_47) = X0_50
% 0.37/1.03      | k2_relat_1(X0_47) != k2_relat_1(X0_47) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1610]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2216,plain,
% 0.37/1.03      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 0.37/1.03      | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1900]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_762,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0_47,X0_50,X1_50)
% 0.37/1.03      | v1_funct_2(X0_47,X2_50,X3_50)
% 0.37/1.03      | X2_50 != X0_50
% 0.37/1.03      | X3_50 != X1_50 ),
% 0.37/1.03      theory(equality) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1399,plain,
% 0.37/1.03      ( v1_funct_2(X0_47,X0_50,X1_50)
% 0.37/1.03      | ~ v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47))
% 0.37/1.03      | X1_50 != k2_relat_1(X0_47)
% 0.37/1.03      | X0_50 != k1_relat_1(X0_47) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_762]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1847,plain,
% 0.37/1.03      ( v1_funct_2(X0_47,X0_50,k2_relat_1(X0_47))
% 0.37/1.03      | ~ v1_funct_2(X0_47,k1_relat_1(X0_47),k2_relat_1(X0_47))
% 0.37/1.03      | X0_50 != k1_relat_1(X0_47)
% 0.37/1.03      | k2_relat_1(X0_47) != k2_relat_1(X0_47) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1399]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2328,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
% 0.37/1.03      | ~ v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
% 0.37/1.03      | k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1847]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2336,plain,
% 0.37/1.03      ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_2328]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2835,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),X0_50,X1_50)
% 0.37/1.03      | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
% 0.37/1.03      | X1_50 != k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | X0_50 != k2_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_762]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2836,plain,
% 0.37/1.03      ( X0_50 != k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | X1_50 != k2_relat_1(sK2)
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),X1_50,X0_50) = iProver_top
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_2835]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_2838,plain,
% 0.37/1.03      ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
% 0.37/1.03      | k1_xboole_0 != k2_relat_1(sK2)
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) != iProver_top
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_2836]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5641,plain,
% 0.37/1.03      ( r1_tarski(k1_xboole_0,X0_50) != iProver_top
% 0.37/1.03      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0_50) = iProver_top ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_5560,c_30,c_27,c_32,c_772,c_781,c_784,c_733,c_732,
% 0.37/1.03                 c_1310,c_1311,c_1314,c_1465,c_1538,c_1609,c_1653,c_1928,
% 0.37/1.03                 c_2064,c_2186,c_2216,c_2336,c_2838,c_3583]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5642,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0_50) = iProver_top
% 0.37/1.03      | r1_tarski(k1_xboole_0,X0_50) != iProver_top ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_5641]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_18,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.37/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.37/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 0.37/1.03      | ~ r1_tarski(X1,X2)
% 0.37/1.03      | ~ v1_funct_1(X0) ),
% 0.37/1.03      inference(cnf_transformation,[],[f68]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_743,plain,
% 0.37/1.03      ( ~ v1_funct_2(X0_47,k1_xboole_0,X0_50)
% 0.37/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50)))
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1_50)))
% 0.37/1.03      | ~ r1_tarski(X0_50,X1_50)
% 0.37/1.03      | ~ v1_funct_1(X0_47) ),
% 0.37/1.03      inference(subtyping,[status(esa)],[c_18]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1130,plain,
% 0.37/1.03      ( v1_funct_2(X0_47,k1_xboole_0,X0_50) != iProver_top
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) != iProver_top
% 0.37/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1_50))) = iProver_top
% 0.37/1.03      | r1_tarski(X0_50,X1_50) != iProver_top
% 0.37/1.03      | v1_funct_1(X0_47) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5559,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) = iProver_top
% 0.37/1.03      | r1_tarski(k1_xboole_0,X0_50) != iProver_top
% 0.37/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_3623,c_1130]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5648,plain,
% 0.37/1.03      ( r1_tarski(k1_xboole_0,X0_50) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) = iProver_top ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_5559,c_30,c_27,c_32,c_772,c_781,c_784,c_733,c_732,
% 0.37/1.03                 c_1310,c_1311,c_1314,c_1465,c_1538,c_1609,c_1653,c_1928,
% 0.37/1.03                 c_2064,c_2186,c_2216,c_2336,c_2838,c_3583]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5649,plain,
% 0.37/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))) = iProver_top
% 0.37/1.03      | r1_tarski(k1_xboole_0,X0_50) != iProver_top ),
% 0.37/1.03      inference(renaming,[status(thm)],[c_5648]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_4163,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top
% 0.37/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.37/1.03      inference(demodulation,[status(thm)],[c_3604,c_1335]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5662,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top
% 0.37/1.03      | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_5649,c_4163]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_757,plain,
% 0.37/1.03      ( ~ r1_tarski(X0_50,X1_50)
% 0.37/1.03      | r1_tarski(X2_50,X1_50)
% 0.37/1.03      | X2_50 != X0_50 ),
% 0.37/1.03      theory(equality) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1346,plain,
% 0.37/1.03      ( r1_tarski(X0_50,sK0)
% 0.37/1.03      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 0.37/1.03      | X0_50 != k1_relat_1(sK2) ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_757]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1347,plain,
% 0.37/1.03      ( X0_50 != k1_relat_1(sK2)
% 0.37/1.03      | r1_tarski(X0_50,sK0) = iProver_top
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 0.37/1.03      inference(predicate_to_equality,[status(thm)],[c_1346]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_1349,plain,
% 0.37/1.03      ( k1_xboole_0 != k1_relat_1(sK2)
% 0.37/1.03      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
% 0.37/1.03      | r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 0.37/1.03      inference(instantiation,[status(thm)],[c_1347]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5749,plain,
% 0.37/1.03      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top ),
% 0.37/1.03      inference(global_propositional_subsumption,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_5662,c_32,c_772,c_1314,c_1349,c_1538,c_3583]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(c_5754,plain,
% 0.37/1.03      ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 0.37/1.03      inference(superposition,[status(thm)],[c_5642,c_5749]) ).
% 0.37/1.03  
% 0.37/1.03  cnf(contradiction,plain,
% 0.37/1.03      ( $false ),
% 0.37/1.03      inference(minisat,
% 0.37/1.03                [status(thm)],
% 0.37/1.03                [c_5754,c_3583,c_1538,c_1349,c_1314,c_772,c_32]) ).
% 0.37/1.03  
% 0.37/1.03  
% 0.37/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.37/1.03  
% 0.37/1.03  ------                               Statistics
% 0.37/1.03  
% 0.37/1.03  ------ General
% 0.37/1.03  
% 0.37/1.03  abstr_ref_over_cycles:                  0
% 0.37/1.03  abstr_ref_under_cycles:                 0
% 0.37/1.03  gc_basic_clause_elim:                   0
% 0.37/1.03  forced_gc_time:                         0
% 0.37/1.03  parsing_time:                           0.015
% 0.37/1.03  unif_index_cands_time:                  0.
% 0.37/1.03  unif_index_add_time:                    0.
% 0.37/1.03  orderings_time:                         0.
% 0.37/1.03  out_proof_time:                         0.015
% 0.37/1.03  total_time:                             0.16
% 0.37/1.03  num_of_symbols:                         51
% 0.37/1.03  num_of_terms:                           3099
% 0.37/1.03  
% 0.37/1.03  ------ Preprocessing
% 0.37/1.03  
% 0.37/1.03  num_of_splits:                          0
% 0.37/1.03  num_of_split_atoms:                     0
% 0.37/1.03  num_of_reused_defs:                     0
% 0.37/1.03  num_eq_ax_congr_red:                    15
% 0.37/1.03  num_of_sem_filtered_clauses:            1
% 0.37/1.03  num_of_subtypes:                        4
% 0.37/1.03  monotx_restored_types:                  0
% 0.37/1.03  sat_num_of_epr_types:                   0
% 0.37/1.03  sat_num_of_non_cyclic_types:            0
% 0.37/1.03  sat_guarded_non_collapsed_types:        1
% 0.37/1.03  num_pure_diseq_elim:                    0
% 0.37/1.03  simp_replaced_by:                       0
% 0.37/1.03  res_preprocessed:                       110
% 0.37/1.03  prep_upred:                             0
% 0.37/1.03  prep_unflattend:                        21
% 0.37/1.03  smt_new_axioms:                         0
% 0.37/1.03  pred_elim_cands:                        5
% 0.37/1.03  pred_elim:                              4
% 0.37/1.03  pred_elim_cl:                           5
% 0.37/1.03  pred_elim_cycles:                       6
% 0.37/1.03  merged_defs:                            0
% 0.37/1.03  merged_defs_ncl:                        0
% 0.37/1.03  bin_hyper_res:                          0
% 0.37/1.03  prep_cycles:                            4
% 0.37/1.03  pred_elim_time:                         0.003
% 0.37/1.03  splitting_time:                         0.
% 0.37/1.03  sem_filter_time:                        0.
% 0.37/1.03  monotx_time:                            0.
% 0.37/1.03  subtype_inf_time:                       0.
% 0.37/1.03  
% 0.37/1.03  ------ Problem properties
% 0.37/1.03  
% 0.37/1.03  clauses:                                21
% 0.37/1.03  conjectures:                            5
% 0.37/1.03  epr:                                    2
% 0.37/1.03  horn:                                   19
% 0.37/1.03  ground:                                 7
% 0.37/1.03  unary:                                  4
% 0.37/1.03  binary:                                 5
% 0.37/1.03  lits:                                   61
% 0.37/1.03  lits_eq:                                10
% 0.37/1.03  fd_pure:                                0
% 0.37/1.03  fd_pseudo:                              0
% 0.37/1.03  fd_cond:                                2
% 0.37/1.03  fd_pseudo_cond:                         0
% 0.37/1.03  ac_symbols:                             0
% 0.37/1.03  
% 0.37/1.03  ------ Propositional Solver
% 0.37/1.03  
% 0.37/1.03  prop_solver_calls:                      30
% 0.37/1.03  prop_fast_solver_calls:                 1057
% 0.37/1.03  smt_solver_calls:                       0
% 0.37/1.03  smt_fast_solver_calls:                  0
% 0.37/1.03  prop_num_of_clauses:                    1780
% 0.37/1.03  prop_preprocess_simplified:             5433
% 0.37/1.03  prop_fo_subsumed:                       71
% 0.37/1.03  prop_solver_time:                       0.
% 0.37/1.03  smt_solver_time:                        0.
% 0.37/1.03  smt_fast_solver_time:                   0.
% 0.37/1.03  prop_fast_solver_time:                  0.
% 0.37/1.03  prop_unsat_core_time:                   0.
% 0.37/1.03  
% 0.37/1.03  ------ QBF
% 0.37/1.03  
% 0.37/1.03  qbf_q_res:                              0
% 0.37/1.03  qbf_num_tautologies:                    0
% 0.37/1.03  qbf_prep_cycles:                        0
% 0.37/1.03  
% 0.37/1.03  ------ BMC1
% 0.37/1.03  
% 0.37/1.03  bmc1_current_bound:                     -1
% 0.37/1.03  bmc1_last_solved_bound:                 -1
% 0.37/1.03  bmc1_unsat_core_size:                   -1
% 0.37/1.03  bmc1_unsat_core_parents_size:           -1
% 0.37/1.03  bmc1_merge_next_fun:                    0
% 0.37/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.37/1.03  
% 0.37/1.03  ------ Instantiation
% 0.37/1.03  
% 0.37/1.03  inst_num_of_clauses:                    621
% 0.37/1.03  inst_num_in_passive:                    269
% 0.37/1.03  inst_num_in_active:                     295
% 0.37/1.03  inst_num_in_unprocessed:                57
% 0.37/1.03  inst_num_of_loops:                      460
% 0.37/1.03  inst_num_of_learning_restarts:          0
% 0.37/1.03  inst_num_moves_active_passive:          158
% 0.37/1.03  inst_lit_activity:                      0
% 0.37/1.03  inst_lit_activity_moves:                0
% 0.37/1.03  inst_num_tautologies:                   0
% 0.37/1.03  inst_num_prop_implied:                  0
% 0.37/1.03  inst_num_existing_simplified:           0
% 0.37/1.03  inst_num_eq_res_simplified:             0
% 0.37/1.03  inst_num_child_elim:                    0
% 0.37/1.03  inst_num_of_dismatching_blockings:      218
% 0.37/1.03  inst_num_of_non_proper_insts:           621
% 0.37/1.03  inst_num_of_duplicates:                 0
% 0.37/1.03  inst_inst_num_from_inst_to_res:         0
% 0.37/1.03  inst_dismatching_checking_time:         0.
% 0.37/1.03  
% 0.37/1.03  ------ Resolution
% 0.37/1.03  
% 0.37/1.03  res_num_of_clauses:                     0
% 0.37/1.03  res_num_in_passive:                     0
% 0.37/1.03  res_num_in_active:                      0
% 0.37/1.03  res_num_of_loops:                       114
% 0.37/1.03  res_forward_subset_subsumed:            43
% 0.37/1.03  res_backward_subset_subsumed:           4
% 0.37/1.03  res_forward_subsumed:                   0
% 0.37/1.03  res_backward_subsumed:                  0
% 0.37/1.03  res_forward_subsumption_resolution:     0
% 0.37/1.03  res_backward_subsumption_resolution:    0
% 0.37/1.03  res_clause_to_clause_subsumption:       295
% 0.37/1.03  res_orphan_elimination:                 0
% 0.37/1.03  res_tautology_del:                      113
% 0.37/1.03  res_num_eq_res_simplified:              0
% 0.37/1.03  res_num_sel_changes:                    0
% 0.37/1.03  res_moves_from_active_to_pass:          0
% 0.37/1.03  
% 0.37/1.03  ------ Superposition
% 0.37/1.03  
% 0.37/1.03  sup_time_total:                         0.
% 0.37/1.03  sup_time_generating:                    0.
% 0.37/1.03  sup_time_sim_full:                      0.
% 0.37/1.03  sup_time_sim_immed:                     0.
% 0.37/1.03  
% 0.37/1.03  sup_num_of_clauses:                     69
% 0.37/1.03  sup_num_in_active:                      61
% 0.37/1.03  sup_num_in_passive:                     8
% 0.37/1.03  sup_num_of_loops:                       90
% 0.37/1.03  sup_fw_superposition:                   53
% 0.37/1.03  sup_bw_superposition:                   100
% 0.37/1.03  sup_immediate_simplified:               92
% 0.37/1.03  sup_given_eliminated:                   0
% 0.37/1.03  comparisons_done:                       0
% 0.37/1.03  comparisons_avoided:                    0
% 0.37/1.03  
% 0.37/1.03  ------ Simplifications
% 0.37/1.03  
% 0.37/1.03  
% 0.37/1.03  sim_fw_subset_subsumed:                 37
% 0.37/1.03  sim_bw_subset_subsumed:                 17
% 0.37/1.03  sim_fw_subsumed:                        6
% 0.37/1.03  sim_bw_subsumed:                        6
% 0.37/1.03  sim_fw_subsumption_res:                 0
% 0.37/1.03  sim_bw_subsumption_res:                 0
% 0.37/1.03  sim_tautology_del:                      2
% 0.37/1.03  sim_eq_tautology_del:                   11
% 0.37/1.03  sim_eq_res_simp:                        1
% 0.37/1.03  sim_fw_demodulated:                     9
% 0.37/1.03  sim_bw_demodulated:                     22
% 0.37/1.03  sim_light_normalised:                   43
% 0.37/1.03  sim_joinable_taut:                      0
% 0.37/1.03  sim_joinable_simp:                      0
% 0.37/1.03  sim_ac_normalised:                      0
% 0.37/1.03  sim_smt_subsumption:                    0
% 0.37/1.03  
%------------------------------------------------------------------------------
