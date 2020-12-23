%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:37 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  215 (3774 expanded)
%              Number of clauses        :  139 (1231 expanded)
%              Number of leaves         :   17 ( 718 expanded)
%              Depth                    :   27
%              Number of atoms          :  649 (18775 expanded)
%              Number of equality atoms :  321 (3629 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f46,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f21])).

fof(f65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f76])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f44,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f20])).

fof(f56,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f78])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f47])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2066,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2062,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2065,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2467,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_2065])).

cnf(c_2568,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2066,c_2467])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2051,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3903,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2568,c_2051])).

cnf(c_17,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_63,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_64,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6318,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3903,c_63,c_64])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2059,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3400,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2568,c_2059])).

cnf(c_81,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_108,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2470,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_4388,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3400,c_17,c_81,c_108,c_2470])).

cnf(c_6322,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6318,c_4388])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_funct_2(X0,k1_xboole_0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2047,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6329,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6322,c_2047])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_470,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_471,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_475,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_17])).

cnf(c_2038,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_4391,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4388,c_2038])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2050,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4396,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4388,c_2050])).

cnf(c_4399,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4396,c_2568])).

cnf(c_9593,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6329,c_63,c_64,c_4391,c_4399])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2049,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6328,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6322,c_2049])).

cnf(c_10062,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6328,c_63,c_64,c_4391,c_4399])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2044,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2052,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3407,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2044,c_2052])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3408,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3407,c_31])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_418,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_419,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_421,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_35])).

cnf(c_2041,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2115])).

cnf(c_2266,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2041,c_35,c_33,c_419,c_2134])).

cnf(c_3463,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3408,c_2266])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2046,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3911,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2051,c_2046])).

cnf(c_48,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8614,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | k2_relat_1(X0) = k1_xboole_0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3911,c_48])).

cnf(c_8615,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8614])).

cnf(c_8619,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_8615])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_432,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_433,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_435,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_35])).

cnf(c_2040,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_2227,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2040,c_35,c_33,c_433,c_2134])).

cnf(c_8620,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8619,c_2227])).

cnf(c_8621,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8620,c_2227])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2102,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2103,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2102])).

cnf(c_2135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2400,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2401,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_3895,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_2050])).

cnf(c_3896,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3895,c_3463])).

cnf(c_3905,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_2051])).

cnf(c_3912,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3905,c_3463])).

cnf(c_4581,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3912,c_36,c_38,c_2103,c_2135,c_2401])).

cnf(c_4590,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4581,c_2046])).

cnf(c_8929,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8621,c_36,c_38,c_2103,c_2135,c_2401,c_3896,c_4590])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2048,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3910,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2051,c_2048])).

cnf(c_7520,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3910,c_48])).

cnf(c_7525,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_7520])).

cnf(c_7532,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7525,c_2227])).

cnf(c_7533,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7532,c_2227])).

cnf(c_4589,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4581,c_2048])).

cnf(c_8156,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7533,c_36,c_38,c_2103,c_2135,c_2401,c_3896,c_4589])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2045,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2222,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2045,c_36,c_38,c_40,c_2103,c_2135])).

cnf(c_2223,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2222])).

cnf(c_8166,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8156,c_2223])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_452,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_5])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_19,c_18,c_5])).

cnf(c_457,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_2039,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_2340,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2039])).

cnf(c_8181,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8166,c_2340])).

cnf(c_8182,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8181])).

cnf(c_8935,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8929,c_8182])).

cnf(c_8938,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8935,c_2340])).

cnf(c_3401,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_2059])).

cnf(c_3402,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3401,c_2266])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2537,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4523,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3402,c_33,c_2134,c_2537])).

cnf(c_4524,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4523])).

cnf(c_4525,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4524,c_3408])).

cnf(c_8972,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8938,c_4525])).

cnf(c_8984,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8972])).

cnf(c_9147,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8984,c_2223])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2061,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3343,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_2061])).

cnf(c_3344,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3343])).

cnf(c_3664,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_funct_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3343,c_35,c_33,c_2134,c_2400,c_3344])).

cnf(c_3665,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3664])).

cnf(c_8978,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8938,c_3665])).

cnf(c_8982,plain,
    ( k2_funct_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8978])).

cnf(c_9151,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9147,c_8982])).

cnf(c_10074,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10062,c_9151])).

cnf(c_10226,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9593,c_10074])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.21/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.05  
% 4.21/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.21/1.05  
% 4.21/1.05  ------  iProver source info
% 4.21/1.05  
% 4.21/1.05  git: date: 2020-06-30 10:37:57 +0100
% 4.21/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.21/1.05  git: non_committed_changes: false
% 4.21/1.05  git: last_make_outside_of_git: false
% 4.21/1.05  
% 4.21/1.05  ------ 
% 4.21/1.05  
% 4.21/1.05  ------ Input Options
% 4.21/1.05  
% 4.21/1.05  --out_options                           all
% 4.21/1.05  --tptp_safe_out                         true
% 4.21/1.05  --problem_path                          ""
% 4.21/1.05  --include_path                          ""
% 4.21/1.05  --clausifier                            res/vclausify_rel
% 4.21/1.05  --clausifier_options                    ""
% 4.21/1.05  --stdin                                 false
% 4.21/1.05  --stats_out                             all
% 4.21/1.05  
% 4.21/1.05  ------ General Options
% 4.21/1.05  
% 4.21/1.05  --fof                                   false
% 4.21/1.05  --time_out_real                         305.
% 4.21/1.05  --time_out_virtual                      -1.
% 4.21/1.05  --symbol_type_check                     false
% 4.21/1.05  --clausify_out                          false
% 4.21/1.05  --sig_cnt_out                           false
% 4.21/1.05  --trig_cnt_out                          false
% 4.21/1.05  --trig_cnt_out_tolerance                1.
% 4.21/1.05  --trig_cnt_out_sk_spl                   false
% 4.21/1.05  --abstr_cl_out                          false
% 4.21/1.05  
% 4.21/1.05  ------ Global Options
% 4.21/1.05  
% 4.21/1.05  --schedule                              default
% 4.21/1.05  --add_important_lit                     false
% 4.21/1.05  --prop_solver_per_cl                    1000
% 4.21/1.05  --min_unsat_core                        false
% 4.21/1.05  --soft_assumptions                      false
% 4.21/1.05  --soft_lemma_size                       3
% 4.21/1.05  --prop_impl_unit_size                   0
% 4.21/1.05  --prop_impl_unit                        []
% 4.21/1.05  --share_sel_clauses                     true
% 4.21/1.05  --reset_solvers                         false
% 4.21/1.05  --bc_imp_inh                            [conj_cone]
% 4.21/1.05  --conj_cone_tolerance                   3.
% 4.21/1.05  --extra_neg_conj                        none
% 4.21/1.05  --large_theory_mode                     true
% 4.21/1.05  --prolific_symb_bound                   200
% 4.21/1.05  --lt_threshold                          2000
% 4.21/1.05  --clause_weak_htbl                      true
% 4.21/1.05  --gc_record_bc_elim                     false
% 4.21/1.05  
% 4.21/1.05  ------ Preprocessing Options
% 4.21/1.05  
% 4.21/1.05  --preprocessing_flag                    true
% 4.21/1.05  --time_out_prep_mult                    0.1
% 4.21/1.05  --splitting_mode                        input
% 4.21/1.05  --splitting_grd                         true
% 4.21/1.05  --splitting_cvd                         false
% 4.21/1.05  --splitting_cvd_svl                     false
% 4.21/1.05  --splitting_nvd                         32
% 4.21/1.05  --sub_typing                            true
% 4.21/1.05  --prep_gs_sim                           true
% 4.21/1.05  --prep_unflatten                        true
% 4.21/1.05  --prep_res_sim                          true
% 4.21/1.05  --prep_upred                            true
% 4.21/1.05  --prep_sem_filter                       exhaustive
% 4.21/1.05  --prep_sem_filter_out                   false
% 4.21/1.05  --pred_elim                             true
% 4.21/1.05  --res_sim_input                         true
% 4.21/1.05  --eq_ax_congr_red                       true
% 4.21/1.05  --pure_diseq_elim                       true
% 4.21/1.05  --brand_transform                       false
% 4.21/1.05  --non_eq_to_eq                          false
% 4.21/1.05  --prep_def_merge                        true
% 4.21/1.05  --prep_def_merge_prop_impl              false
% 4.21/1.05  --prep_def_merge_mbd                    true
% 4.21/1.05  --prep_def_merge_tr_red                 false
% 4.21/1.05  --prep_def_merge_tr_cl                  false
% 4.21/1.05  --smt_preprocessing                     true
% 4.21/1.05  --smt_ac_axioms                         fast
% 4.21/1.05  --preprocessed_out                      false
% 4.21/1.05  --preprocessed_stats                    false
% 4.21/1.05  
% 4.21/1.05  ------ Abstraction refinement Options
% 4.21/1.05  
% 4.21/1.05  --abstr_ref                             []
% 4.21/1.05  --abstr_ref_prep                        false
% 4.21/1.05  --abstr_ref_until_sat                   false
% 4.21/1.05  --abstr_ref_sig_restrict                funpre
% 4.21/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 4.21/1.05  --abstr_ref_under                       []
% 4.21/1.05  
% 4.21/1.05  ------ SAT Options
% 4.21/1.05  
% 4.21/1.05  --sat_mode                              false
% 4.21/1.05  --sat_fm_restart_options                ""
% 4.21/1.05  --sat_gr_def                            false
% 4.21/1.05  --sat_epr_types                         true
% 4.21/1.05  --sat_non_cyclic_types                  false
% 4.21/1.05  --sat_finite_models                     false
% 4.21/1.05  --sat_fm_lemmas                         false
% 4.21/1.05  --sat_fm_prep                           false
% 4.21/1.05  --sat_fm_uc_incr                        true
% 4.21/1.05  --sat_out_model                         small
% 4.21/1.05  --sat_out_clauses                       false
% 4.21/1.05  
% 4.21/1.05  ------ QBF Options
% 4.21/1.05  
% 4.21/1.05  --qbf_mode                              false
% 4.21/1.05  --qbf_elim_univ                         false
% 4.21/1.05  --qbf_dom_inst                          none
% 4.21/1.05  --qbf_dom_pre_inst                      false
% 4.21/1.05  --qbf_sk_in                             false
% 4.21/1.05  --qbf_pred_elim                         true
% 4.21/1.05  --qbf_split                             512
% 4.21/1.05  
% 4.21/1.05  ------ BMC1 Options
% 4.21/1.05  
% 4.21/1.05  --bmc1_incremental                      false
% 4.21/1.05  --bmc1_axioms                           reachable_all
% 4.21/1.05  --bmc1_min_bound                        0
% 4.21/1.05  --bmc1_max_bound                        -1
% 4.21/1.05  --bmc1_max_bound_default                -1
% 4.21/1.05  --bmc1_symbol_reachability              true
% 4.21/1.05  --bmc1_property_lemmas                  false
% 4.21/1.05  --bmc1_k_induction                      false
% 4.21/1.05  --bmc1_non_equiv_states                 false
% 4.21/1.05  --bmc1_deadlock                         false
% 4.21/1.05  --bmc1_ucm                              false
% 4.21/1.05  --bmc1_add_unsat_core                   none
% 4.21/1.05  --bmc1_unsat_core_children              false
% 4.21/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 4.21/1.05  --bmc1_out_stat                         full
% 4.21/1.05  --bmc1_ground_init                      false
% 4.21/1.05  --bmc1_pre_inst_next_state              false
% 4.21/1.05  --bmc1_pre_inst_state                   false
% 4.21/1.05  --bmc1_pre_inst_reach_state             false
% 4.21/1.05  --bmc1_out_unsat_core                   false
% 4.21/1.05  --bmc1_aig_witness_out                  false
% 4.21/1.05  --bmc1_verbose                          false
% 4.21/1.05  --bmc1_dump_clauses_tptp                false
% 4.21/1.05  --bmc1_dump_unsat_core_tptp             false
% 4.21/1.05  --bmc1_dump_file                        -
% 4.21/1.05  --bmc1_ucm_expand_uc_limit              128
% 4.21/1.05  --bmc1_ucm_n_expand_iterations          6
% 4.21/1.05  --bmc1_ucm_extend_mode                  1
% 4.21/1.05  --bmc1_ucm_init_mode                    2
% 4.21/1.05  --bmc1_ucm_cone_mode                    none
% 4.21/1.05  --bmc1_ucm_reduced_relation_type        0
% 4.21/1.05  --bmc1_ucm_relax_model                  4
% 4.21/1.05  --bmc1_ucm_full_tr_after_sat            true
% 4.21/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 4.21/1.05  --bmc1_ucm_layered_model                none
% 4.21/1.05  --bmc1_ucm_max_lemma_size               10
% 4.21/1.05  
% 4.21/1.05  ------ AIG Options
% 4.21/1.05  
% 4.21/1.05  --aig_mode                              false
% 4.21/1.05  
% 4.21/1.05  ------ Instantiation Options
% 4.21/1.05  
% 4.21/1.05  --instantiation_flag                    true
% 4.21/1.05  --inst_sos_flag                         true
% 4.21/1.05  --inst_sos_phase                        true
% 4.21/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.21/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.21/1.05  --inst_lit_sel_side                     num_symb
% 4.21/1.05  --inst_solver_per_active                1400
% 4.21/1.05  --inst_solver_calls_frac                1.
% 4.21/1.05  --inst_passive_queue_type               priority_queues
% 4.21/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.21/1.05  --inst_passive_queues_freq              [25;2]
% 4.21/1.05  --inst_dismatching                      true
% 4.21/1.05  --inst_eager_unprocessed_to_passive     true
% 4.21/1.05  --inst_prop_sim_given                   true
% 4.21/1.05  --inst_prop_sim_new                     false
% 4.21/1.05  --inst_subs_new                         false
% 4.21/1.05  --inst_eq_res_simp                      false
% 4.21/1.05  --inst_subs_given                       false
% 4.21/1.05  --inst_orphan_elimination               true
% 4.21/1.05  --inst_learning_loop_flag               true
% 4.21/1.05  --inst_learning_start                   3000
% 4.21/1.05  --inst_learning_factor                  2
% 4.21/1.05  --inst_start_prop_sim_after_learn       3
% 4.21/1.05  --inst_sel_renew                        solver
% 4.21/1.05  --inst_lit_activity_flag                true
% 4.21/1.05  --inst_restr_to_given                   false
% 4.21/1.05  --inst_activity_threshold               500
% 4.21/1.05  --inst_out_proof                        true
% 4.21/1.05  
% 4.21/1.05  ------ Resolution Options
% 4.21/1.05  
% 4.21/1.05  --resolution_flag                       true
% 4.21/1.05  --res_lit_sel                           adaptive
% 4.21/1.05  --res_lit_sel_side                      none
% 4.21/1.05  --res_ordering                          kbo
% 4.21/1.05  --res_to_prop_solver                    active
% 4.21/1.05  --res_prop_simpl_new                    false
% 4.21/1.05  --res_prop_simpl_given                  true
% 4.21/1.05  --res_passive_queue_type                priority_queues
% 4.21/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.21/1.05  --res_passive_queues_freq               [15;5]
% 4.21/1.05  --res_forward_subs                      full
% 4.21/1.05  --res_backward_subs                     full
% 4.21/1.05  --res_forward_subs_resolution           true
% 4.21/1.05  --res_backward_subs_resolution          true
% 4.21/1.05  --res_orphan_elimination                true
% 4.21/1.05  --res_time_limit                        2.
% 4.21/1.05  --res_out_proof                         true
% 4.21/1.05  
% 4.21/1.05  ------ Superposition Options
% 4.21/1.05  
% 4.21/1.05  --superposition_flag                    true
% 4.21/1.05  --sup_passive_queue_type                priority_queues
% 4.21/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.21/1.05  --sup_passive_queues_freq               [8;1;4]
% 4.21/1.05  --demod_completeness_check              fast
% 4.21/1.05  --demod_use_ground                      true
% 4.21/1.05  --sup_to_prop_solver                    passive
% 4.21/1.05  --sup_prop_simpl_new                    true
% 4.21/1.05  --sup_prop_simpl_given                  true
% 4.21/1.05  --sup_fun_splitting                     true
% 4.21/1.05  --sup_smt_interval                      50000
% 4.21/1.05  
% 4.21/1.05  ------ Superposition Simplification Setup
% 4.21/1.05  
% 4.21/1.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.21/1.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.21/1.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.21/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 4.21/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.21/1.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.21/1.05  --sup_immed_triv                        [TrivRules]
% 4.21/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.05  --sup_immed_bw_main                     []
% 4.21/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.21/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 4.21/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.05  --sup_input_bw                          []
% 4.21/1.05  
% 4.21/1.05  ------ Combination Options
% 4.21/1.05  
% 4.21/1.05  --comb_res_mult                         3
% 4.21/1.05  --comb_sup_mult                         2
% 4.21/1.05  --comb_inst_mult                        10
% 4.21/1.05  
% 4.21/1.05  ------ Debug Options
% 4.21/1.05  
% 4.21/1.05  --dbg_backtrace                         false
% 4.21/1.05  --dbg_dump_prop_clauses                 false
% 4.21/1.05  --dbg_dump_prop_clauses_file            -
% 4.21/1.05  --dbg_out_stat                          false
% 4.21/1.05  ------ Parsing...
% 4.21/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.21/1.05  
% 4.21/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.21/1.05  
% 4.21/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.21/1.05  
% 4.21/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.21/1.05  ------ Proving...
% 4.21/1.05  ------ Problem Properties 
% 4.21/1.05  
% 4.21/1.05  
% 4.21/1.05  clauses                                 30
% 4.21/1.05  conjectures                             5
% 4.21/1.05  EPR                                     6
% 4.21/1.05  Horn                                    28
% 4.21/1.05  unary                                   8
% 4.21/1.05  binary                                  9
% 4.21/1.05  lits                                    75
% 4.21/1.05  lits eq                                 15
% 4.21/1.05  fd_pure                                 0
% 4.21/1.05  fd_pseudo                               0
% 4.21/1.05  fd_cond                                 5
% 4.21/1.05  fd_pseudo_cond                          0
% 4.21/1.05  AC symbols                              0
% 4.21/1.05  
% 4.21/1.05  ------ Schedule dynamic 5 is on 
% 4.21/1.05  
% 4.21/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.21/1.05  
% 4.21/1.05  
% 4.21/1.05  ------ 
% 4.21/1.05  Current options:
% 4.21/1.05  ------ 
% 4.21/1.05  
% 4.21/1.05  ------ Input Options
% 4.21/1.05  
% 4.21/1.05  --out_options                           all
% 4.21/1.05  --tptp_safe_out                         true
% 4.21/1.05  --problem_path                          ""
% 4.21/1.05  --include_path                          ""
% 4.21/1.05  --clausifier                            res/vclausify_rel
% 4.21/1.05  --clausifier_options                    ""
% 4.21/1.05  --stdin                                 false
% 4.21/1.05  --stats_out                             all
% 4.21/1.05  
% 4.21/1.05  ------ General Options
% 4.21/1.05  
% 4.21/1.05  --fof                                   false
% 4.21/1.05  --time_out_real                         305.
% 4.21/1.05  --time_out_virtual                      -1.
% 4.21/1.05  --symbol_type_check                     false
% 4.21/1.05  --clausify_out                          false
% 4.21/1.05  --sig_cnt_out                           false
% 4.21/1.05  --trig_cnt_out                          false
% 4.21/1.05  --trig_cnt_out_tolerance                1.
% 4.21/1.05  --trig_cnt_out_sk_spl                   false
% 4.21/1.05  --abstr_cl_out                          false
% 4.21/1.05  
% 4.21/1.05  ------ Global Options
% 4.21/1.05  
% 4.21/1.05  --schedule                              default
% 4.21/1.05  --add_important_lit                     false
% 4.21/1.05  --prop_solver_per_cl                    1000
% 4.21/1.05  --min_unsat_core                        false
% 4.21/1.05  --soft_assumptions                      false
% 4.21/1.05  --soft_lemma_size                       3
% 4.21/1.05  --prop_impl_unit_size                   0
% 4.21/1.05  --prop_impl_unit                        []
% 4.21/1.05  --share_sel_clauses                     true
% 4.21/1.05  --reset_solvers                         false
% 4.21/1.05  --bc_imp_inh                            [conj_cone]
% 4.21/1.05  --conj_cone_tolerance                   3.
% 4.21/1.05  --extra_neg_conj                        none
% 4.21/1.05  --large_theory_mode                     true
% 4.21/1.05  --prolific_symb_bound                   200
% 4.21/1.05  --lt_threshold                          2000
% 4.21/1.05  --clause_weak_htbl                      true
% 4.21/1.05  --gc_record_bc_elim                     false
% 4.21/1.05  
% 4.21/1.05  ------ Preprocessing Options
% 4.21/1.05  
% 4.21/1.05  --preprocessing_flag                    true
% 4.21/1.05  --time_out_prep_mult                    0.1
% 4.21/1.05  --splitting_mode                        input
% 4.21/1.05  --splitting_grd                         true
% 4.21/1.05  --splitting_cvd                         false
% 4.21/1.05  --splitting_cvd_svl                     false
% 4.21/1.05  --splitting_nvd                         32
% 4.21/1.05  --sub_typing                            true
% 4.21/1.05  --prep_gs_sim                           true
% 4.21/1.05  --prep_unflatten                        true
% 4.21/1.05  --prep_res_sim                          true
% 4.21/1.05  --prep_upred                            true
% 4.21/1.05  --prep_sem_filter                       exhaustive
% 4.21/1.05  --prep_sem_filter_out                   false
% 4.21/1.05  --pred_elim                             true
% 4.21/1.05  --res_sim_input                         true
% 4.21/1.05  --eq_ax_congr_red                       true
% 4.21/1.05  --pure_diseq_elim                       true
% 4.21/1.05  --brand_transform                       false
% 4.21/1.05  --non_eq_to_eq                          false
% 4.21/1.05  --prep_def_merge                        true
% 4.21/1.05  --prep_def_merge_prop_impl              false
% 4.21/1.05  --prep_def_merge_mbd                    true
% 4.21/1.05  --prep_def_merge_tr_red                 false
% 4.21/1.05  --prep_def_merge_tr_cl                  false
% 4.21/1.05  --smt_preprocessing                     true
% 4.21/1.05  --smt_ac_axioms                         fast
% 4.21/1.05  --preprocessed_out                      false
% 4.21/1.05  --preprocessed_stats                    false
% 4.21/1.05  
% 4.21/1.05  ------ Abstraction refinement Options
% 4.21/1.05  
% 4.21/1.05  --abstr_ref                             []
% 4.21/1.05  --abstr_ref_prep                        false
% 4.21/1.05  --abstr_ref_until_sat                   false
% 4.21/1.05  --abstr_ref_sig_restrict                funpre
% 4.21/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 4.21/1.05  --abstr_ref_under                       []
% 4.21/1.05  
% 4.21/1.05  ------ SAT Options
% 4.21/1.05  
% 4.21/1.05  --sat_mode                              false
% 4.21/1.05  --sat_fm_restart_options                ""
% 4.21/1.05  --sat_gr_def                            false
% 4.21/1.05  --sat_epr_types                         true
% 4.21/1.05  --sat_non_cyclic_types                  false
% 4.21/1.05  --sat_finite_models                     false
% 4.21/1.05  --sat_fm_lemmas                         false
% 4.21/1.05  --sat_fm_prep                           false
% 4.21/1.05  --sat_fm_uc_incr                        true
% 4.21/1.05  --sat_out_model                         small
% 4.21/1.05  --sat_out_clauses                       false
% 4.21/1.05  
% 4.21/1.05  ------ QBF Options
% 4.21/1.05  
% 4.21/1.05  --qbf_mode                              false
% 4.21/1.05  --qbf_elim_univ                         false
% 4.21/1.05  --qbf_dom_inst                          none
% 4.21/1.05  --qbf_dom_pre_inst                      false
% 4.21/1.05  --qbf_sk_in                             false
% 4.21/1.05  --qbf_pred_elim                         true
% 4.21/1.05  --qbf_split                             512
% 4.21/1.05  
% 4.21/1.05  ------ BMC1 Options
% 4.21/1.05  
% 4.21/1.05  --bmc1_incremental                      false
% 4.21/1.05  --bmc1_axioms                           reachable_all
% 4.21/1.05  --bmc1_min_bound                        0
% 4.21/1.05  --bmc1_max_bound                        -1
% 4.21/1.05  --bmc1_max_bound_default                -1
% 4.21/1.05  --bmc1_symbol_reachability              true
% 4.21/1.05  --bmc1_property_lemmas                  false
% 4.21/1.05  --bmc1_k_induction                      false
% 4.21/1.05  --bmc1_non_equiv_states                 false
% 4.21/1.05  --bmc1_deadlock                         false
% 4.21/1.05  --bmc1_ucm                              false
% 4.21/1.05  --bmc1_add_unsat_core                   none
% 4.21/1.05  --bmc1_unsat_core_children              false
% 4.21/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 4.21/1.05  --bmc1_out_stat                         full
% 4.21/1.05  --bmc1_ground_init                      false
% 4.21/1.05  --bmc1_pre_inst_next_state              false
% 4.21/1.05  --bmc1_pre_inst_state                   false
% 4.21/1.05  --bmc1_pre_inst_reach_state             false
% 4.21/1.05  --bmc1_out_unsat_core                   false
% 4.21/1.05  --bmc1_aig_witness_out                  false
% 4.21/1.05  --bmc1_verbose                          false
% 4.21/1.05  --bmc1_dump_clauses_tptp                false
% 4.21/1.05  --bmc1_dump_unsat_core_tptp             false
% 4.21/1.05  --bmc1_dump_file                        -
% 4.21/1.05  --bmc1_ucm_expand_uc_limit              128
% 4.21/1.05  --bmc1_ucm_n_expand_iterations          6
% 4.21/1.05  --bmc1_ucm_extend_mode                  1
% 4.21/1.05  --bmc1_ucm_init_mode                    2
% 4.21/1.05  --bmc1_ucm_cone_mode                    none
% 4.21/1.05  --bmc1_ucm_reduced_relation_type        0
% 4.21/1.05  --bmc1_ucm_relax_model                  4
% 4.21/1.05  --bmc1_ucm_full_tr_after_sat            true
% 4.21/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 4.21/1.05  --bmc1_ucm_layered_model                none
% 4.21/1.05  --bmc1_ucm_max_lemma_size               10
% 4.21/1.05  
% 4.21/1.05  ------ AIG Options
% 4.21/1.05  
% 4.21/1.05  --aig_mode                              false
% 4.21/1.05  
% 4.21/1.05  ------ Instantiation Options
% 4.21/1.05  
% 4.21/1.05  --instantiation_flag                    true
% 4.21/1.05  --inst_sos_flag                         true
% 4.21/1.05  --inst_sos_phase                        true
% 4.21/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.21/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.21/1.05  --inst_lit_sel_side                     none
% 4.21/1.05  --inst_solver_per_active                1400
% 4.21/1.05  --inst_solver_calls_frac                1.
% 4.21/1.05  --inst_passive_queue_type               priority_queues
% 4.21/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.21/1.05  --inst_passive_queues_freq              [25;2]
% 4.21/1.05  --inst_dismatching                      true
% 4.21/1.05  --inst_eager_unprocessed_to_passive     true
% 4.21/1.05  --inst_prop_sim_given                   true
% 4.21/1.05  --inst_prop_sim_new                     false
% 4.21/1.05  --inst_subs_new                         false
% 4.21/1.05  --inst_eq_res_simp                      false
% 4.21/1.05  --inst_subs_given                       false
% 4.21/1.05  --inst_orphan_elimination               true
% 4.21/1.05  --inst_learning_loop_flag               true
% 4.21/1.05  --inst_learning_start                   3000
% 4.21/1.05  --inst_learning_factor                  2
% 4.21/1.05  --inst_start_prop_sim_after_learn       3
% 4.21/1.05  --inst_sel_renew                        solver
% 4.21/1.05  --inst_lit_activity_flag                true
% 4.21/1.05  --inst_restr_to_given                   false
% 4.21/1.05  --inst_activity_threshold               500
% 4.21/1.05  --inst_out_proof                        true
% 4.21/1.05  
% 4.21/1.05  ------ Resolution Options
% 4.21/1.05  
% 4.21/1.05  --resolution_flag                       false
% 4.21/1.05  --res_lit_sel                           adaptive
% 4.21/1.05  --res_lit_sel_side                      none
% 4.21/1.05  --res_ordering                          kbo
% 4.21/1.05  --res_to_prop_solver                    active
% 4.21/1.05  --res_prop_simpl_new                    false
% 4.21/1.05  --res_prop_simpl_given                  true
% 4.21/1.05  --res_passive_queue_type                priority_queues
% 4.21/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.21/1.05  --res_passive_queues_freq               [15;5]
% 4.21/1.05  --res_forward_subs                      full
% 4.21/1.05  --res_backward_subs                     full
% 4.21/1.05  --res_forward_subs_resolution           true
% 4.21/1.05  --res_backward_subs_resolution          true
% 4.21/1.05  --res_orphan_elimination                true
% 4.21/1.05  --res_time_limit                        2.
% 4.21/1.05  --res_out_proof                         true
% 4.21/1.05  
% 4.21/1.05  ------ Superposition Options
% 4.21/1.05  
% 4.21/1.05  --superposition_flag                    true
% 4.21/1.05  --sup_passive_queue_type                priority_queues
% 4.21/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.21/1.05  --sup_passive_queues_freq               [8;1;4]
% 4.21/1.05  --demod_completeness_check              fast
% 4.21/1.05  --demod_use_ground                      true
% 4.21/1.05  --sup_to_prop_solver                    passive
% 4.21/1.05  --sup_prop_simpl_new                    true
% 4.21/1.05  --sup_prop_simpl_given                  true
% 4.21/1.05  --sup_fun_splitting                     true
% 4.21/1.05  --sup_smt_interval                      50000
% 4.21/1.05  
% 4.21/1.05  ------ Superposition Simplification Setup
% 4.21/1.05  
% 4.21/1.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.21/1.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.21/1.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.21/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 4.21/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.21/1.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.21/1.05  --sup_immed_triv                        [TrivRules]
% 4.21/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.05  --sup_immed_bw_main                     []
% 4.21/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.21/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 4.21/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.05  --sup_input_bw                          []
% 4.21/1.05  
% 4.21/1.05  ------ Combination Options
% 4.21/1.05  
% 4.21/1.05  --comb_res_mult                         3
% 4.21/1.05  --comb_sup_mult                         2
% 4.21/1.05  --comb_inst_mult                        10
% 4.21/1.05  
% 4.21/1.05  ------ Debug Options
% 4.21/1.05  
% 4.21/1.05  --dbg_backtrace                         false
% 4.21/1.05  --dbg_dump_prop_clauses                 false
% 4.21/1.05  --dbg_dump_prop_clauses_file            -
% 4.21/1.05  --dbg_out_stat                          false
% 4.21/1.05  
% 4.21/1.05  
% 4.21/1.05  
% 4.21/1.05  
% 4.21/1.05  ------ Proving...
% 4.21/1.05  
% 4.21/1.05  
% 4.21/1.05  % SZS status Theorem for theBenchmark.p
% 4.21/1.05  
% 4.21/1.05   Resolution empty clause
% 4.21/1.05  
% 4.21/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 4.21/1.05  
% 4.21/1.05  fof(f1,axiom,(
% 4.21/1.05    v1_xboole_0(k1_xboole_0)),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f49,plain,(
% 4.21/1.05    v1_xboole_0(k1_xboole_0)),
% 4.21/1.05    inference(cnf_transformation,[],[f1])).
% 4.21/1.05  
% 4.21/1.05  fof(f5,axiom,(
% 4.21/1.05    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f25,plain,(
% 4.21/1.05    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 4.21/1.05    inference(ennf_transformation,[],[f5])).
% 4.21/1.05  
% 4.21/1.05  fof(f55,plain,(
% 4.21/1.05    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f25])).
% 4.21/1.05  
% 4.21/1.05  fof(f2,axiom,(
% 4.21/1.05    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f23,plain,(
% 4.21/1.05    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.21/1.05    inference(ennf_transformation,[],[f2])).
% 4.21/1.05  
% 4.21/1.05  fof(f50,plain,(
% 4.21/1.05    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f23])).
% 4.21/1.05  
% 4.21/1.05  fof(f15,axiom,(
% 4.21/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f36,plain,(
% 4.21/1.05    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.21/1.05    inference(ennf_transformation,[],[f15])).
% 4.21/1.05  
% 4.21/1.05  fof(f37,plain,(
% 4.21/1.05    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.21/1.05    inference(flattening,[],[f36])).
% 4.21/1.05  
% 4.21/1.05  fof(f72,plain,(
% 4.21/1.05    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f37])).
% 4.21/1.05  
% 4.21/1.05  fof(f11,axiom,(
% 4.21/1.05    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f19,plain,(
% 4.21/1.05    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 4.21/1.05    inference(pure_predicate_removal,[],[f11])).
% 4.21/1.05  
% 4.21/1.05  fof(f21,plain,(
% 4.21/1.05    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 4.21/1.05    inference(pure_predicate_removal,[],[f19])).
% 4.21/1.05  
% 4.21/1.05  fof(f46,plain,(
% 4.21/1.05    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 4.21/1.05    inference(rectify,[],[f21])).
% 4.21/1.05  
% 4.21/1.05  fof(f65,plain,(
% 4.21/1.05    v1_relat_1(k1_xboole_0)),
% 4.21/1.05    inference(cnf_transformation,[],[f46])).
% 4.21/1.05  
% 4.21/1.05  fof(f66,plain,(
% 4.21/1.05    v1_funct_1(k1_xboole_0)),
% 4.21/1.05    inference(cnf_transformation,[],[f46])).
% 4.21/1.05  
% 4.21/1.05  fof(f8,axiom,(
% 4.21/1.05    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f28,plain,(
% 4.21/1.05    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.21/1.05    inference(ennf_transformation,[],[f8])).
% 4.21/1.05  
% 4.21/1.05  fof(f45,plain,(
% 4.21/1.05    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.21/1.05    inference(nnf_transformation,[],[f28])).
% 4.21/1.05  
% 4.21/1.05  fof(f60,plain,(
% 4.21/1.05    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f45])).
% 4.21/1.05  
% 4.21/1.05  fof(f16,axiom,(
% 4.21/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f38,plain,(
% 4.21/1.05    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.21/1.05    inference(ennf_transformation,[],[f16])).
% 4.21/1.05  
% 4.21/1.05  fof(f39,plain,(
% 4.21/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.21/1.05    inference(flattening,[],[f38])).
% 4.21/1.05  
% 4.21/1.05  fof(f76,plain,(
% 4.21/1.05    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f39])).
% 4.21/1.05  
% 4.21/1.05  fof(f86,plain,(
% 4.21/1.05    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 4.21/1.05    inference(equality_resolution,[],[f76])).
% 4.21/1.05  
% 4.21/1.05  fof(f4,axiom,(
% 4.21/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f24,plain,(
% 4.21/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.21/1.05    inference(ennf_transformation,[],[f4])).
% 4.21/1.05  
% 4.21/1.05  fof(f43,plain,(
% 4.21/1.05    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.21/1.05    inference(nnf_transformation,[],[f24])).
% 4.21/1.05  
% 4.21/1.05  fof(f53,plain,(
% 4.21/1.05    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f43])).
% 4.21/1.05  
% 4.21/1.05  fof(f6,axiom,(
% 4.21/1.05    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f20,plain,(
% 4.21/1.05    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 4.21/1.05    inference(pure_predicate_removal,[],[f6])).
% 4.21/1.05  
% 4.21/1.05  fof(f44,plain,(
% 4.21/1.05    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 4.21/1.05    inference(rectify,[],[f20])).
% 4.21/1.05  
% 4.21/1.05  fof(f56,plain,(
% 4.21/1.05    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f44])).
% 4.21/1.05  
% 4.21/1.05  fof(f71,plain,(
% 4.21/1.05    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f37])).
% 4.21/1.05  
% 4.21/1.05  fof(f78,plain,(
% 4.21/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f39])).
% 4.21/1.05  
% 4.21/1.05  fof(f85,plain,(
% 4.21/1.05    ( ! [X2,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 4.21/1.05    inference(equality_resolution,[],[f78])).
% 4.21/1.05  
% 4.21/1.05  fof(f17,conjecture,(
% 4.21/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f18,negated_conjecture,(
% 4.21/1.05    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 4.21/1.05    inference(negated_conjecture,[],[f17])).
% 4.21/1.05  
% 4.21/1.05  fof(f40,plain,(
% 4.21/1.05    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.21/1.05    inference(ennf_transformation,[],[f18])).
% 4.21/1.05  
% 4.21/1.05  fof(f41,plain,(
% 4.21/1.05    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.21/1.05    inference(flattening,[],[f40])).
% 4.21/1.05  
% 4.21/1.05  fof(f47,plain,(
% 4.21/1.05    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 4.21/1.05    introduced(choice_axiom,[])).
% 4.21/1.05  
% 4.21/1.05  fof(f48,plain,(
% 4.21/1.05    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 4.21/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f47])).
% 4.21/1.05  
% 4.21/1.05  fof(f81,plain,(
% 4.21/1.05    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.21/1.05    inference(cnf_transformation,[],[f48])).
% 4.21/1.05  
% 4.21/1.05  fof(f14,axiom,(
% 4.21/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f35,plain,(
% 4.21/1.05    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.21/1.05    inference(ennf_transformation,[],[f14])).
% 4.21/1.05  
% 4.21/1.05  fof(f69,plain,(
% 4.21/1.05    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.21/1.05    inference(cnf_transformation,[],[f35])).
% 4.21/1.05  
% 4.21/1.05  fof(f83,plain,(
% 4.21/1.05    k2_relset_1(sK0,sK1,sK2) = sK1),
% 4.21/1.05    inference(cnf_transformation,[],[f48])).
% 4.21/1.05  
% 4.21/1.05  fof(f10,axiom,(
% 4.21/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f31,plain,(
% 4.21/1.05    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.21/1.05    inference(ennf_transformation,[],[f10])).
% 4.21/1.05  
% 4.21/1.05  fof(f32,plain,(
% 4.21/1.05    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.21/1.05    inference(flattening,[],[f31])).
% 4.21/1.05  
% 4.21/1.05  fof(f63,plain,(
% 4.21/1.05    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f32])).
% 4.21/1.05  
% 4.21/1.05  fof(f82,plain,(
% 4.21/1.05    v2_funct_1(sK2)),
% 4.21/1.05    inference(cnf_transformation,[],[f48])).
% 4.21/1.05  
% 4.21/1.05  fof(f79,plain,(
% 4.21/1.05    v1_funct_1(sK2)),
% 4.21/1.05    inference(cnf_transformation,[],[f48])).
% 4.21/1.05  
% 4.21/1.05  fof(f12,axiom,(
% 4.21/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f33,plain,(
% 4.21/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.21/1.05    inference(ennf_transformation,[],[f12])).
% 4.21/1.05  
% 4.21/1.05  fof(f67,plain,(
% 4.21/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.21/1.05    inference(cnf_transformation,[],[f33])).
% 4.21/1.05  
% 4.21/1.05  fof(f75,plain,(
% 4.21/1.05    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f39])).
% 4.21/1.05  
% 4.21/1.05  fof(f64,plain,(
% 4.21/1.05    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f32])).
% 4.21/1.05  
% 4.21/1.05  fof(f9,axiom,(
% 4.21/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f29,plain,(
% 4.21/1.05    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.21/1.05    inference(ennf_transformation,[],[f9])).
% 4.21/1.05  
% 4.21/1.05  fof(f30,plain,(
% 4.21/1.05    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.21/1.05    inference(flattening,[],[f29])).
% 4.21/1.05  
% 4.21/1.05  fof(f62,plain,(
% 4.21/1.05    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f30])).
% 4.21/1.05  
% 4.21/1.05  fof(f61,plain,(
% 4.21/1.05    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f30])).
% 4.21/1.05  
% 4.21/1.05  fof(f77,plain,(
% 4.21/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f39])).
% 4.21/1.05  
% 4.21/1.05  fof(f84,plain,(
% 4.21/1.05    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 4.21/1.05    inference(cnf_transformation,[],[f48])).
% 4.21/1.05  
% 4.21/1.05  fof(f13,axiom,(
% 4.21/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f22,plain,(
% 4.21/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 4.21/1.05    inference(pure_predicate_removal,[],[f13])).
% 4.21/1.05  
% 4.21/1.05  fof(f34,plain,(
% 4.21/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.21/1.05    inference(ennf_transformation,[],[f22])).
% 4.21/1.05  
% 4.21/1.05  fof(f68,plain,(
% 4.21/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.21/1.05    inference(cnf_transformation,[],[f34])).
% 4.21/1.05  
% 4.21/1.05  fof(f59,plain,(
% 4.21/1.05    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f45])).
% 4.21/1.05  
% 4.21/1.05  fof(f7,axiom,(
% 4.21/1.05    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 4.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.21/1.05  
% 4.21/1.05  fof(f26,plain,(
% 4.21/1.05    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.21/1.05    inference(ennf_transformation,[],[f7])).
% 4.21/1.05  
% 4.21/1.05  fof(f27,plain,(
% 4.21/1.05    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.21/1.05    inference(flattening,[],[f26])).
% 4.21/1.05  
% 4.21/1.05  fof(f58,plain,(
% 4.21/1.05    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.21/1.05    inference(cnf_transformation,[],[f27])).
% 4.21/1.05  
% 4.21/1.05  cnf(c_0,plain,
% 4.21/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f49]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2066,plain,
% 4.21/1.05      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_6,plain,
% 4.21/1.05      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 4.21/1.05      inference(cnf_transformation,[],[f55]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2062,plain,
% 4.21/1.05      ( v1_xboole_0(X0) != iProver_top
% 4.21/1.05      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_1,plain,
% 4.21/1.05      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 4.21/1.05      inference(cnf_transformation,[],[f50]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2065,plain,
% 4.21/1.05      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2467,plain,
% 4.21/1.05      ( k2_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_2062,c_2065]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2568,plain,
% 4.21/1.05      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_2066,c_2467]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_21,plain,
% 4.21/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 4.21/1.05      | ~ v1_funct_1(X0)
% 4.21/1.05      | ~ v1_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f72]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2051,plain,
% 4.21/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top
% 4.21/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_3903,plain,
% 4.21/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
% 4.21/1.05      | v1_funct_1(k1_xboole_0) != iProver_top
% 4.21/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_2568,c_2051]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_17,plain,
% 4.21/1.05      ( v1_relat_1(k1_xboole_0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f65]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_63,plain,
% 4.21/1.05      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_16,plain,
% 4.21/1.05      ( v1_funct_1(k1_xboole_0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f66]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_64,plain,
% 4.21/1.05      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_6318,plain,
% 4.21/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top ),
% 4.21/1.05      inference(global_propositional_subsumption,
% 4.21/1.05                [status(thm)],
% 4.21/1.05                [c_3903,c_63,c_64]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_10,plain,
% 4.21/1.05      ( ~ v1_relat_1(X0)
% 4.21/1.05      | k2_relat_1(X0) != k1_xboole_0
% 4.21/1.05      | k1_relat_1(X0) = k1_xboole_0 ),
% 4.21/1.05      inference(cnf_transformation,[],[f60]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2059,plain,
% 4.21/1.05      ( k2_relat_1(X0) != k1_xboole_0
% 4.21/1.05      | k1_relat_1(X0) = k1_xboole_0
% 4.21/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_3400,plain,
% 4.21/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 4.21/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_2568,c_2059]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_81,plain,
% 4.21/1.05      ( ~ v1_relat_1(k1_xboole_0)
% 4.21/1.05      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 4.21/1.05      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.21/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_108,plain,
% 4.21/1.05      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2470,plain,
% 4.21/1.05      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 4.21/1.05      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.21/1.05      inference(instantiation,[status(thm)],[c_2467]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_4388,plain,
% 4.21/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.21/1.05      inference(global_propositional_subsumption,
% 4.21/1.05                [status(thm)],
% 4.21/1.05                [c_3400,c_17,c_81,c_108,c_2470]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_6322,plain,
% 4.21/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 4.21/1.05      inference(light_normalisation,[status(thm)],[c_6318,c_4388]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_26,plain,
% 4.21/1.05      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 4.21/1.05      | v1_funct_2(X0,k1_xboole_0,X2)
% 4.21/1.05      | ~ r1_tarski(X1,X2)
% 4.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.21/1.05      | ~ v1_funct_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f86]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2047,plain,
% 4.21/1.05      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 4.21/1.05      | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
% 4.21/1.05      | r1_tarski(X1,X2) != iProver_top
% 4.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_6329,plain,
% 4.21/1.05      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 4.21/1.05      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 4.21/1.05      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 4.21/1.05      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_6322,c_2047]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_5,plain,
% 4.21/1.05      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f53]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_7,plain,
% 4.21/1.05      ( v4_relat_1(k1_xboole_0,X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f56]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_470,plain,
% 4.21/1.05      ( r1_tarski(k1_relat_1(X0),X1)
% 4.21/1.05      | ~ v1_relat_1(X0)
% 4.21/1.05      | X2 != X1
% 4.21/1.05      | k1_xboole_0 != X0 ),
% 4.21/1.05      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_471,plain,
% 4.21/1.05      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~ v1_relat_1(k1_xboole_0) ),
% 4.21/1.05      inference(unflattening,[status(thm)],[c_470]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_475,plain,
% 4.21/1.05      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
% 4.21/1.05      inference(global_propositional_subsumption,[status(thm)],[c_471,c_17]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2038,plain,
% 4.21/1.05      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_4391,plain,
% 4.21/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.21/1.05      inference(demodulation,[status(thm)],[c_4388,c_2038]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_22,plain,
% 4.21/1.05      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 4.21/1.05      | ~ v1_funct_1(X0)
% 4.21/1.05      | ~ v1_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f71]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2050,plain,
% 4.21/1.05      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top
% 4.21/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_4396,plain,
% 4.21/1.05      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0)) = iProver_top
% 4.21/1.05      | v1_funct_1(k1_xboole_0) != iProver_top
% 4.21/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_4388,c_2050]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_4399,plain,
% 4.21/1.05      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 4.21/1.05      | v1_funct_1(k1_xboole_0) != iProver_top
% 4.21/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.21/1.05      inference(light_normalisation,[status(thm)],[c_4396,c_2568]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_9593,plain,
% 4.21/1.05      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 4.21/1.05      inference(global_propositional_subsumption,
% 4.21/1.05                [status(thm)],
% 4.21/1.05                [c_6329,c_63,c_64,c_4391,c_4399]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_24,plain,
% 4.21/1.05      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 4.21/1.05      | ~ r1_tarski(X1,X2)
% 4.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 4.21/1.05      | ~ v1_funct_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f85]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2049,plain,
% 4.21/1.05      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 4.21/1.05      | r1_tarski(X1,X2) != iProver_top
% 4.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 4.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) = iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_6328,plain,
% 4.21/1.05      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 4.21/1.05      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 4.21/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 4.21/1.05      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_6322,c_2049]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_10062,plain,
% 4.21/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 4.21/1.05      inference(global_propositional_subsumption,
% 4.21/1.05                [status(thm)],
% 4.21/1.05                [c_6328,c_63,c_64,c_4391,c_4399]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_33,negated_conjecture,
% 4.21/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 4.21/1.05      inference(cnf_transformation,[],[f81]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2044,plain,
% 4.21/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_20,plain,
% 4.21/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f69]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2052,plain,
% 4.21/1.05      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.21/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_3407,plain,
% 4.21/1.05      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_2044,c_2052]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_31,negated_conjecture,
% 4.21/1.05      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 4.21/1.05      inference(cnf_transformation,[],[f83]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_3408,plain,
% 4.21/1.05      ( k2_relat_1(sK2) = sK1 ),
% 4.21/1.05      inference(light_normalisation,[status(thm)],[c_3407,c_31]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_15,plain,
% 4.21/1.05      ( ~ v2_funct_1(X0)
% 4.21/1.05      | ~ v1_funct_1(X0)
% 4.21/1.05      | ~ v1_relat_1(X0)
% 4.21/1.05      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f63]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_32,negated_conjecture,
% 4.21/1.05      ( v2_funct_1(sK2) ),
% 4.21/1.05      inference(cnf_transformation,[],[f82]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_418,plain,
% 4.21/1.05      ( ~ v1_funct_1(X0)
% 4.21/1.05      | ~ v1_relat_1(X0)
% 4.21/1.05      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 4.21/1.05      | sK2 != X0 ),
% 4.21/1.05      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_419,plain,
% 4.21/1.05      ( ~ v1_funct_1(sK2)
% 4.21/1.05      | ~ v1_relat_1(sK2)
% 4.21/1.05      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 4.21/1.05      inference(unflattening,[status(thm)],[c_418]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_35,negated_conjecture,
% 4.21/1.05      ( v1_funct_1(sK2) ),
% 4.21/1.05      inference(cnf_transformation,[],[f79]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_421,plain,
% 4.21/1.05      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 4.21/1.05      inference(global_propositional_subsumption,[status(thm)],[c_419,c_35]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2041,plain,
% 4.21/1.05      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 4.21/1.05      | v1_relat_1(sK2) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_18,plain,
% 4.21/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f67]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2115,plain,
% 4.21/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK2) ),
% 4.21/1.05      inference(instantiation,[status(thm)],[c_18]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2134,plain,
% 4.21/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.21/1.05      | v1_relat_1(sK2) ),
% 4.21/1.05      inference(instantiation,[status(thm)],[c_2115]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2266,plain,
% 4.21/1.05      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 4.21/1.05      inference(global_propositional_subsumption,
% 4.21/1.05                [status(thm)],
% 4.21/1.05                [c_2041,c_35,c_33,c_419,c_2134]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_3463,plain,
% 4.21/1.05      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 4.21/1.05      inference(demodulation,[status(thm)],[c_3408,c_2266]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_27,plain,
% 4.21/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 4.21/1.05      | v1_funct_2(X0,X1,X3)
% 4.21/1.05      | ~ r1_tarski(X2,X3)
% 4.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.05      | ~ v1_funct_1(X0)
% 4.21/1.05      | k1_xboole_0 = X2 ),
% 4.21/1.05      inference(cnf_transformation,[],[f75]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2046,plain,
% 4.21/1.05      ( k1_xboole_0 = X0
% 4.21/1.05      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.21/1.05      | v1_funct_2(X1,X2,X3) = iProver_top
% 4.21/1.05      | r1_tarski(X0,X3) != iProver_top
% 4.21/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.21/1.05      | v1_funct_1(X1) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_3911,plain,
% 4.21/1.05      ( k2_relat_1(X0) = k1_xboole_0
% 4.21/1.05      | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 4.21/1.05      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 4.21/1.05      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top
% 4.21/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_2051,c_2046]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_48,plain,
% 4.21/1.05      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top
% 4.21/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_8614,plain,
% 4.21/1.05      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 4.21/1.05      | k2_relat_1(X0) = k1_xboole_0
% 4.21/1.05      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top
% 4.21/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.05      inference(global_propositional_subsumption,[status(thm)],[c_3911,c_48]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_8615,plain,
% 4.21/1.05      ( k2_relat_1(X0) = k1_xboole_0
% 4.21/1.05      | v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 4.21/1.05      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.21/1.05      | v1_funct_1(X0) != iProver_top
% 4.21/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.05      inference(renaming,[status(thm)],[c_8614]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_8619,plain,
% 4.21/1.05      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 4.21/1.05      | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
% 4.21/1.05      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 4.21/1.05      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.05      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.05      inference(superposition,[status(thm)],[c_3463,c_8615]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_14,plain,
% 4.21/1.05      ( ~ v2_funct_1(X0)
% 4.21/1.05      | ~ v1_funct_1(X0)
% 4.21/1.05      | ~ v1_relat_1(X0)
% 4.21/1.05      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f64]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_432,plain,
% 4.21/1.05      ( ~ v1_funct_1(X0)
% 4.21/1.05      | ~ v1_relat_1(X0)
% 4.21/1.05      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 4.21/1.05      | sK2 != X0 ),
% 4.21/1.05      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_433,plain,
% 4.21/1.05      ( ~ v1_funct_1(sK2)
% 4.21/1.05      | ~ v1_relat_1(sK2)
% 4.21/1.05      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 4.21/1.05      inference(unflattening,[status(thm)],[c_432]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_435,plain,
% 4.21/1.05      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 4.21/1.05      inference(global_propositional_subsumption,[status(thm)],[c_433,c_35]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2040,plain,
% 4.21/1.05      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 4.21/1.05      | v1_relat_1(sK2) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2227,plain,
% 4.21/1.05      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 4.21/1.05      inference(global_propositional_subsumption,
% 4.21/1.05                [status(thm)],
% 4.21/1.05                [c_2040,c_35,c_33,c_433,c_2134]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_8620,plain,
% 4.21/1.05      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 4.21/1.05      | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
% 4.21/1.05      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.21/1.05      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.05      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.05      inference(light_normalisation,[status(thm)],[c_8619,c_2227]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_8621,plain,
% 4.21/1.05      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.05      | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
% 4.21/1.05      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.21/1.05      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.05      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.05      inference(demodulation,[status(thm)],[c_8620,c_2227]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_36,plain,
% 4.21/1.05      ( v1_funct_1(sK2) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_38,plain,
% 4.21/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_12,plain,
% 4.21/1.05      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 4.21/1.05      inference(cnf_transformation,[],[f62]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2102,plain,
% 4.21/1.05      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 4.21/1.05      inference(instantiation,[status(thm)],[c_12]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2103,plain,
% 4.21/1.05      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 4.21/1.05      | v1_funct_1(sK2) != iProver_top
% 4.21/1.05      | v1_relat_1(sK2) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_2102]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2135,plain,
% 4.21/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.21/1.05      | v1_relat_1(sK2) = iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_2134]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_13,plain,
% 4.21/1.05      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 4.21/1.05      inference(cnf_transformation,[],[f61]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2400,plain,
% 4.21/1.05      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 4.21/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_2401,plain,
% 4.21/1.05      ( v1_funct_1(sK2) != iProver_top
% 4.21/1.05      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 4.21/1.05      | v1_relat_1(sK2) != iProver_top ),
% 4.21/1.05      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 4.21/1.05  
% 4.21/1.05  cnf(c_3895,plain,
% 4.21/1.05      ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_2227,c_2050]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3896,plain,
% 4.21/1.06      ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(light_normalisation,[status(thm)],[c_3895,c_3463]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3905,plain,
% 4.21/1.06      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_2227,c_2051]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3912,plain,
% 4.21/1.06      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(light_normalisation,[status(thm)],[c_3905,c_3463]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_4581,plain,
% 4.21/1.06      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 4.21/1.06      inference(global_propositional_subsumption,
% 4.21/1.06                [status(thm)],
% 4.21/1.06                [c_3912,c_36,c_38,c_2103,c_2135,c_2401]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_4590,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
% 4.21/1.06      | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_4581,c_2046]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8929,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | v1_funct_2(k2_funct_1(sK2),sK1,X0) = iProver_top
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 4.21/1.06      inference(global_propositional_subsumption,
% 4.21/1.06                [status(thm)],
% 4.21/1.06                [c_8621,c_36,c_38,c_2103,c_2135,c_2401,c_3896,c_4590]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_25,plain,
% 4.21/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 4.21/1.06      | ~ r1_tarski(X2,X3)
% 4.21/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 4.21/1.06      | ~ v1_funct_1(X0)
% 4.21/1.06      | k1_xboole_0 = X2 ),
% 4.21/1.06      inference(cnf_transformation,[],[f77]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2048,plain,
% 4.21/1.06      ( k1_xboole_0 = X0
% 4.21/1.06      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.21/1.06      | r1_tarski(X0,X3) != iProver_top
% 4.21/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.21/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 4.21/1.06      | v1_funct_1(X1) != iProver_top ),
% 4.21/1.06      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3910,plain,
% 4.21/1.06      ( k2_relat_1(X0) = k1_xboole_0
% 4.21/1.06      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 4.21/1.06      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.21/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 4.21/1.06      | v1_funct_1(X0) != iProver_top
% 4.21/1.06      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_2051,c_2048]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_7520,plain,
% 4.21/1.06      ( k2_relat_1(X0) = k1_xboole_0
% 4.21/1.06      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 4.21/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 4.21/1.06      | v1_funct_1(X0) != iProver_top
% 4.21/1.06      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.06      inference(global_propositional_subsumption,[status(thm)],[c_3910,c_48]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_7525,plain,
% 4.21/1.06      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 4.21/1.06      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_3463,c_7520]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_7532,plain,
% 4.21/1.06      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(light_normalisation,[status(thm)],[c_7525,c_2227]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_7533,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(demodulation,[status(thm)],[c_7532,c_2227]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_4589,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) != iProver_top
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_4581,c_2048]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8156,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
% 4.21/1.06      inference(global_propositional_subsumption,
% 4.21/1.06                [status(thm)],
% 4.21/1.06                [c_7533,c_36,c_38,c_2103,c_2135,c_2401,c_3896,c_4589]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_30,negated_conjecture,
% 4.21/1.06      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 4.21/1.06      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.21/1.06      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 4.21/1.06      inference(cnf_transformation,[],[f84]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2045,plain,
% 4.21/1.06      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_40,plain,
% 4.21/1.06      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.21/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2222,plain,
% 4.21/1.06      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.21/1.06      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 4.21/1.06      inference(global_propositional_subsumption,
% 4.21/1.06                [status(thm)],
% 4.21/1.06                [c_2045,c_36,c_38,c_40,c_2103,c_2135]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2223,plain,
% 4.21/1.06      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 4.21/1.06      inference(renaming,[status(thm)],[c_2222]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8166,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_8156,c_2223]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_19,plain,
% 4.21/1.06      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.21/1.06      inference(cnf_transformation,[],[f68]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_452,plain,
% 4.21/1.06      ( r1_tarski(k1_relat_1(X0),X1)
% 4.21/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.06      | ~ v1_relat_1(X0) ),
% 4.21/1.06      inference(resolution,[status(thm)],[c_19,c_5]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_456,plain,
% 4.21/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.06      | r1_tarski(k1_relat_1(X0),X1) ),
% 4.21/1.06      inference(global_propositional_subsumption,
% 4.21/1.06                [status(thm)],
% 4.21/1.06                [c_452,c_19,c_18,c_5]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_457,plain,
% 4.21/1.06      ( r1_tarski(k1_relat_1(X0),X1)
% 4.21/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.21/1.06      inference(renaming,[status(thm)],[c_456]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2039,plain,
% 4.21/1.06      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 4.21/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 4.21/1.06      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2340,plain,
% 4.21/1.06      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_2044,c_2039]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8181,plain,
% 4.21/1.06      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 4.21/1.06      | k1_relat_1(sK2) = k1_xboole_0 ),
% 4.21/1.06      inference(global_propositional_subsumption,[status(thm)],[c_8166,c_2340]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8182,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 4.21/1.06      inference(renaming,[status(thm)],[c_8181]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8935,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_8929,c_8182]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8938,plain,
% 4.21/1.06      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 4.21/1.06      inference(global_propositional_subsumption,[status(thm)],[c_8935,c_2340]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3401,plain,
% 4.21/1.06      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 4.21/1.06      | k1_relat_1(sK2) != k1_xboole_0
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_2227,c_2059]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3402,plain,
% 4.21/1.06      ( k2_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | k1_relat_1(sK2) != k1_xboole_0
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(demodulation,[status(thm)],[c_3401,c_2266]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_11,plain,
% 4.21/1.06      ( ~ v1_relat_1(X0)
% 4.21/1.06      | k2_relat_1(X0) = k1_xboole_0
% 4.21/1.06      | k1_relat_1(X0) != k1_xboole_0 ),
% 4.21/1.06      inference(cnf_transformation,[],[f59]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2537,plain,
% 4.21/1.06      ( ~ v1_relat_1(sK2)
% 4.21/1.06      | k2_relat_1(sK2) = k1_xboole_0
% 4.21/1.06      | k1_relat_1(sK2) != k1_xboole_0 ),
% 4.21/1.06      inference(instantiation,[status(thm)],[c_11]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_4523,plain,
% 4.21/1.06      ( k1_relat_1(sK2) != k1_xboole_0 | k2_relat_1(sK2) = k1_xboole_0 ),
% 4.21/1.06      inference(global_propositional_subsumption,
% 4.21/1.06                [status(thm)],
% 4.21/1.06                [c_3402,c_33,c_2134,c_2537]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_4524,plain,
% 4.21/1.06      ( k2_relat_1(sK2) = k1_xboole_0 | k1_relat_1(sK2) != k1_xboole_0 ),
% 4.21/1.06      inference(renaming,[status(thm)],[c_4523]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_4525,plain,
% 4.21/1.06      ( k1_relat_1(sK2) != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 4.21/1.06      inference(demodulation,[status(thm)],[c_4524,c_3408]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8972,plain,
% 4.21/1.06      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.21/1.06      inference(demodulation,[status(thm)],[c_8938,c_4525]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8984,plain,
% 4.21/1.06      ( sK1 = k1_xboole_0 ),
% 4.21/1.06      inference(equality_resolution_simp,[status(thm)],[c_8972]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_9147,plain,
% 4.21/1.06      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) != iProver_top
% 4.21/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 4.21/1.06      inference(demodulation,[status(thm)],[c_8984,c_2223]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8,plain,
% 4.21/1.06      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 4.21/1.06      inference(cnf_transformation,[],[f58]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_2061,plain,
% 4.21/1.06      ( k2_relat_1(X0) != k1_xboole_0
% 4.21/1.06      | k1_xboole_0 = X0
% 4.21/1.06      | v1_relat_1(X0) != iProver_top ),
% 4.21/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3343,plain,
% 4.21/1.06      ( k2_funct_1(sK2) = k1_xboole_0
% 4.21/1.06      | k1_relat_1(sK2) != k1_xboole_0
% 4.21/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_2227,c_2061]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3344,plain,
% 4.21/1.06      ( ~ v1_relat_1(k2_funct_1(sK2))
% 4.21/1.06      | k2_funct_1(sK2) = k1_xboole_0
% 4.21/1.06      | k1_relat_1(sK2) != k1_xboole_0 ),
% 4.21/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_3343]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3664,plain,
% 4.21/1.06      ( k1_relat_1(sK2) != k1_xboole_0 | k2_funct_1(sK2) = k1_xboole_0 ),
% 4.21/1.06      inference(global_propositional_subsumption,
% 4.21/1.06                [status(thm)],
% 4.21/1.06                [c_3343,c_35,c_33,c_2134,c_2400,c_3344]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_3665,plain,
% 4.21/1.06      ( k2_funct_1(sK2) = k1_xboole_0 | k1_relat_1(sK2) != k1_xboole_0 ),
% 4.21/1.06      inference(renaming,[status(thm)],[c_3664]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8978,plain,
% 4.21/1.06      ( k2_funct_1(sK2) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.21/1.06      inference(demodulation,[status(thm)],[c_8938,c_3665]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_8982,plain,
% 4.21/1.06      ( k2_funct_1(sK2) = k1_xboole_0 ),
% 4.21/1.06      inference(equality_resolution_simp,[status(thm)],[c_8978]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_9151,plain,
% 4.21/1.06      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) != iProver_top
% 4.21/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 4.21/1.06      inference(light_normalisation,[status(thm)],[c_9147,c_8982]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_10074,plain,
% 4.21/1.06      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) != iProver_top ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_10062,c_9151]) ).
% 4.21/1.06  
% 4.21/1.06  cnf(c_10226,plain,
% 4.21/1.06      ( $false ),
% 4.21/1.06      inference(superposition,[status(thm)],[c_9593,c_10074]) ).
% 4.21/1.06  
% 4.21/1.06  
% 4.21/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 4.21/1.06  
% 4.21/1.06  ------                               Statistics
% 4.21/1.06  
% 4.21/1.06  ------ General
% 4.21/1.06  
% 4.21/1.06  abstr_ref_over_cycles:                  0
% 4.21/1.06  abstr_ref_under_cycles:                 0
% 4.21/1.06  gc_basic_clause_elim:                   0
% 4.21/1.06  forced_gc_time:                         0
% 4.21/1.06  parsing_time:                           0.018
% 4.21/1.06  unif_index_cands_time:                  0.
% 4.21/1.06  unif_index_add_time:                    0.
% 4.21/1.06  orderings_time:                         0.
% 4.21/1.06  out_proof_time:                         0.039
% 4.21/1.06  total_time:                             0.513
% 4.21/1.06  num_of_symbols:                         49
% 4.21/1.06  num_of_terms:                           7614
% 4.21/1.06  
% 4.21/1.06  ------ Preprocessing
% 4.21/1.06  
% 4.21/1.06  num_of_splits:                          0
% 4.21/1.06  num_of_split_atoms:                     0
% 4.21/1.06  num_of_reused_defs:                     0
% 4.21/1.06  num_eq_ax_congr_red:                    4
% 4.21/1.06  num_of_sem_filtered_clauses:            1
% 4.21/1.06  num_of_subtypes:                        0
% 4.21/1.06  monotx_restored_types:                  0
% 4.21/1.06  sat_num_of_epr_types:                   0
% 4.21/1.06  sat_num_of_non_cyclic_types:            0
% 4.21/1.06  sat_guarded_non_collapsed_types:        0
% 4.21/1.06  num_pure_diseq_elim:                    0
% 4.21/1.06  simp_replaced_by:                       0
% 4.21/1.06  res_preprocessed:                       152
% 4.21/1.06  prep_upred:                             0
% 4.21/1.06  prep_unflattend:                        60
% 4.21/1.06  smt_new_axioms:                         0
% 4.21/1.06  pred_elim_cands:                        6
% 4.21/1.06  pred_elim:                              2
% 4.21/1.06  pred_elim_cl:                           3
% 4.21/1.06  pred_elim_cycles:                       4
% 4.21/1.06  merged_defs:                            8
% 4.21/1.06  merged_defs_ncl:                        0
% 4.21/1.06  bin_hyper_res:                          8
% 4.21/1.06  prep_cycles:                            4
% 4.21/1.06  pred_elim_time:                         0.013
% 4.21/1.06  splitting_time:                         0.
% 4.21/1.06  sem_filter_time:                        0.
% 4.21/1.06  monotx_time:                            0.
% 4.21/1.06  subtype_inf_time:                       0.
% 4.21/1.06  
% 4.21/1.06  ------ Problem properties
% 4.21/1.06  
% 4.21/1.06  clauses:                                30
% 4.21/1.06  conjectures:                            5
% 4.21/1.06  epr:                                    6
% 4.21/1.06  horn:                                   28
% 4.21/1.06  ground:                                 10
% 4.21/1.06  unary:                                  8
% 4.21/1.06  binary:                                 9
% 4.21/1.06  lits:                                   75
% 4.21/1.06  lits_eq:                                15
% 4.21/1.06  fd_pure:                                0
% 4.21/1.06  fd_pseudo:                              0
% 4.21/1.06  fd_cond:                                5
% 4.21/1.06  fd_pseudo_cond:                         0
% 4.21/1.06  ac_symbols:                             0
% 4.21/1.06  
% 4.21/1.06  ------ Propositional Solver
% 4.21/1.06  
% 4.21/1.06  prop_solver_calls:                      37
% 4.21/1.06  prop_fast_solver_calls:                 1524
% 4.21/1.06  smt_solver_calls:                       0
% 4.21/1.06  smt_fast_solver_calls:                  0
% 4.21/1.06  prop_num_of_clauses:                    4208
% 4.21/1.06  prop_preprocess_simplified:             9383
% 4.21/1.06  prop_fo_subsumed:                       74
% 4.21/1.06  prop_solver_time:                       0.
% 4.21/1.06  smt_solver_time:                        0.
% 4.21/1.06  smt_fast_solver_time:                   0.
% 4.21/1.06  prop_fast_solver_time:                  0.
% 4.21/1.06  prop_unsat_core_time:                   0.
% 4.21/1.06  
% 4.21/1.06  ------ QBF
% 4.21/1.06  
% 4.21/1.06  qbf_q_res:                              0
% 4.21/1.06  qbf_num_tautologies:                    0
% 4.21/1.06  qbf_prep_cycles:                        0
% 4.21/1.06  
% 4.21/1.06  ------ BMC1
% 4.21/1.06  
% 4.21/1.06  bmc1_current_bound:                     -1
% 4.21/1.06  bmc1_last_solved_bound:                 -1
% 4.21/1.06  bmc1_unsat_core_size:                   -1
% 4.21/1.06  bmc1_unsat_core_parents_size:           -1
% 4.21/1.06  bmc1_merge_next_fun:                    0
% 4.21/1.06  bmc1_unsat_core_clauses_time:           0.
% 4.21/1.06  
% 4.21/1.06  ------ Instantiation
% 4.21/1.06  
% 4.21/1.06  inst_num_of_clauses:                    1325
% 4.21/1.06  inst_num_in_passive:                    547
% 4.21/1.06  inst_num_in_active:                     558
% 4.21/1.06  inst_num_in_unprocessed:                220
% 4.21/1.06  inst_num_of_loops:                      790
% 4.21/1.06  inst_num_of_learning_restarts:          0
% 4.21/1.06  inst_num_moves_active_passive:          223
% 4.21/1.06  inst_lit_activity:                      0
% 4.21/1.06  inst_lit_activity_moves:                0
% 4.21/1.06  inst_num_tautologies:                   0
% 4.21/1.06  inst_num_prop_implied:                  0
% 4.21/1.06  inst_num_existing_simplified:           0
% 4.21/1.06  inst_num_eq_res_simplified:             0
% 4.21/1.06  inst_num_child_elim:                    0
% 4.21/1.06  inst_num_of_dismatching_blockings:      430
% 4.21/1.06  inst_num_of_non_proper_insts:           1558
% 4.21/1.06  inst_num_of_duplicates:                 0
% 4.21/1.06  inst_inst_num_from_inst_to_res:         0
% 4.21/1.06  inst_dismatching_checking_time:         0.
% 4.21/1.06  
% 4.21/1.06  ------ Resolution
% 4.21/1.06  
% 4.21/1.06  res_num_of_clauses:                     0
% 4.21/1.06  res_num_in_passive:                     0
% 4.21/1.06  res_num_in_active:                      0
% 4.21/1.06  res_num_of_loops:                       156
% 4.21/1.06  res_forward_subset_subsumed:            81
% 4.21/1.06  res_backward_subset_subsumed:           2
% 4.21/1.06  res_forward_subsumed:                   0
% 4.21/1.06  res_backward_subsumed:                  0
% 4.21/1.06  res_forward_subsumption_resolution:     0
% 4.21/1.06  res_backward_subsumption_resolution:    0
% 4.21/1.06  res_clause_to_clause_subsumption:       1063
% 4.21/1.06  res_orphan_elimination:                 0
% 4.21/1.06  res_tautology_del:                      303
% 4.21/1.06  res_num_eq_res_simplified:              0
% 4.21/1.06  res_num_sel_changes:                    0
% 4.21/1.06  res_moves_from_active_to_pass:          0
% 4.21/1.06  
% 4.21/1.06  ------ Superposition
% 4.21/1.06  
% 4.21/1.06  sup_time_total:                         0.
% 4.21/1.06  sup_time_generating:                    0.
% 4.21/1.06  sup_time_sim_full:                      0.
% 4.21/1.06  sup_time_sim_immed:                     0.
% 4.21/1.06  
% 4.21/1.06  sup_num_of_clauses:                     102
% 4.21/1.06  sup_num_in_active:                      66
% 4.21/1.06  sup_num_in_passive:                     36
% 4.21/1.06  sup_num_of_loops:                       157
% 4.21/1.06  sup_fw_superposition:                   124
% 4.21/1.06  sup_bw_superposition:                   231
% 4.21/1.06  sup_immediate_simplified:               163
% 4.21/1.06  sup_given_eliminated:                   0
% 4.21/1.06  comparisons_done:                       0
% 4.21/1.06  comparisons_avoided:                    24
% 4.21/1.06  
% 4.21/1.06  ------ Simplifications
% 4.21/1.06  
% 4.21/1.06  
% 4.21/1.06  sim_fw_subset_subsumed:                 59
% 4.21/1.06  sim_bw_subset_subsumed:                 45
% 4.21/1.06  sim_fw_subsumed:                        14
% 4.21/1.06  sim_bw_subsumed:                        3
% 4.21/1.06  sim_fw_subsumption_res:                 0
% 4.21/1.06  sim_bw_subsumption_res:                 0
% 4.21/1.06  sim_tautology_del:                      4
% 4.21/1.06  sim_eq_tautology_del:                   43
% 4.21/1.06  sim_eq_res_simp:                        3
% 4.21/1.06  sim_fw_demodulated:                     29
% 4.21/1.06  sim_bw_demodulated:                     86
% 4.21/1.06  sim_light_normalised:                   68
% 4.21/1.06  sim_joinable_taut:                      0
% 4.21/1.06  sim_joinable_simp:                      0
% 4.21/1.06  sim_ac_normalised:                      0
% 4.21/1.06  sim_smt_subsumption:                    0
% 4.21/1.06  
%------------------------------------------------------------------------------
