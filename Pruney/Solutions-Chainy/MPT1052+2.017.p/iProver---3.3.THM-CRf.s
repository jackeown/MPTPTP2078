%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:57 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  208 (4423 expanded)
%              Number of clauses        :  136 (1490 expanded)
%              Number of leaves         :   26 ( 867 expanded)
%              Depth                    :   26
%              Number of atoms          :  579 (13731 expanded)
%              Number of equality atoms :  347 (5888 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
        | k1_relat_1(sK3) != sK1 )
      & r2_hidden(sK3,k1_funct_2(sK1,sK2))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
      | k1_relat_1(sK3) != sK1 )
    & r2_hidden(sK3,k1_funct_2(sK1,sK2))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42])).

fof(f74,plain,(
    r2_hidden(sK3,k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f74,f72])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f70,f72])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1846,plain,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1848])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1854,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3321,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3110,c_1854])).

cnf(c_12,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1852,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3819,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1852])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_70,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5297,plain,
    ( v1_relat_1(X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3819,c_70])).

cnf(c_5298,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5297])).

cnf(c_5307,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_5298])).

cnf(c_30,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_27,c_24])).

cnf(c_412,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_26,c_24])).

cnf(c_416,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_27])).

cnf(c_713,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_709,c_27,c_412])).

cnf(c_1844,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_3009,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1846,c_1844])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1850,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3322,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3110,c_1850])).

cnf(c_3456,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3009,c_3322])).

cnf(c_28,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1847,plain,
    ( k1_relat_1(sK3) != sK1
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3596,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3456,c_1847])).

cnf(c_3627,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3596])).

cnf(c_5323,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5307])).

cnf(c_5651,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5307,c_30,c_3627,c_5323])).

cnf(c_5663,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5651,c_3321])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5689,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5663,c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1856,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5968,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5689,c_1856])).

cnf(c_1316,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2082,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relat_1(sK3) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_2166,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relat_1(sK3) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_2168,plain,
    ( k2_relat_1(sK3) != X0
    | sK2 != sK2
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2166])).

cnf(c_2170,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK2 != sK2
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2168])).

cnf(c_1312,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2167,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2407,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2410,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2407])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3820,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1852])).

cnf(c_72,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_79,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_80,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1320,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2031,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_2032,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_2034,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_1313,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2202,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2203,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_3945,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3820,c_72,c_79,c_80,c_2034,c_2203])).

cnf(c_3946,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3945])).

cnf(c_3954,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_1856])).

cnf(c_5966,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5689,c_3954])).

cnf(c_6056,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5966])).

cnf(c_6263,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5968,c_30,c_2170,c_2167,c_2410,c_3596,c_6056])).

cnf(c_6277,plain,
    ( r2_hidden(sK3,k5_partfun1(sK1,k1_xboole_0,k3_partfun1(k1_xboole_0,sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6263,c_1846])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r2_hidden(X2,k5_partfun1(X3,X4,k3_partfun1(k1_xboole_0,X3,X4)))
    | X2 != X0
    | X3 != X1
    | k1_xboole_0 != X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_749,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_737,c_26])).

cnf(c_1843,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_6424,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6277,c_1843])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_90,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_390,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) != k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_391,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_393,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_2114,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2160,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(c_2926,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_2927,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2926])).

cnf(c_2437,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_3065,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_3066,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3065])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3185,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3186,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3185])).

cnf(c_2247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3474,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2247])).

cnf(c_3477,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_2321,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_2981,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2321])).

cnf(c_4695,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_4698,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4695])).

cnf(c_1325,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
    theory(equality)).

cnf(c_2393,plain,
    ( X0 != k3_partfun1(k1_xboole_0,sK1,sK2)
    | X1 != sK1
    | X2 != sK2
    | k5_partfun1(X1,X2,X0) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_3175,plain,
    ( X0 != k3_partfun1(k1_xboole_0,sK1,sK2)
    | X1 != sK2
    | k5_partfun1(k1_xboole_0,X1,X0) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2393])).

cnf(c_5265,plain,
    ( X0 != sK2
    | k5_partfun1(k1_xboole_0,X0,k3_partfun1(X1,X2,X3)) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
    | k3_partfun1(X1,X2,X3) != k3_partfun1(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_3175])).

cnf(c_5267,plain,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
    | k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_partfun1(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5265])).

cnf(c_1324,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k3_partfun1(X0,X2,X4) = k3_partfun1(X1,X3,X5) ),
    theory(equality)).

cnf(c_5266,plain,
    ( X0 != sK1
    | X1 != sK2
    | X2 != k1_xboole_0
    | k3_partfun1(X2,X0,X1) = k3_partfun1(k1_xboole_0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_5268,plain,
    ( k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k3_partfun1(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5266])).

cnf(c_25,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1849,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1860,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2500,plain,
    ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1860])).

cnf(c_3207,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_2500])).

cnf(c_6270,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6263,c_3207])).

cnf(c_6582,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6424,c_30,c_79,c_80,c_90,c_393,c_2114,c_2160,c_2170,c_2167,c_2203,c_2410,c_2927,c_3066,c_3186,c_3477,c_3596,c_4698,c_5267,c_5268,c_6056,c_6270])).

cnf(c_6276,plain,
    ( k1_relat_1(sK3) != sK1
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6263,c_1847])).

cnf(c_71,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_85,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2033,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_1321,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_2575,plain,
    ( k2_relat_1(sK3) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_2580,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2575])).

cnf(c_3859,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3820])).

cnf(c_3861,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3859])).

cnf(c_4421,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relat_1(sK3) != k2_relat_1(X0)
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_4434,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k2_relat_1(sK3) != k2_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4421])).

cnf(c_6435,plain,
    ( k1_relat_1(sK3) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6276,c_30,c_28,c_71,c_79,c_80,c_85,c_90,c_393,c_2033,c_2114,c_2160,c_2170,c_2167,c_2203,c_2410,c_2580,c_2927,c_3066,c_3186,c_3477,c_3596,c_3861,c_4434,c_4698,c_5267,c_5268,c_6056,c_6270])).

cnf(c_6585,plain,
    ( k1_relat_1(k1_xboole_0) != sK1 ),
    inference(demodulation,[status(thm)],[c_6582,c_6435])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6592,plain,
    ( sK1 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6585,c_17])).

cnf(c_3160,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_6346,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3160])).

cnf(c_6347,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_6346])).

cnf(c_3158,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6592,c_6347,c_6270,c_3186,c_3158,c_90])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.59/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.99  
% 2.59/0.99  ------  iProver source info
% 2.59/0.99  
% 2.59/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.99  git: non_committed_changes: false
% 2.59/0.99  git: last_make_outside_of_git: false
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     num_symb
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       true
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  ------ Parsing...
% 2.59/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.99  ------ Proving...
% 2.59/0.99  ------ Problem Properties 
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  clauses                                 27
% 2.59/0.99  conjectures                             3
% 2.59/0.99  EPR                                     6
% 2.59/0.99  Horn                                    20
% 2.59/0.99  unary                                   9
% 2.59/0.99  binary                                  10
% 2.59/0.99  lits                                    55
% 2.59/0.99  lits eq                                 22
% 2.59/0.99  fd_pure                                 0
% 2.59/0.99  fd_pseudo                               0
% 2.59/0.99  fd_cond                                 4
% 2.59/0.99  fd_pseudo_cond                          0
% 2.59/0.99  AC symbols                              0
% 2.59/0.99  
% 2.59/0.99  ------ Schedule dynamic 5 is on 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ 
% 2.59/0.99  Current options:
% 2.59/0.99  ------ 
% 2.59/0.99  
% 2.59/0.99  ------ Input Options
% 2.59/0.99  
% 2.59/0.99  --out_options                           all
% 2.59/0.99  --tptp_safe_out                         true
% 2.59/0.99  --problem_path                          ""
% 2.59/0.99  --include_path                          ""
% 2.59/0.99  --clausifier                            res/vclausify_rel
% 2.59/0.99  --clausifier_options                    --mode clausify
% 2.59/0.99  --stdin                                 false
% 2.59/0.99  --stats_out                             all
% 2.59/0.99  
% 2.59/0.99  ------ General Options
% 2.59/0.99  
% 2.59/0.99  --fof                                   false
% 2.59/0.99  --time_out_real                         305.
% 2.59/0.99  --time_out_virtual                      -1.
% 2.59/0.99  --symbol_type_check                     false
% 2.59/0.99  --clausify_out                          false
% 2.59/0.99  --sig_cnt_out                           false
% 2.59/0.99  --trig_cnt_out                          false
% 2.59/0.99  --trig_cnt_out_tolerance                1.
% 2.59/0.99  --trig_cnt_out_sk_spl                   false
% 2.59/0.99  --abstr_cl_out                          false
% 2.59/0.99  
% 2.59/0.99  ------ Global Options
% 2.59/0.99  
% 2.59/0.99  --schedule                              default
% 2.59/0.99  --add_important_lit                     false
% 2.59/0.99  --prop_solver_per_cl                    1000
% 2.59/0.99  --min_unsat_core                        false
% 2.59/0.99  --soft_assumptions                      false
% 2.59/0.99  --soft_lemma_size                       3
% 2.59/0.99  --prop_impl_unit_size                   0
% 2.59/0.99  --prop_impl_unit                        []
% 2.59/0.99  --share_sel_clauses                     true
% 2.59/0.99  --reset_solvers                         false
% 2.59/0.99  --bc_imp_inh                            [conj_cone]
% 2.59/0.99  --conj_cone_tolerance                   3.
% 2.59/0.99  --extra_neg_conj                        none
% 2.59/0.99  --large_theory_mode                     true
% 2.59/0.99  --prolific_symb_bound                   200
% 2.59/0.99  --lt_threshold                          2000
% 2.59/0.99  --clause_weak_htbl                      true
% 2.59/0.99  --gc_record_bc_elim                     false
% 2.59/0.99  
% 2.59/0.99  ------ Preprocessing Options
% 2.59/0.99  
% 2.59/0.99  --preprocessing_flag                    true
% 2.59/0.99  --time_out_prep_mult                    0.1
% 2.59/0.99  --splitting_mode                        input
% 2.59/0.99  --splitting_grd                         true
% 2.59/0.99  --splitting_cvd                         false
% 2.59/0.99  --splitting_cvd_svl                     false
% 2.59/0.99  --splitting_nvd                         32
% 2.59/0.99  --sub_typing                            true
% 2.59/0.99  --prep_gs_sim                           true
% 2.59/0.99  --prep_unflatten                        true
% 2.59/0.99  --prep_res_sim                          true
% 2.59/0.99  --prep_upred                            true
% 2.59/0.99  --prep_sem_filter                       exhaustive
% 2.59/0.99  --prep_sem_filter_out                   false
% 2.59/0.99  --pred_elim                             true
% 2.59/0.99  --res_sim_input                         true
% 2.59/0.99  --eq_ax_congr_red                       true
% 2.59/0.99  --pure_diseq_elim                       true
% 2.59/0.99  --brand_transform                       false
% 2.59/0.99  --non_eq_to_eq                          false
% 2.59/0.99  --prep_def_merge                        true
% 2.59/0.99  --prep_def_merge_prop_impl              false
% 2.59/0.99  --prep_def_merge_mbd                    true
% 2.59/0.99  --prep_def_merge_tr_red                 false
% 2.59/0.99  --prep_def_merge_tr_cl                  false
% 2.59/0.99  --smt_preprocessing                     true
% 2.59/0.99  --smt_ac_axioms                         fast
% 2.59/0.99  --preprocessed_out                      false
% 2.59/0.99  --preprocessed_stats                    false
% 2.59/0.99  
% 2.59/0.99  ------ Abstraction refinement Options
% 2.59/0.99  
% 2.59/0.99  --abstr_ref                             []
% 2.59/0.99  --abstr_ref_prep                        false
% 2.59/0.99  --abstr_ref_until_sat                   false
% 2.59/0.99  --abstr_ref_sig_restrict                funpre
% 2.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.99  --abstr_ref_under                       []
% 2.59/0.99  
% 2.59/0.99  ------ SAT Options
% 2.59/0.99  
% 2.59/0.99  --sat_mode                              false
% 2.59/0.99  --sat_fm_restart_options                ""
% 2.59/0.99  --sat_gr_def                            false
% 2.59/0.99  --sat_epr_types                         true
% 2.59/0.99  --sat_non_cyclic_types                  false
% 2.59/0.99  --sat_finite_models                     false
% 2.59/0.99  --sat_fm_lemmas                         false
% 2.59/0.99  --sat_fm_prep                           false
% 2.59/0.99  --sat_fm_uc_incr                        true
% 2.59/0.99  --sat_out_model                         small
% 2.59/0.99  --sat_out_clauses                       false
% 2.59/0.99  
% 2.59/0.99  ------ QBF Options
% 2.59/0.99  
% 2.59/0.99  --qbf_mode                              false
% 2.59/0.99  --qbf_elim_univ                         false
% 2.59/0.99  --qbf_dom_inst                          none
% 2.59/0.99  --qbf_dom_pre_inst                      false
% 2.59/0.99  --qbf_sk_in                             false
% 2.59/0.99  --qbf_pred_elim                         true
% 2.59/0.99  --qbf_split                             512
% 2.59/0.99  
% 2.59/0.99  ------ BMC1 Options
% 2.59/0.99  
% 2.59/0.99  --bmc1_incremental                      false
% 2.59/0.99  --bmc1_axioms                           reachable_all
% 2.59/0.99  --bmc1_min_bound                        0
% 2.59/0.99  --bmc1_max_bound                        -1
% 2.59/0.99  --bmc1_max_bound_default                -1
% 2.59/0.99  --bmc1_symbol_reachability              true
% 2.59/0.99  --bmc1_property_lemmas                  false
% 2.59/0.99  --bmc1_k_induction                      false
% 2.59/0.99  --bmc1_non_equiv_states                 false
% 2.59/0.99  --bmc1_deadlock                         false
% 2.59/0.99  --bmc1_ucm                              false
% 2.59/0.99  --bmc1_add_unsat_core                   none
% 2.59/0.99  --bmc1_unsat_core_children              false
% 2.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.99  --bmc1_out_stat                         full
% 2.59/0.99  --bmc1_ground_init                      false
% 2.59/0.99  --bmc1_pre_inst_next_state              false
% 2.59/0.99  --bmc1_pre_inst_state                   false
% 2.59/0.99  --bmc1_pre_inst_reach_state             false
% 2.59/0.99  --bmc1_out_unsat_core                   false
% 2.59/0.99  --bmc1_aig_witness_out                  false
% 2.59/0.99  --bmc1_verbose                          false
% 2.59/0.99  --bmc1_dump_clauses_tptp                false
% 2.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.99  --bmc1_dump_file                        -
% 2.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.99  --bmc1_ucm_extend_mode                  1
% 2.59/0.99  --bmc1_ucm_init_mode                    2
% 2.59/0.99  --bmc1_ucm_cone_mode                    none
% 2.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.99  --bmc1_ucm_relax_model                  4
% 2.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.99  --bmc1_ucm_layered_model                none
% 2.59/0.99  --bmc1_ucm_max_lemma_size               10
% 2.59/0.99  
% 2.59/0.99  ------ AIG Options
% 2.59/0.99  
% 2.59/0.99  --aig_mode                              false
% 2.59/0.99  
% 2.59/0.99  ------ Instantiation Options
% 2.59/0.99  
% 2.59/0.99  --instantiation_flag                    true
% 2.59/0.99  --inst_sos_flag                         false
% 2.59/0.99  --inst_sos_phase                        true
% 2.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.99  --inst_lit_sel_side                     none
% 2.59/0.99  --inst_solver_per_active                1400
% 2.59/0.99  --inst_solver_calls_frac                1.
% 2.59/0.99  --inst_passive_queue_type               priority_queues
% 2.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.99  --inst_passive_queues_freq              [25;2]
% 2.59/0.99  --inst_dismatching                      true
% 2.59/0.99  --inst_eager_unprocessed_to_passive     true
% 2.59/0.99  --inst_prop_sim_given                   true
% 2.59/0.99  --inst_prop_sim_new                     false
% 2.59/0.99  --inst_subs_new                         false
% 2.59/0.99  --inst_eq_res_simp                      false
% 2.59/0.99  --inst_subs_given                       false
% 2.59/0.99  --inst_orphan_elimination               true
% 2.59/0.99  --inst_learning_loop_flag               true
% 2.59/0.99  --inst_learning_start                   3000
% 2.59/0.99  --inst_learning_factor                  2
% 2.59/0.99  --inst_start_prop_sim_after_learn       3
% 2.59/0.99  --inst_sel_renew                        solver
% 2.59/0.99  --inst_lit_activity_flag                true
% 2.59/0.99  --inst_restr_to_given                   false
% 2.59/0.99  --inst_activity_threshold               500
% 2.59/0.99  --inst_out_proof                        true
% 2.59/0.99  
% 2.59/0.99  ------ Resolution Options
% 2.59/0.99  
% 2.59/0.99  --resolution_flag                       false
% 2.59/0.99  --res_lit_sel                           adaptive
% 2.59/0.99  --res_lit_sel_side                      none
% 2.59/0.99  --res_ordering                          kbo
% 2.59/0.99  --res_to_prop_solver                    active
% 2.59/0.99  --res_prop_simpl_new                    false
% 2.59/0.99  --res_prop_simpl_given                  true
% 2.59/0.99  --res_passive_queue_type                priority_queues
% 2.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.99  --res_passive_queues_freq               [15;5]
% 2.59/0.99  --res_forward_subs                      full
% 2.59/0.99  --res_backward_subs                     full
% 2.59/0.99  --res_forward_subs_resolution           true
% 2.59/0.99  --res_backward_subs_resolution          true
% 2.59/0.99  --res_orphan_elimination                true
% 2.59/0.99  --res_time_limit                        2.
% 2.59/0.99  --res_out_proof                         true
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Options
% 2.59/0.99  
% 2.59/0.99  --superposition_flag                    true
% 2.59/0.99  --sup_passive_queue_type                priority_queues
% 2.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.99  --demod_completeness_check              fast
% 2.59/0.99  --demod_use_ground                      true
% 2.59/0.99  --sup_to_prop_solver                    passive
% 2.59/0.99  --sup_prop_simpl_new                    true
% 2.59/0.99  --sup_prop_simpl_given                  true
% 2.59/0.99  --sup_fun_splitting                     false
% 2.59/0.99  --sup_smt_interval                      50000
% 2.59/0.99  
% 2.59/0.99  ------ Superposition Simplification Setup
% 2.59/0.99  
% 2.59/0.99  --sup_indices_passive                   []
% 2.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_full_bw                           [BwDemod]
% 2.59/0.99  --sup_immed_triv                        [TrivRules]
% 2.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_immed_bw_main                     []
% 2.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.99  
% 2.59/0.99  ------ Combination Options
% 2.59/0.99  
% 2.59/0.99  --comb_res_mult                         3
% 2.59/0.99  --comb_sup_mult                         2
% 2.59/0.99  --comb_inst_mult                        10
% 2.59/0.99  
% 2.59/0.99  ------ Debug Options
% 2.59/0.99  
% 2.59/0.99  --dbg_backtrace                         false
% 2.59/0.99  --dbg_dump_prop_clauses                 false
% 2.59/0.99  --dbg_dump_prop_clauses_file            -
% 2.59/0.99  --dbg_out_stat                          false
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  ------ Proving...
% 2.59/0.99  
% 2.59/0.99  
% 2.59/0.99  % SZS status Theorem for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.99  
% 2.59/0.99  fof(f17,conjecture,(
% 2.59/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f18,negated_conjecture,(
% 2.59/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.59/0.99    inference(negated_conjecture,[],[f17])).
% 2.59/0.99  
% 2.59/0.99  fof(f20,plain,(
% 2.59/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.59/0.99    inference(pure_predicate_removal,[],[f18])).
% 2.59/0.99  
% 2.59/0.99  fof(f32,plain,(
% 2.59/0.99    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 2.59/0.99    inference(ennf_transformation,[],[f20])).
% 2.59/0.99  
% 2.59/0.99  fof(f33,plain,(
% 2.59/0.99    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 2.59/0.99    inference(flattening,[],[f32])).
% 2.59/0.99  
% 2.59/0.99  fof(f42,plain,(
% 2.59/0.99    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f43,plain,(
% 2.59/0.99    (~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3)),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42])).
% 2.59/0.99  
% 2.59/0.99  fof(f74,plain,(
% 2.59/0.99    r2_hidden(sK3,k1_funct_2(sK1,sK2))),
% 2.59/0.99    inference(cnf_transformation,[],[f43])).
% 2.59/0.99  
% 2.59/0.99  fof(f16,axiom,(
% 2.59/0.99    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f72,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f16])).
% 2.59/0.99  
% 2.59/0.99  fof(f79,plain,(
% 2.59/0.99    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))),
% 2.59/0.99    inference(definition_unfolding,[],[f74,f72])).
% 2.59/0.99  
% 2.59/0.99  fof(f15,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f19,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 2.59/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.59/0.99  
% 2.59/0.99  fof(f31,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 2.59/0.99    inference(ennf_transformation,[],[f19])).
% 2.59/0.99  
% 2.59/0.99  fof(f71,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f31])).
% 2.59/0.99  
% 2.59/0.99  fof(f77,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f71,f72])).
% 2.59/0.99  
% 2.59/0.99  fof(f7,axiom,(
% 2.59/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f40,plain,(
% 2.59/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.59/0.99    inference(nnf_transformation,[],[f7])).
% 2.59/0.99  
% 2.59/0.99  fof(f53,plain,(
% 2.59/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f40])).
% 2.59/0.99  
% 2.59/0.99  fof(f9,axiom,(
% 2.59/0.99    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f23,plain,(
% 2.59/0.99    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.59/0.99    inference(ennf_transformation,[],[f9])).
% 2.59/0.99  
% 2.59/0.99  fof(f57,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.59/0.99    inference(cnf_transformation,[],[f23])).
% 2.59/0.99  
% 2.59/0.99  fof(f10,axiom,(
% 2.59/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f24,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f10])).
% 2.59/0.99  
% 2.59/0.99  fof(f25,plain,(
% 2.59/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.99    inference(flattening,[],[f24])).
% 2.59/0.99  
% 2.59/0.99  fof(f59,plain,(
% 2.59/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f25])).
% 2.59/0.99  
% 2.59/0.99  fof(f8,axiom,(
% 2.59/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f55,plain,(
% 2.59/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f8])).
% 2.59/0.99  
% 2.59/0.99  fof(f73,plain,(
% 2.59/0.99    v1_relat_1(sK3)),
% 2.59/0.99    inference(cnf_transformation,[],[f43])).
% 2.59/0.99  
% 2.59/0.99  fof(f70,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f31])).
% 2.59/0.99  
% 2.59/0.99  fof(f78,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.59/0.99    inference(definition_unfolding,[],[f70,f72])).
% 2.59/0.99  
% 2.59/0.99  fof(f13,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f27,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.99    inference(ennf_transformation,[],[f13])).
% 2.59/0.99  
% 2.59/0.99  fof(f28,plain,(
% 2.59/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.99    inference(flattening,[],[f27])).
% 2.59/0.99  
% 2.59/0.99  fof(f41,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.99    inference(nnf_transformation,[],[f28])).
% 2.59/0.99  
% 2.59/0.99  fof(f63,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f41])).
% 2.59/0.99  
% 2.59/0.99  fof(f12,axiom,(
% 2.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f26,plain,(
% 2.59/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.99    inference(ennf_transformation,[],[f12])).
% 2.59/0.99  
% 2.59/0.99  fof(f62,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f26])).
% 2.59/0.99  
% 2.59/0.99  fof(f75,plain,(
% 2.59/0.99    ~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1),
% 2.59/0.99    inference(cnf_transformation,[],[f43])).
% 2.59/0.99  
% 2.59/0.99  fof(f6,axiom,(
% 2.59/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f38,plain,(
% 2.59/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.59/0.99    inference(nnf_transformation,[],[f6])).
% 2.59/0.99  
% 2.59/0.99  fof(f39,plain,(
% 2.59/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.59/0.99    inference(flattening,[],[f38])).
% 2.59/0.99  
% 2.59/0.99  fof(f51,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.59/0.99    inference(cnf_transformation,[],[f39])).
% 2.59/0.99  
% 2.59/0.99  fof(f81,plain,(
% 2.59/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.59/0.99    inference(equality_resolution,[],[f51])).
% 2.59/0.99  
% 2.59/0.99  fof(f5,axiom,(
% 2.59/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f22,plain,(
% 2.59/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.59/0.99    inference(ennf_transformation,[],[f5])).
% 2.59/0.99  
% 2.59/0.99  fof(f49,plain,(
% 2.59/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f22])).
% 2.59/0.99  
% 2.59/0.99  fof(f4,axiom,(
% 2.59/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f48,plain,(
% 2.59/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f4])).
% 2.59/0.99  
% 2.59/0.99  fof(f11,axiom,(
% 2.59/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f61,plain,(
% 2.59/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.59/0.99    inference(cnf_transformation,[],[f11])).
% 2.59/0.99  
% 2.59/0.99  fof(f50,plain,(
% 2.59/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f39])).
% 2.59/0.99  
% 2.59/0.99  fof(f67,plain,(
% 2.59/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.99    inference(cnf_transformation,[],[f41])).
% 2.59/0.99  
% 2.59/0.99  fof(f84,plain,(
% 2.59/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.59/0.99    inference(equality_resolution,[],[f67])).
% 2.59/0.99  
% 2.59/0.99  fof(f2,axiom,(
% 2.59/0.99    v1_xboole_0(k1_xboole_0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f46,plain,(
% 2.59/0.99    v1_xboole_0(k1_xboole_0)),
% 2.59/0.99    inference(cnf_transformation,[],[f2])).
% 2.59/0.99  
% 2.59/0.99  fof(f3,axiom,(
% 2.59/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f21,plain,(
% 2.59/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.59/0.99    inference(ennf_transformation,[],[f3])).
% 2.59/0.99  
% 2.59/0.99  fof(f47,plain,(
% 2.59/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f21])).
% 2.59/0.99  
% 2.59/0.99  fof(f14,axiom,(
% 2.59/0.99    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f29,plain,(
% 2.59/0.99    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.59/0.99    inference(ennf_transformation,[],[f14])).
% 2.59/0.99  
% 2.59/0.99  fof(f30,plain,(
% 2.59/0.99    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.59/0.99    inference(flattening,[],[f29])).
% 2.59/0.99  
% 2.59/0.99  fof(f69,plain,(
% 2.59/0.99    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f30])).
% 2.59/0.99  
% 2.59/0.99  fof(f76,plain,(
% 2.59/0.99    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.59/0.99    inference(definition_unfolding,[],[f69,f72])).
% 2.59/0.99  
% 2.59/0.99  fof(f1,axiom,(
% 2.59/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.99  
% 2.59/0.99  fof(f34,plain,(
% 2.59/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.59/0.99    inference(nnf_transformation,[],[f1])).
% 2.59/0.99  
% 2.59/0.99  fof(f35,plain,(
% 2.59/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.59/0.99    inference(rectify,[],[f34])).
% 2.59/0.99  
% 2.59/0.99  fof(f36,plain,(
% 2.59/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.59/0.99    introduced(choice_axiom,[])).
% 2.59/0.99  
% 2.59/0.99  fof(f37,plain,(
% 2.59/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.59/0.99  
% 2.59/0.99  fof(f44,plain,(
% 2.59/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.59/0.99    inference(cnf_transformation,[],[f37])).
% 2.59/0.99  
% 2.59/0.99  fof(f60,plain,(
% 2.59/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.59/0.99    inference(cnf_transformation,[],[f11])).
% 2.59/0.99  
% 2.59/0.99  cnf(c_29,negated_conjecture,
% 2.59/0.99      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
% 2.59/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1846,plain,
% 2.59/0.99      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_26,plain,
% 2.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.59/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1848,plain,
% 2.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.59/0.99      | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3110,plain,
% 2.59/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_1846,c_1848]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_10,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.59/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1854,plain,
% 2.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.59/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3321,plain,
% 2.59/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3110,c_1854]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_12,plain,
% 2.59/0.99      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_14,plain,
% 2.59/0.99      ( ~ r1_tarski(X0,X1)
% 2.59/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.59/0.99      | ~ v1_relat_1(X1)
% 2.59/0.99      | ~ v1_relat_1(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1852,plain,
% 2.59/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 2.59/0.99      | v1_relat_1(X1) != iProver_top
% 2.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3819,plain,
% 2.59/0.99      ( k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.59/0.99      | v1_relat_1(X2) != iProver_top
% 2.59/0.99      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_12,c_1852]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_11,plain,
% 2.59/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.59/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_70,plain,
% 2.59/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5297,plain,
% 2.59/0.99      ( v1_relat_1(X2) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.59/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_3819,c_70]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5298,plain,
% 2.59/0.99      ( k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.59/0.99      | v1_relat_1(X2) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_5297]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5307,plain,
% 2.59/0.99      ( sK1 = k1_xboole_0
% 2.59/0.99      | sK2 = k1_xboole_0
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.59/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3321,c_5298]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_30,negated_conjecture,
% 2.59/0.99      ( v1_relat_1(sK3) ),
% 2.59/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_27,plain,
% 2.59/0.99      ( v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.59/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_24,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_709,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(resolution,[status(thm)],[c_27,c_24]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_412,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(resolution,[status(thm)],[c_26,c_24]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_416,plain,
% 2.59/0.99      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_412,c_27]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_713,plain,
% 2.59/0.99      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.59/0.99      | k1_xboole_0 = X2 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_709,c_27,c_412]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1844,plain,
% 2.59/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3009,plain,
% 2.59/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_1846,c_1844]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_18,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1850,plain,
% 2.59/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3322,plain,
% 2.59/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3110,c_1850]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3456,plain,
% 2.59/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3009,c_3322]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_28,negated_conjecture,
% 2.59/0.99      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1847,plain,
% 2.59/0.99      ( k1_relat_1(sK3) != sK1
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3596,plain,
% 2.59/0.99      ( sK2 = k1_xboole_0
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3456,c_1847]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3627,plain,
% 2.59/0.99      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | sK2 = k1_xboole_0 ),
% 2.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3596]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5323,plain,
% 2.59/0.99      ( r1_tarski(k2_relat_1(sK3),sK2)
% 2.59/0.99      | ~ v1_relat_1(sK3)
% 2.59/0.99      | sK1 = k1_xboole_0
% 2.59/0.99      | sK2 = k1_xboole_0 ),
% 2.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5307]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5651,plain,
% 2.59/0.99      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_5307,c_30,c_3627,c_5323]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5663,plain,
% 2.59/0.99      ( sK2 = k1_xboole_0
% 2.59/0.99      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_5651,c_3321]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_7,plain,
% 2.59/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.59/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5689,plain,
% 2.59/0.99      ( sK2 = k1_xboole_0 | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_5663,c_7]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5,plain,
% 2.59/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.59/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1856,plain,
% 2.59/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5968,plain,
% 2.59/0.99      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_5689,c_1856]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1316,plain,
% 2.59/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.59/0.99      theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2082,plain,
% 2.59/0.99      ( ~ r1_tarski(X0,X1)
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.59/0.99      | k2_relat_1(sK3) != X0
% 2.59/0.99      | sK2 != X1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1316]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2166,plain,
% 2.59/0.99      ( ~ r1_tarski(X0,sK2)
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.59/0.99      | k2_relat_1(sK3) != X0
% 2.59/0.99      | sK2 != sK2 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2082]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2168,plain,
% 2.59/0.99      ( k2_relat_1(sK3) != X0
% 2.59/0.99      | sK2 != sK2
% 2.59/0.99      | r1_tarski(X0,sK2) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2166]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2170,plain,
% 2.59/0.99      ( k2_relat_1(sK3) != k1_xboole_0
% 2.59/0.99      | sK2 != sK2
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.59/0.99      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2168]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1312,plain,( X0 = X0 ),theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2167,plain,
% 2.59/0.99      ( sK2 = sK2 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1312]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4,plain,
% 2.59/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2407,plain,
% 2.59/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2410,plain,
% 2.59/0.99      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2407]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_16,plain,
% 2.59/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.59/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3820,plain,
% 2.59/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
% 2.59/0.99      | v1_relat_1(X0) != iProver_top
% 2.59/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_16,c_1852]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_72,plain,
% 2.59/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_70]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_8,plain,
% 2.59/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_79,plain,
% 2.59/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.59/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_80,plain,
% 2.59/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1320,plain,
% 2.59/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.59/0.99      theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2031,plain,
% 2.59/0.99      ( v1_relat_1(X0)
% 2.59/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 2.59/0.99      | X0 != k2_zfmisc_1(X1,X2) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1320]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2032,plain,
% 2.59/0.99      ( X0 != k2_zfmisc_1(X1,X2)
% 2.59/0.99      | v1_relat_1(X0) = iProver_top
% 2.59/0.99      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2031]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2034,plain,
% 2.59/0.99      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 2.59/0.99      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.59/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2032]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1313,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2202,plain,
% 2.59/0.99      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2203,plain,
% 2.59/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.59/0.99      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 2.59/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2202]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3945,plain,
% 2.59/0.99      ( v1_relat_1(X0) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
% 2.59/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_3820,c_72,c_79,c_80,c_2034,c_2203]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3946,plain,
% 2.59/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.59/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
% 2.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.59/0.99      inference(renaming,[status(thm)],[c_3945]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3954,plain,
% 2.59/0.99      ( k2_relat_1(X0) = k1_xboole_0
% 2.59/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_3946,c_1856]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5966,plain,
% 2.59/0.99      ( k2_relat_1(sK3) = k1_xboole_0
% 2.59/0.99      | sK2 = k1_xboole_0
% 2.59/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_5689,c_3954]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6056,plain,
% 2.59/0.99      ( ~ v1_relat_1(sK3)
% 2.59/0.99      | k2_relat_1(sK3) = k1_xboole_0
% 2.59/0.99      | sK2 = k1_xboole_0 ),
% 2.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5966]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6263,plain,
% 2.59/0.99      ( sK2 = k1_xboole_0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_5968,c_30,c_2170,c_2167,c_2410,c_3596,c_6056]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6277,plain,
% 2.59/0.99      ( r2_hidden(sK3,k5_partfun1(sK1,k1_xboole_0,k3_partfun1(k1_xboole_0,sK1,k1_xboole_0))) = iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_6263,c_1846]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_20,plain,
% 2.59/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | k1_xboole_0 = X0 ),
% 2.59/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_736,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.59/0.99      | ~ r2_hidden(X2,k5_partfun1(X3,X4,k3_partfun1(k1_xboole_0,X3,X4)))
% 2.59/0.99      | X2 != X0
% 2.59/0.99      | X3 != X1
% 2.59/0.99      | k1_xboole_0 != X4
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_737,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.59/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_736]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_749,plain,
% 2.59/0.99      ( ~ r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
% 2.59/0.99      | k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1 ),
% 2.59/0.99      inference(forward_subsumption_resolution,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_737,c_26]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1843,plain,
% 2.59/0.99      ( k1_xboole_0 = X0
% 2.59/0.99      | k1_xboole_0 = X1
% 2.59/0.99      | r2_hidden(X0,k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0))) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6424,plain,
% 2.59/0.99      ( sK1 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_6277,c_1843]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2,plain,
% 2.59/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.59/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_90,plain,
% 2.59/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_390,plain,
% 2.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) != k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
% 2.59/0.99      | sK3 != X0 ),
% 2.59/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_391,plain,
% 2.59/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) != k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)) ),
% 2.59/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_393,plain,
% 2.59/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 2.59/0.99      | k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_391]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2114,plain,
% 2.59/0.99      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2160,plain,
% 2.59/0.99      ( sK3 = sK3 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1312]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2926,plain,
% 2.59/0.99      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2927,plain,
% 2.59/0.99      ( sK2 != k1_xboole_0
% 2.59/0.99      | k1_xboole_0 = sK2
% 2.59/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2926]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2437,plain,
% 2.59/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3065,plain,
% 2.59/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2437]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3066,plain,
% 2.59/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_3065]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3,plain,
% 2.59/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.59/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3185,plain,
% 2.59/0.99      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3186,plain,
% 2.59/0.99      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_3185]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2247,plain,
% 2.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3474,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.99      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2247]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3477,plain,
% 2.59/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 2.59/0.99      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_3474]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2321,plain,
% 2.59/0.99      ( ~ r1_tarski(X0,X1)
% 2.59/0.99      | r1_tarski(sK3,k1_xboole_0)
% 2.59/0.99      | sK3 != X0
% 2.59/0.99      | k1_xboole_0 != X1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1316]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2981,plain,
% 2.59/0.99      ( ~ r1_tarski(sK3,X0)
% 2.59/0.99      | r1_tarski(sK3,k1_xboole_0)
% 2.59/0.99      | sK3 != sK3
% 2.59/0.99      | k1_xboole_0 != X0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2321]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4695,plain,
% 2.59/0.99      ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
% 2.59/0.99      | r1_tarski(sK3,k1_xboole_0)
% 2.59/0.99      | sK3 != sK3
% 2.59/0.99      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2981]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_4698,plain,
% 2.59/0.99      ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.59/0.99      | r1_tarski(sK3,k1_xboole_0)
% 2.59/0.99      | sK3 != sK3
% 2.59/0.99      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_4695]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1325,plain,
% 2.59/0.99      ( X0 != X1
% 2.59/0.99      | X2 != X3
% 2.59/0.99      | X4 != X5
% 2.59/0.99      | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
% 2.59/0.99      theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2393,plain,
% 2.59/0.99      ( X0 != k3_partfun1(k1_xboole_0,sK1,sK2)
% 2.59/0.99      | X1 != sK1
% 2.59/0.99      | X2 != sK2
% 2.59/0.99      | k5_partfun1(X1,X2,X0) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3175,plain,
% 2.59/0.99      ( X0 != k3_partfun1(k1_xboole_0,sK1,sK2)
% 2.59/0.99      | X1 != sK2
% 2.59/0.99      | k5_partfun1(k1_xboole_0,X1,X0) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
% 2.59/0.99      | k1_xboole_0 != sK1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2393]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5265,plain,
% 2.59/0.99      ( X0 != sK2
% 2.59/0.99      | k5_partfun1(k1_xboole_0,X0,k3_partfun1(X1,X2,X3)) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
% 2.59/0.99      | k3_partfun1(X1,X2,X3) != k3_partfun1(k1_xboole_0,sK1,sK2)
% 2.59/0.99      | k1_xboole_0 != sK1 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_3175]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5267,plain,
% 2.59/0.99      ( k5_partfun1(k1_xboole_0,k1_xboole_0,k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))
% 2.59/0.99      | k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_partfun1(k1_xboole_0,sK1,sK2)
% 2.59/0.99      | k1_xboole_0 != sK1
% 2.59/0.99      | k1_xboole_0 != sK2 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_5265]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1324,plain,
% 2.59/0.99      ( X0 != X1
% 2.59/0.99      | X2 != X3
% 2.59/0.99      | X4 != X5
% 2.59/0.99      | k3_partfun1(X0,X2,X4) = k3_partfun1(X1,X3,X5) ),
% 2.59/0.99      theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5266,plain,
% 2.59/0.99      ( X0 != sK1
% 2.59/0.99      | X1 != sK2
% 2.59/0.99      | X2 != k1_xboole_0
% 2.59/0.99      | k3_partfun1(X2,X0,X1) = k3_partfun1(k1_xboole_0,sK1,sK2) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1324]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_5268,plain,
% 2.59/0.99      ( k3_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k3_partfun1(k1_xboole_0,sK1,sK2)
% 2.59/0.99      | k1_xboole_0 != sK1
% 2.59/0.99      | k1_xboole_0 != sK2
% 2.59/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_5266]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_25,plain,
% 2.59/0.99      ( ~ v1_xboole_0(X0)
% 2.59/0.99      | v1_xboole_0(X1)
% 2.59/0.99      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
% 2.59/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1849,plain,
% 2.59/0.99      ( v1_xboole_0(X0) != iProver_top
% 2.59/0.99      | v1_xboole_0(X1) = iProver_top
% 2.59/0.99      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1,plain,
% 2.59/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.59/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1860,plain,
% 2.59/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.59/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2500,plain,
% 2.59/0.99      ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_1846,c_1860]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3207,plain,
% 2.59/0.99      ( v1_xboole_0(sK1) = iProver_top
% 2.59/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.59/0.99      inference(superposition,[status(thm)],[c_1849,c_2500]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6270,plain,
% 2.59/0.99      ( v1_xboole_0(sK1) = iProver_top
% 2.59/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_6263,c_3207]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6582,plain,
% 2.59/0.99      ( sK3 = k1_xboole_0 ),
% 2.59/0.99      inference(global_propositional_subsumption,
% 2.59/0.99                [status(thm)],
% 2.59/0.99                [c_6424,c_30,c_79,c_80,c_90,c_393,c_2114,c_2160,c_2170,
% 2.59/0.99                 c_2167,c_2203,c_2410,c_2927,c_3066,c_3186,c_3477,c_3596,
% 2.59/0.99                 c_4698,c_5267,c_5268,c_6056,c_6270]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_6276,plain,
% 2.59/0.99      ( k1_relat_1(sK3) != sK1
% 2.59/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 2.59/0.99      inference(demodulation,[status(thm)],[c_6263,c_1847]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_71,plain,
% 2.59/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_85,plain,
% 2.59/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2033,plain,
% 2.59/0.99      ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.59/0.99      | v1_relat_1(k1_xboole_0)
% 2.59/0.99      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2031]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_1321,plain,
% 2.59/0.99      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 2.59/0.99      theory(equality) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2575,plain,
% 2.59/0.99      ( k2_relat_1(sK3) = k2_relat_1(X0) | sK3 != X0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_1321]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_2580,plain,
% 2.59/0.99      ( k2_relat_1(sK3) = k2_relat_1(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 2.59/0.99      inference(instantiation,[status(thm)],[c_2575]) ).
% 2.59/0.99  
% 2.59/0.99  cnf(c_3859,plain,
% 2.59/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 2.59/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 2.59/0.99      | ~ v1_relat_1(X0)
% 2.59/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 2.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3820]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3861,plain,
% 2.59/1.00      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.59/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.59/1.00      | ~ v1_relat_1(k1_xboole_0) ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_3859]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4421,plain,
% 2.59/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.59/1.00      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.59/1.00      | k2_relat_1(sK3) != k2_relat_1(X0)
% 2.59/1.00      | sK2 != X1 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_2082]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_4434,plain,
% 2.59/1.00      ( r1_tarski(k2_relat_1(sK3),sK2)
% 2.59/1.00      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.59/1.00      | k2_relat_1(sK3) != k2_relat_1(k1_xboole_0)
% 2.59/1.00      | sK2 != k1_xboole_0 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_4421]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6435,plain,
% 2.59/1.00      ( k1_relat_1(sK3) != sK1 ),
% 2.59/1.00      inference(global_propositional_subsumption,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6276,c_30,c_28,c_71,c_79,c_80,c_85,c_90,c_393,c_2033,
% 2.59/1.00                 c_2114,c_2160,c_2170,c_2167,c_2203,c_2410,c_2580,c_2927,
% 2.59/1.00                 c_3066,c_3186,c_3477,c_3596,c_3861,c_4434,c_4698,c_5267,
% 2.59/1.00                 c_5268,c_6056,c_6270]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6585,plain,
% 2.59/1.00      ( k1_relat_1(k1_xboole_0) != sK1 ),
% 2.59/1.00      inference(demodulation,[status(thm)],[c_6582,c_6435]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_17,plain,
% 2.59/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.59/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6592,plain,
% 2.59/1.00      ( sK1 != k1_xboole_0 ),
% 2.59/1.00      inference(light_normalisation,[status(thm)],[c_6585,c_17]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3160,plain,
% 2.59/1.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_1313]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6346,plain,
% 2.59/1.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_3160]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_6347,plain,
% 2.59/1.00      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_6346]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(c_3158,plain,
% 2.59/1.00      ( sK1 = sK1 ),
% 2.59/1.00      inference(instantiation,[status(thm)],[c_1312]) ).
% 2.59/1.00  
% 2.59/1.00  cnf(contradiction,plain,
% 2.59/1.00      ( $false ),
% 2.59/1.00      inference(minisat,
% 2.59/1.00                [status(thm)],
% 2.59/1.00                [c_6592,c_6347,c_6270,c_3186,c_3158,c_90]) ).
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/1.00  
% 2.59/1.00  ------                               Statistics
% 2.59/1.00  
% 2.59/1.00  ------ General
% 2.59/1.00  
% 2.59/1.00  abstr_ref_over_cycles:                  0
% 2.59/1.00  abstr_ref_under_cycles:                 0
% 2.59/1.00  gc_basic_clause_elim:                   0
% 2.59/1.00  forced_gc_time:                         0
% 2.59/1.00  parsing_time:                           0.011
% 2.59/1.00  unif_index_cands_time:                  0.
% 2.59/1.00  unif_index_add_time:                    0.
% 2.59/1.00  orderings_time:                         0.
% 2.59/1.00  out_proof_time:                         0.013
% 2.59/1.00  total_time:                             0.196
% 2.59/1.00  num_of_symbols:                         49
% 2.59/1.00  num_of_terms:                           4292
% 2.59/1.00  
% 2.59/1.00  ------ Preprocessing
% 2.59/1.00  
% 2.59/1.00  num_of_splits:                          0
% 2.59/1.00  num_of_split_atoms:                     0
% 2.59/1.00  num_of_reused_defs:                     0
% 2.59/1.00  num_eq_ax_congr_red:                    11
% 2.59/1.00  num_of_sem_filtered_clauses:            1
% 2.59/1.00  num_of_subtypes:                        0
% 2.59/1.00  monotx_restored_types:                  0
% 2.59/1.00  sat_num_of_epr_types:                   0
% 2.59/1.00  sat_num_of_non_cyclic_types:            0
% 2.59/1.00  sat_guarded_non_collapsed_types:        0
% 2.59/1.00  num_pure_diseq_elim:                    0
% 2.59/1.00  simp_replaced_by:                       0
% 2.59/1.00  res_preprocessed:                       141
% 2.59/1.00  prep_upred:                             0
% 2.59/1.00  prep_unflattend:                        84
% 2.59/1.00  smt_new_axioms:                         0
% 2.59/1.00  pred_elim_cands:                        5
% 2.59/1.00  pred_elim:                              1
% 2.59/1.00  pred_elim_cl:                           4
% 2.59/1.00  pred_elim_cycles:                       7
% 2.59/1.00  merged_defs:                            8
% 2.59/1.00  merged_defs_ncl:                        0
% 2.59/1.00  bin_hyper_res:                          8
% 2.59/1.00  prep_cycles:                            4
% 2.59/1.00  pred_elim_time:                         0.015
% 2.59/1.00  splitting_time:                         0.
% 2.59/1.00  sem_filter_time:                        0.
% 2.59/1.00  monotx_time:                            0.001
% 2.59/1.00  subtype_inf_time:                       0.
% 2.59/1.00  
% 2.59/1.00  ------ Problem properties
% 2.59/1.00  
% 2.59/1.00  clauses:                                27
% 2.59/1.00  conjectures:                            3
% 2.59/1.00  epr:                                    6
% 2.59/1.00  horn:                                   20
% 2.59/1.00  ground:                                 6
% 2.59/1.00  unary:                                  9
% 2.59/1.00  binary:                                 10
% 2.59/1.00  lits:                                   55
% 2.59/1.00  lits_eq:                                22
% 2.59/1.00  fd_pure:                                0
% 2.59/1.00  fd_pseudo:                              0
% 2.59/1.00  fd_cond:                                4
% 2.59/1.00  fd_pseudo_cond:                         0
% 2.59/1.00  ac_symbols:                             0
% 2.59/1.00  
% 2.59/1.00  ------ Propositional Solver
% 2.59/1.00  
% 2.59/1.00  prop_solver_calls:                      28
% 2.59/1.00  prop_fast_solver_calls:                 1078
% 2.59/1.00  smt_solver_calls:                       0
% 2.59/1.00  smt_fast_solver_calls:                  0
% 2.59/1.00  prop_num_of_clauses:                    1890
% 2.59/1.00  prop_preprocess_simplified:             6003
% 2.59/1.00  prop_fo_subsumed:                       21
% 2.59/1.00  prop_solver_time:                       0.
% 2.59/1.00  smt_solver_time:                        0.
% 2.59/1.00  smt_fast_solver_time:                   0.
% 2.59/1.00  prop_fast_solver_time:                  0.
% 2.59/1.00  prop_unsat_core_time:                   0.
% 2.59/1.00  
% 2.59/1.00  ------ QBF
% 2.59/1.00  
% 2.59/1.00  qbf_q_res:                              0
% 2.59/1.00  qbf_num_tautologies:                    0
% 2.59/1.00  qbf_prep_cycles:                        0
% 2.59/1.00  
% 2.59/1.00  ------ BMC1
% 2.59/1.00  
% 2.59/1.00  bmc1_current_bound:                     -1
% 2.59/1.00  bmc1_last_solved_bound:                 -1
% 2.59/1.00  bmc1_unsat_core_size:                   -1
% 2.59/1.00  bmc1_unsat_core_parents_size:           -1
% 2.59/1.00  bmc1_merge_next_fun:                    0
% 2.59/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.59/1.00  
% 2.59/1.00  ------ Instantiation
% 2.59/1.00  
% 2.59/1.00  inst_num_of_clauses:                    642
% 2.59/1.00  inst_num_in_passive:                    24
% 2.59/1.00  inst_num_in_active:                     334
% 2.59/1.00  inst_num_in_unprocessed:                284
% 2.59/1.00  inst_num_of_loops:                      450
% 2.59/1.00  inst_num_of_learning_restarts:          0
% 2.59/1.00  inst_num_moves_active_passive:          113
% 2.59/1.00  inst_lit_activity:                      0
% 2.59/1.00  inst_lit_activity_moves:                0
% 2.59/1.00  inst_num_tautologies:                   0
% 2.59/1.00  inst_num_prop_implied:                  0
% 2.59/1.00  inst_num_existing_simplified:           0
% 2.59/1.00  inst_num_eq_res_simplified:             0
% 2.59/1.00  inst_num_child_elim:                    0
% 2.59/1.00  inst_num_of_dismatching_blockings:      88
% 2.59/1.00  inst_num_of_non_proper_insts:           454
% 2.59/1.00  inst_num_of_duplicates:                 0
% 2.59/1.00  inst_inst_num_from_inst_to_res:         0
% 2.59/1.00  inst_dismatching_checking_time:         0.
% 2.59/1.00  
% 2.59/1.00  ------ Resolution
% 2.59/1.00  
% 2.59/1.00  res_num_of_clauses:                     0
% 2.59/1.00  res_num_in_passive:                     0
% 2.59/1.00  res_num_in_active:                      0
% 2.59/1.00  res_num_of_loops:                       145
% 2.59/1.00  res_forward_subset_subsumed:            31
% 2.59/1.00  res_backward_subset_subsumed:           0
% 2.59/1.00  res_forward_subsumed:                   0
% 2.59/1.00  res_backward_subsumed:                  0
% 2.59/1.00  res_forward_subsumption_resolution:     3
% 2.59/1.00  res_backward_subsumption_resolution:    0
% 2.59/1.00  res_clause_to_clause_subsumption:       563
% 2.59/1.00  res_orphan_elimination:                 0
% 2.59/1.00  res_tautology_del:                      71
% 2.59/1.00  res_num_eq_res_simplified:              0
% 2.59/1.00  res_num_sel_changes:                    0
% 2.59/1.00  res_moves_from_active_to_pass:          0
% 2.59/1.00  
% 2.59/1.00  ------ Superposition
% 2.59/1.00  
% 2.59/1.00  sup_time_total:                         0.
% 2.59/1.00  sup_time_generating:                    0.
% 2.59/1.00  sup_time_sim_full:                      0.
% 2.59/1.00  sup_time_sim_immed:                     0.
% 2.59/1.00  
% 2.59/1.00  sup_num_of_clauses:                     124
% 2.59/1.00  sup_num_in_active:                      60
% 2.59/1.00  sup_num_in_passive:                     64
% 2.59/1.00  sup_num_of_loops:                       89
% 2.59/1.00  sup_fw_superposition:                   116
% 2.59/1.00  sup_bw_superposition:                   87
% 2.59/1.00  sup_immediate_simplified:               35
% 2.59/1.00  sup_given_eliminated:                   0
% 2.59/1.00  comparisons_done:                       0
% 2.59/1.00  comparisons_avoided:                    12
% 2.59/1.00  
% 2.59/1.00  ------ Simplifications
% 2.59/1.00  
% 2.59/1.00  
% 2.59/1.00  sim_fw_subset_subsumed:                 11
% 2.59/1.00  sim_bw_subset_subsumed:                 15
% 2.59/1.00  sim_fw_subsumed:                        8
% 2.59/1.00  sim_bw_subsumed:                        0
% 2.59/1.00  sim_fw_subsumption_res:                 2
% 2.59/1.00  sim_bw_subsumption_res:                 0
% 2.59/1.00  sim_tautology_del:                      6
% 2.59/1.00  sim_eq_tautology_del:                   37
% 2.59/1.00  sim_eq_res_simp:                        0
% 2.59/1.00  sim_fw_demodulated:                     5
% 2.59/1.00  sim_bw_demodulated:                     16
% 2.59/1.00  sim_light_normalised:                   15
% 2.59/1.00  sim_joinable_taut:                      0
% 2.59/1.00  sim_joinable_simp:                      0
% 2.59/1.00  sim_ac_normalised:                      0
% 2.59/1.00  sim_smt_subsumption:                    0
% 2.59/1.00  
%------------------------------------------------------------------------------
