%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:18 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 678 expanded)
%              Number of clauses        :  139 ( 222 expanded)
%              Number of leaves         :   25 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :  644 (2102 expanded)
%              Number of equality atoms :  387 (1128 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f49,f47,f82,f82,f82,f83,f83,f83,f47])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f41])).

fof(f78,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f78,f83])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f48,f83])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k2_tarski(X0,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f47,f82])).

fof(f99,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f83,f83])).

fof(f81,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(definition_unfolding,[],[f81,f83,f83])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3458,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_4523,plain,
    ( k2_relat_1(sK2) != X0_49
    | k1_xboole_0 != X0_49
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_6929,plain,
    ( k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k1_xboole_0 != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4523])).

cnf(c_6933,plain,
    ( k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6929])).

cnf(c_4346,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_49
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k2_relat_1(sK2) != X0_49 ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_6930,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) ),
    inference(instantiation,[status(thm)],[c_4346])).

cnf(c_6932,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_6930])).

cnf(c_4336,plain,
    ( X0_49 != X1_49
    | k2_relat_1(sK2) != X1_49
    | k2_relat_1(sK2) = X0_49 ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_4608,plain,
    ( X0_49 != k2_relat_1(sK2)
    | k2_relat_1(sK2) = X0_49
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4336])).

cnf(c_6578,plain,
    ( k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4608])).

cnf(c_6580,plain,
    ( k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6578])).

cnf(c_3466,plain,
    ( X0_49 != X1_49
    | k2_relat_1(X0_49) = k2_relat_1(X1_49) ),
    theory(equality)).

cnf(c_4903,plain,
    ( X0_49 != sK2
    | k2_relat_1(X0_49) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3466])).

cnf(c_6483,plain,
    ( k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X1_50,X2_50)) != sK2
    | k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X1_50,X2_50))) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4903])).

cnf(c_6489,plain,
    ( k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) != sK2
    | k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6483])).

cnf(c_3463,plain,
    ( X0_49 != X1_49
    | k1_relat_1(X0_49) = k1_relat_1(X1_49) ),
    theory(equality)).

cnf(c_5597,plain,
    ( X0_49 != sK2
    | k1_relat_1(X0_49) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3463])).

cnf(c_5599,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5597])).

cnf(c_4329,plain,
    ( X0_49 != X1_49
    | k1_relat_1(sK2) != X1_49
    | k1_relat_1(sK2) = X0_49 ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_4602,plain,
    ( X0_49 != k1_relat_1(sK2)
    | k1_relat_1(sK2) = X0_49
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4329])).

cnf(c_5596,plain,
    ( k1_relat_1(X0_49) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(X0_49)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4602])).

cnf(c_5598,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5596])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_389,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_14])).

cnf(c_3433,plain,
    ( ~ r1_tarski(k1_relat_1(X0_49),X1_49)
    | ~ v1_relat_1(X0_49)
    | k7_relat_1(X0_49,X1_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_4234,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0_49)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0_49) = sK2 ),
    inference(instantiation,[status(thm)],[c_3433])).

cnf(c_5504,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_enumset1(X0_50,X0_50,X1_50,X2_50))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X1_50,X2_50)) = sK2 ),
    inference(instantiation,[status(thm)],[c_4234])).

cnf(c_5508,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_5504])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3439,plain,
    ( ~ r1_tarski(X0_49,k2_enumset1(X0_50,X0_50,X1_50,X2_50))
    | k2_enumset1(X1_50,X1_50,X1_50,X2_50) = X0_49
    | k2_enumset1(X2_50,X2_50,X2_50,X2_50) = X0_49
    | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = X0_49
    | k2_enumset1(X0_50,X0_50,X1_50,X2_50) = X0_49
    | k2_enumset1(X0_50,X0_50,X0_50,X2_50) = X0_49
    | k2_enumset1(X0_50,X0_50,X0_50,X1_50) = X0_49
    | k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_49
    | k1_xboole_0 = X0_49 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4386,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(X1_50,X1_50,X2_50,X3_50))
    | k2_enumset1(X2_50,X2_50,X2_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_enumset1(X3_50,X3_50,X3_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_enumset1(X2_50,X2_50,X2_50,X2_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_enumset1(X1_50,X1_50,X2_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_enumset1(X1_50,X1_50,X1_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_enumset1(X1_50,X1_50,X1_50,X2_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) ),
    inference(instantiation,[status(thm)],[c_3439])).

cnf(c_5174,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)))
    | k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
    | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) ),
    inference(instantiation,[status(thm)],[c_4386])).

cnf(c_5176,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)))
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_5174])).

cnf(c_3460,plain,
    ( ~ v1_xboole_0(X0_49)
    | v1_xboole_0(X1_49)
    | X1_49 != X0_49 ),
    theory(equality)).

cnf(c_5001,plain,
    ( ~ v1_xboole_0(X0_49)
    | v1_xboole_0(k2_relat_1(sK2))
    | k2_relat_1(sK2) != X0_49 ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_5003,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5001])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_358,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_359,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_746,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v1_relat_1(sK2)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_359])).

cnf(c_747,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ v1_relat_1(sK2)
    | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_1615,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | sK1 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_747])).

cnf(c_1616,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(unflattening,[status(thm)],[c_1615])).

cnf(c_3423,plain,
    ( ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1616])).

cnf(c_3913,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3423])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3448,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0_50,X0_50,X0_50,X0_50)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3492,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_3448])).

cnf(c_4210,plain,
    ( v1_xboole_0(X0_49)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0_49 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_4217,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4210])).

cnf(c_3450,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3892,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3450])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3449,plain,
    ( ~ v1_xboole_0(X0_49)
    | k1_xboole_0 = X0_49 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3893,plain,
    ( k1_xboole_0 = X0_49
    | v1_xboole_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3449])).

cnf(c_4269,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3892,c_3893])).

cnf(c_4371,plain,
    ( ~ v1_xboole_0(X0_49)
    | v1_xboole_0(k2_enumset1(X0_50,X0_50,X0_50,X0_50))
    | k2_enumset1(X0_50,X0_50,X0_50,X0_50) != X0_49 ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_4373,plain,
    ( v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4371])).

cnf(c_4980,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3913,c_0,c_3492,c_4217,c_4269,c_4373])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_512,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_513,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_3431,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_4140,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_3431])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_548,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_relat_1(sK2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_359])).

cnf(c_549,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ v1_relat_1(sK2)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_1555,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) != X0
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_549])).

cnf(c_1556,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1555])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1558,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1556,c_32])).

cnf(c_1559,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_1558])).

cnf(c_467,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_468,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_1572,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_468])).

cnf(c_1573,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1572])).

cnf(c_1574,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1573,c_32])).

cnf(c_1575,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_1574])).

cnf(c_1984,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_1575])).

cnf(c_1986,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_1984])).

cnf(c_3417,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subtyping,[status(esa)],[c_1986])).

cnf(c_4172,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4140,c_3417])).

cnf(c_4982,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4980,c_4172])).

cnf(c_4,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X2,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3446,plain,
    ( r1_tarski(k2_enumset1(X0_50,X0_50,X0_50,X1_50),k2_enumset1(X0_50,X0_50,X2_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3896,plain,
    ( r1_tarski(k2_enumset1(X0_50,X0_50,X0_50,X1_50),k2_enumset1(X0_50,X0_50,X2_50,X1_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3446])).

cnf(c_4750,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,X0_50,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_3896])).

cnf(c_4756,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,X0_50,sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4750])).

cnf(c_4758,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_4756])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_620,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_359])).

cnf(c_621,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_3426,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(X0_49)
    | v1_xboole_0(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)) ),
    inference(subtyping,[status(esa)],[c_621])).

cnf(c_3451,plain,
    ( ~ v1_xboole_0(X0_49)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3426])).

cnf(c_4740,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_3451])).

cnf(c_4536,plain,
    ( k1_relat_1(X0_49) != X1_49
    | k1_xboole_0 != X1_49
    | k1_xboole_0 = k1_relat_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_4537,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4536])).

cnf(c_4436,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_3454,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_4335,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_4159,plain,
    ( k2_relat_1(sK2) != X0_49
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0_49 ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_4334,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_4158,plain,
    ( k1_relat_1(sK2) != X0_49
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0_49 ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_4330,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0_49)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0_49) ),
    inference(instantiation,[status(thm)],[c_4158])).

cnf(c_4332,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4330])).

cnf(c_4328,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_3456,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_4306,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_3456])).

cnf(c_4164,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_49
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0_49 ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_4230,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4164])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_503,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_504,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_3432,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k2_relset_1(X0_49,X1_49,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_504])).

cnf(c_4145,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3432])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_536,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_537,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_3429,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_537])).

cnf(c_4147,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_3429])).

cnf(c_4144,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_3456])).

cnf(c_3452,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3426])).

cnf(c_17,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_368,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_369,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)))
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_3434,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)))
    | ~ v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_3508,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3434])).

cnf(c_31,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3436,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3437,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3485,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6933,c_6932,c_6580,c_6489,c_5599,c_5598,c_5508,c_5176,c_5003,c_4982,c_4758,c_4740,c_4537,c_4436,c_4335,c_4334,c_4332,c_4328,c_4306,c_4269,c_4230,c_4217,c_4145,c_4147,c_4144,c_3452,c_3508,c_3436,c_3437,c_3485,c_0])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.64/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/0.98  
% 2.64/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/0.98  
% 2.64/0.98  ------  iProver source info
% 2.64/0.98  
% 2.64/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.64/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/0.98  git: non_committed_changes: false
% 2.64/0.98  git: last_make_outside_of_git: false
% 2.64/0.98  
% 2.64/0.98  ------ 
% 2.64/0.98  
% 2.64/0.98  ------ Input Options
% 2.64/0.98  
% 2.64/0.98  --out_options                           all
% 2.64/0.98  --tptp_safe_out                         true
% 2.64/0.98  --problem_path                          ""
% 2.64/0.98  --include_path                          ""
% 2.64/0.98  --clausifier                            res/vclausify_rel
% 2.64/0.98  --clausifier_options                    --mode clausify
% 2.64/0.98  --stdin                                 false
% 2.64/0.98  --stats_out                             all
% 2.64/0.98  
% 2.64/0.98  ------ General Options
% 2.64/0.98  
% 2.64/0.98  --fof                                   false
% 2.64/0.98  --time_out_real                         305.
% 2.64/0.98  --time_out_virtual                      -1.
% 2.64/0.98  --symbol_type_check                     false
% 2.64/0.98  --clausify_out                          false
% 2.64/0.98  --sig_cnt_out                           false
% 2.64/0.98  --trig_cnt_out                          false
% 2.64/0.98  --trig_cnt_out_tolerance                1.
% 2.64/0.98  --trig_cnt_out_sk_spl                   false
% 2.64/0.98  --abstr_cl_out                          false
% 2.64/0.98  
% 2.64/0.98  ------ Global Options
% 2.64/0.98  
% 2.64/0.98  --schedule                              default
% 2.64/0.98  --add_important_lit                     false
% 2.64/0.98  --prop_solver_per_cl                    1000
% 2.64/0.98  --min_unsat_core                        false
% 2.64/0.98  --soft_assumptions                      false
% 2.64/0.98  --soft_lemma_size                       3
% 2.64/0.98  --prop_impl_unit_size                   0
% 2.64/0.98  --prop_impl_unit                        []
% 2.64/0.98  --share_sel_clauses                     true
% 2.64/0.98  --reset_solvers                         false
% 2.64/0.98  --bc_imp_inh                            [conj_cone]
% 2.64/0.98  --conj_cone_tolerance                   3.
% 2.64/0.98  --extra_neg_conj                        none
% 2.64/0.98  --large_theory_mode                     true
% 2.64/0.98  --prolific_symb_bound                   200
% 2.64/0.98  --lt_threshold                          2000
% 2.64/0.98  --clause_weak_htbl                      true
% 2.64/0.98  --gc_record_bc_elim                     false
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing Options
% 2.64/0.98  
% 2.64/0.98  --preprocessing_flag                    true
% 2.64/0.98  --time_out_prep_mult                    0.1
% 2.64/0.98  --splitting_mode                        input
% 2.64/0.98  --splitting_grd                         true
% 2.64/0.98  --splitting_cvd                         false
% 2.64/0.98  --splitting_cvd_svl                     false
% 2.64/0.98  --splitting_nvd                         32
% 2.64/0.98  --sub_typing                            true
% 2.64/0.98  --prep_gs_sim                           true
% 2.64/0.98  --prep_unflatten                        true
% 2.64/0.98  --prep_res_sim                          true
% 2.64/0.98  --prep_upred                            true
% 2.64/0.98  --prep_sem_filter                       exhaustive
% 2.64/0.98  --prep_sem_filter_out                   false
% 2.64/0.98  --pred_elim                             true
% 2.64/0.98  --res_sim_input                         true
% 2.64/0.98  --eq_ax_congr_red                       true
% 2.64/0.98  --pure_diseq_elim                       true
% 2.64/0.98  --brand_transform                       false
% 2.64/0.98  --non_eq_to_eq                          false
% 2.64/0.98  --prep_def_merge                        true
% 2.64/0.98  --prep_def_merge_prop_impl              false
% 2.64/0.98  --prep_def_merge_mbd                    true
% 2.64/0.98  --prep_def_merge_tr_red                 false
% 2.64/0.98  --prep_def_merge_tr_cl                  false
% 2.64/0.98  --smt_preprocessing                     true
% 2.64/0.98  --smt_ac_axioms                         fast
% 2.64/0.98  --preprocessed_out                      false
% 2.64/0.98  --preprocessed_stats                    false
% 2.64/0.98  
% 2.64/0.98  ------ Abstraction refinement Options
% 2.64/0.98  
% 2.64/0.98  --abstr_ref                             []
% 2.64/0.98  --abstr_ref_prep                        false
% 2.64/0.98  --abstr_ref_until_sat                   false
% 2.64/0.98  --abstr_ref_sig_restrict                funpre
% 2.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.98  --abstr_ref_under                       []
% 2.64/0.98  
% 2.64/0.98  ------ SAT Options
% 2.64/0.98  
% 2.64/0.98  --sat_mode                              false
% 2.64/0.98  --sat_fm_restart_options                ""
% 2.64/0.98  --sat_gr_def                            false
% 2.64/0.98  --sat_epr_types                         true
% 2.64/0.98  --sat_non_cyclic_types                  false
% 2.64/0.98  --sat_finite_models                     false
% 2.64/0.98  --sat_fm_lemmas                         false
% 2.64/0.98  --sat_fm_prep                           false
% 2.64/0.98  --sat_fm_uc_incr                        true
% 2.64/0.98  --sat_out_model                         small
% 2.64/0.98  --sat_out_clauses                       false
% 2.64/0.98  
% 2.64/0.98  ------ QBF Options
% 2.64/0.98  
% 2.64/0.98  --qbf_mode                              false
% 2.64/0.98  --qbf_elim_univ                         false
% 2.64/0.98  --qbf_dom_inst                          none
% 2.64/0.98  --qbf_dom_pre_inst                      false
% 2.64/0.98  --qbf_sk_in                             false
% 2.64/0.98  --qbf_pred_elim                         true
% 2.64/0.98  --qbf_split                             512
% 2.64/0.98  
% 2.64/0.98  ------ BMC1 Options
% 2.64/0.98  
% 2.64/0.98  --bmc1_incremental                      false
% 2.64/0.98  --bmc1_axioms                           reachable_all
% 2.64/0.98  --bmc1_min_bound                        0
% 2.64/0.98  --bmc1_max_bound                        -1
% 2.64/0.98  --bmc1_max_bound_default                -1
% 2.64/0.98  --bmc1_symbol_reachability              true
% 2.64/0.98  --bmc1_property_lemmas                  false
% 2.64/0.98  --bmc1_k_induction                      false
% 2.64/0.98  --bmc1_non_equiv_states                 false
% 2.64/0.98  --bmc1_deadlock                         false
% 2.64/0.98  --bmc1_ucm                              false
% 2.64/0.98  --bmc1_add_unsat_core                   none
% 2.64/0.98  --bmc1_unsat_core_children              false
% 2.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.98  --bmc1_out_stat                         full
% 2.64/0.98  --bmc1_ground_init                      false
% 2.64/0.98  --bmc1_pre_inst_next_state              false
% 2.64/0.98  --bmc1_pre_inst_state                   false
% 2.64/0.98  --bmc1_pre_inst_reach_state             false
% 2.64/0.98  --bmc1_out_unsat_core                   false
% 2.64/0.98  --bmc1_aig_witness_out                  false
% 2.64/0.98  --bmc1_verbose                          false
% 2.64/0.98  --bmc1_dump_clauses_tptp                false
% 2.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.98  --bmc1_dump_file                        -
% 2.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.98  --bmc1_ucm_extend_mode                  1
% 2.64/0.98  --bmc1_ucm_init_mode                    2
% 2.64/0.98  --bmc1_ucm_cone_mode                    none
% 2.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.98  --bmc1_ucm_relax_model                  4
% 2.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.98  --bmc1_ucm_layered_model                none
% 2.64/0.98  --bmc1_ucm_max_lemma_size               10
% 2.64/0.98  
% 2.64/0.98  ------ AIG Options
% 2.64/0.98  
% 2.64/0.98  --aig_mode                              false
% 2.64/0.98  
% 2.64/0.98  ------ Instantiation Options
% 2.64/0.98  
% 2.64/0.98  --instantiation_flag                    true
% 2.64/0.98  --inst_sos_flag                         false
% 2.64/0.98  --inst_sos_phase                        true
% 2.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.98  --inst_lit_sel_side                     num_symb
% 2.64/0.98  --inst_solver_per_active                1400
% 2.64/0.98  --inst_solver_calls_frac                1.
% 2.64/0.98  --inst_passive_queue_type               priority_queues
% 2.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.98  --inst_passive_queues_freq              [25;2]
% 2.64/0.98  --inst_dismatching                      true
% 2.64/0.98  --inst_eager_unprocessed_to_passive     true
% 2.64/0.98  --inst_prop_sim_given                   true
% 2.64/0.98  --inst_prop_sim_new                     false
% 2.64/0.98  --inst_subs_new                         false
% 2.64/0.98  --inst_eq_res_simp                      false
% 2.64/0.98  --inst_subs_given                       false
% 2.64/0.98  --inst_orphan_elimination               true
% 2.64/0.98  --inst_learning_loop_flag               true
% 2.64/0.98  --inst_learning_start                   3000
% 2.64/0.98  --inst_learning_factor                  2
% 2.64/0.98  --inst_start_prop_sim_after_learn       3
% 2.64/0.98  --inst_sel_renew                        solver
% 2.64/0.98  --inst_lit_activity_flag                true
% 2.64/0.98  --inst_restr_to_given                   false
% 2.64/0.98  --inst_activity_threshold               500
% 2.64/0.98  --inst_out_proof                        true
% 2.64/0.98  
% 2.64/0.98  ------ Resolution Options
% 2.64/0.98  
% 2.64/0.98  --resolution_flag                       true
% 2.64/0.98  --res_lit_sel                           adaptive
% 2.64/0.98  --res_lit_sel_side                      none
% 2.64/0.98  --res_ordering                          kbo
% 2.64/0.98  --res_to_prop_solver                    active
% 2.64/0.98  --res_prop_simpl_new                    false
% 2.64/0.98  --res_prop_simpl_given                  true
% 2.64/0.98  --res_passive_queue_type                priority_queues
% 2.64/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.98  --res_passive_queues_freq               [15;5]
% 2.64/0.98  --res_forward_subs                      full
% 2.64/0.98  --res_backward_subs                     full
% 2.64/0.98  --res_forward_subs_resolution           true
% 2.64/0.98  --res_backward_subs_resolution          true
% 2.64/0.98  --res_orphan_elimination                true
% 2.64/0.98  --res_time_limit                        2.
% 2.64/0.98  --res_out_proof                         true
% 2.64/0.98  
% 2.64/0.98  ------ Superposition Options
% 2.64/0.98  
% 2.64/0.98  --superposition_flag                    true
% 2.64/0.98  --sup_passive_queue_type                priority_queues
% 2.64/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.98  --demod_completeness_check              fast
% 2.64/0.98  --demod_use_ground                      true
% 2.64/0.98  --sup_to_prop_solver                    passive
% 2.64/0.98  --sup_prop_simpl_new                    true
% 2.64/0.98  --sup_prop_simpl_given                  true
% 2.64/0.98  --sup_fun_splitting                     false
% 2.64/0.98  --sup_smt_interval                      50000
% 2.64/0.98  
% 2.64/0.98  ------ Superposition Simplification Setup
% 2.64/0.98  
% 2.64/0.98  --sup_indices_passive                   []
% 2.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.98  --sup_full_bw                           [BwDemod]
% 2.64/0.98  --sup_immed_triv                        [TrivRules]
% 2.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.98  --sup_immed_bw_main                     []
% 2.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.98  
% 2.64/0.98  ------ Combination Options
% 2.64/0.98  
% 2.64/0.98  --comb_res_mult                         3
% 2.64/0.98  --comb_sup_mult                         2
% 2.64/0.98  --comb_inst_mult                        10
% 2.64/0.98  
% 2.64/0.98  ------ Debug Options
% 2.64/0.98  
% 2.64/0.98  --dbg_backtrace                         false
% 2.64/0.98  --dbg_dump_prop_clauses                 false
% 2.64/0.98  --dbg_dump_prop_clauses_file            -
% 2.64/0.98  --dbg_out_stat                          false
% 2.64/0.98  ------ Parsing...
% 2.64/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/0.98  ------ Proving...
% 2.64/0.98  ------ Problem Properties 
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  clauses                                 35
% 2.64/0.98  conjectures                             2
% 2.64/0.98  EPR                                     4
% 2.64/0.98  Horn                                    29
% 2.64/0.98  unary                                   15
% 2.64/0.98  binary                                  5
% 2.64/0.98  lits                                    84
% 2.64/0.98  lits eq                                 54
% 2.64/0.98  fd_pure                                 0
% 2.64/0.98  fd_pseudo                               0
% 2.64/0.98  fd_cond                                 1
% 2.64/0.98  fd_pseudo_cond                          1
% 2.64/0.98  AC symbols                              0
% 2.64/0.98  
% 2.64/0.98  ------ Schedule dynamic 5 is on 
% 2.64/0.98  
% 2.64/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  ------ 
% 2.64/0.98  Current options:
% 2.64/0.98  ------ 
% 2.64/0.98  
% 2.64/0.98  ------ Input Options
% 2.64/0.98  
% 2.64/0.98  --out_options                           all
% 2.64/0.98  --tptp_safe_out                         true
% 2.64/0.98  --problem_path                          ""
% 2.64/0.98  --include_path                          ""
% 2.64/0.98  --clausifier                            res/vclausify_rel
% 2.64/0.98  --clausifier_options                    --mode clausify
% 2.64/0.98  --stdin                                 false
% 2.64/0.98  --stats_out                             all
% 2.64/0.98  
% 2.64/0.98  ------ General Options
% 2.64/0.98  
% 2.64/0.98  --fof                                   false
% 2.64/0.98  --time_out_real                         305.
% 2.64/0.98  --time_out_virtual                      -1.
% 2.64/0.98  --symbol_type_check                     false
% 2.64/0.98  --clausify_out                          false
% 2.64/0.98  --sig_cnt_out                           false
% 2.64/0.98  --trig_cnt_out                          false
% 2.64/0.98  --trig_cnt_out_tolerance                1.
% 2.64/0.98  --trig_cnt_out_sk_spl                   false
% 2.64/0.98  --abstr_cl_out                          false
% 2.64/0.98  
% 2.64/0.98  ------ Global Options
% 2.64/0.98  
% 2.64/0.98  --schedule                              default
% 2.64/0.98  --add_important_lit                     false
% 2.64/0.98  --prop_solver_per_cl                    1000
% 2.64/0.98  --min_unsat_core                        false
% 2.64/0.98  --soft_assumptions                      false
% 2.64/0.98  --soft_lemma_size                       3
% 2.64/0.98  --prop_impl_unit_size                   0
% 2.64/0.98  --prop_impl_unit                        []
% 2.64/0.98  --share_sel_clauses                     true
% 2.64/0.98  --reset_solvers                         false
% 2.64/0.98  --bc_imp_inh                            [conj_cone]
% 2.64/0.98  --conj_cone_tolerance                   3.
% 2.64/0.98  --extra_neg_conj                        none
% 2.64/0.98  --large_theory_mode                     true
% 2.64/0.98  --prolific_symb_bound                   200
% 2.64/0.98  --lt_threshold                          2000
% 2.64/0.98  --clause_weak_htbl                      true
% 2.64/0.98  --gc_record_bc_elim                     false
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing Options
% 2.64/0.98  
% 2.64/0.98  --preprocessing_flag                    true
% 2.64/0.98  --time_out_prep_mult                    0.1
% 2.64/0.98  --splitting_mode                        input
% 2.64/0.98  --splitting_grd                         true
% 2.64/0.98  --splitting_cvd                         false
% 2.64/0.98  --splitting_cvd_svl                     false
% 2.64/0.98  --splitting_nvd                         32
% 2.64/0.98  --sub_typing                            true
% 2.64/0.98  --prep_gs_sim                           true
% 2.64/0.98  --prep_unflatten                        true
% 2.64/0.98  --prep_res_sim                          true
% 2.64/0.98  --prep_upred                            true
% 2.64/0.98  --prep_sem_filter                       exhaustive
% 2.64/0.98  --prep_sem_filter_out                   false
% 2.64/0.98  --pred_elim                             true
% 2.64/0.98  --res_sim_input                         true
% 2.64/0.98  --eq_ax_congr_red                       true
% 2.64/0.98  --pure_diseq_elim                       true
% 2.64/0.98  --brand_transform                       false
% 2.64/0.98  --non_eq_to_eq                          false
% 2.64/0.98  --prep_def_merge                        true
% 2.64/0.98  --prep_def_merge_prop_impl              false
% 2.64/0.98  --prep_def_merge_mbd                    true
% 2.64/0.98  --prep_def_merge_tr_red                 false
% 2.64/0.98  --prep_def_merge_tr_cl                  false
% 2.64/0.98  --smt_preprocessing                     true
% 2.64/0.98  --smt_ac_axioms                         fast
% 2.64/0.98  --preprocessed_out                      false
% 2.64/0.98  --preprocessed_stats                    false
% 2.64/0.98  
% 2.64/0.98  ------ Abstraction refinement Options
% 2.64/0.98  
% 2.64/0.98  --abstr_ref                             []
% 2.64/0.98  --abstr_ref_prep                        false
% 2.64/0.98  --abstr_ref_until_sat                   false
% 2.64/0.98  --abstr_ref_sig_restrict                funpre
% 2.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.98  --abstr_ref_under                       []
% 2.64/0.98  
% 2.64/0.98  ------ SAT Options
% 2.64/0.98  
% 2.64/0.98  --sat_mode                              false
% 2.64/0.98  --sat_fm_restart_options                ""
% 2.64/0.98  --sat_gr_def                            false
% 2.64/0.98  --sat_epr_types                         true
% 2.64/0.98  --sat_non_cyclic_types                  false
% 2.64/0.98  --sat_finite_models                     false
% 2.64/0.98  --sat_fm_lemmas                         false
% 2.64/0.98  --sat_fm_prep                           false
% 2.64/0.98  --sat_fm_uc_incr                        true
% 2.64/0.98  --sat_out_model                         small
% 2.64/0.98  --sat_out_clauses                       false
% 2.64/0.98  
% 2.64/0.98  ------ QBF Options
% 2.64/0.98  
% 2.64/0.98  --qbf_mode                              false
% 2.64/0.98  --qbf_elim_univ                         false
% 2.64/0.98  --qbf_dom_inst                          none
% 2.64/0.98  --qbf_dom_pre_inst                      false
% 2.64/0.98  --qbf_sk_in                             false
% 2.64/0.98  --qbf_pred_elim                         true
% 2.64/0.98  --qbf_split                             512
% 2.64/0.98  
% 2.64/0.98  ------ BMC1 Options
% 2.64/0.98  
% 2.64/0.98  --bmc1_incremental                      false
% 2.64/0.98  --bmc1_axioms                           reachable_all
% 2.64/0.98  --bmc1_min_bound                        0
% 2.64/0.98  --bmc1_max_bound                        -1
% 2.64/0.98  --bmc1_max_bound_default                -1
% 2.64/0.98  --bmc1_symbol_reachability              true
% 2.64/0.98  --bmc1_property_lemmas                  false
% 2.64/0.98  --bmc1_k_induction                      false
% 2.64/0.98  --bmc1_non_equiv_states                 false
% 2.64/0.98  --bmc1_deadlock                         false
% 2.64/0.98  --bmc1_ucm                              false
% 2.64/0.98  --bmc1_add_unsat_core                   none
% 2.64/0.98  --bmc1_unsat_core_children              false
% 2.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.98  --bmc1_out_stat                         full
% 2.64/0.98  --bmc1_ground_init                      false
% 2.64/0.98  --bmc1_pre_inst_next_state              false
% 2.64/0.98  --bmc1_pre_inst_state                   false
% 2.64/0.98  --bmc1_pre_inst_reach_state             false
% 2.64/0.98  --bmc1_out_unsat_core                   false
% 2.64/0.98  --bmc1_aig_witness_out                  false
% 2.64/0.98  --bmc1_verbose                          false
% 2.64/0.98  --bmc1_dump_clauses_tptp                false
% 2.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.98  --bmc1_dump_file                        -
% 2.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.98  --bmc1_ucm_extend_mode                  1
% 2.64/0.98  --bmc1_ucm_init_mode                    2
% 2.64/0.98  --bmc1_ucm_cone_mode                    none
% 2.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.98  --bmc1_ucm_relax_model                  4
% 2.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.98  --bmc1_ucm_layered_model                none
% 2.64/0.98  --bmc1_ucm_max_lemma_size               10
% 2.64/0.98  
% 2.64/0.98  ------ AIG Options
% 2.64/0.98  
% 2.64/0.98  --aig_mode                              false
% 2.64/0.98  
% 2.64/0.98  ------ Instantiation Options
% 2.64/0.98  
% 2.64/0.98  --instantiation_flag                    true
% 2.64/0.98  --inst_sos_flag                         false
% 2.64/0.98  --inst_sos_phase                        true
% 2.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.98  --inst_lit_sel_side                     none
% 2.64/0.98  --inst_solver_per_active                1400
% 2.64/0.98  --inst_solver_calls_frac                1.
% 2.64/0.98  --inst_passive_queue_type               priority_queues
% 2.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.98  --inst_passive_queues_freq              [25;2]
% 2.64/0.98  --inst_dismatching                      true
% 2.64/0.98  --inst_eager_unprocessed_to_passive     true
% 2.64/0.98  --inst_prop_sim_given                   true
% 2.64/0.98  --inst_prop_sim_new                     false
% 2.64/0.98  --inst_subs_new                         false
% 2.64/0.98  --inst_eq_res_simp                      false
% 2.64/0.98  --inst_subs_given                       false
% 2.64/0.98  --inst_orphan_elimination               true
% 2.64/0.98  --inst_learning_loop_flag               true
% 2.64/0.98  --inst_learning_start                   3000
% 2.64/0.98  --inst_learning_factor                  2
% 2.64/0.98  --inst_start_prop_sim_after_learn       3
% 2.64/0.98  --inst_sel_renew                        solver
% 2.64/0.98  --inst_lit_activity_flag                true
% 2.64/0.98  --inst_restr_to_given                   false
% 2.64/0.98  --inst_activity_threshold               500
% 2.64/0.98  --inst_out_proof                        true
% 2.64/0.98  
% 2.64/0.98  ------ Resolution Options
% 2.64/0.98  
% 2.64/0.98  --resolution_flag                       false
% 2.64/0.98  --res_lit_sel                           adaptive
% 2.64/0.98  --res_lit_sel_side                      none
% 2.64/0.98  --res_ordering                          kbo
% 2.64/0.98  --res_to_prop_solver                    active
% 2.64/0.98  --res_prop_simpl_new                    false
% 2.64/0.98  --res_prop_simpl_given                  true
% 2.64/0.98  --res_passive_queue_type                priority_queues
% 2.64/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.98  --res_passive_queues_freq               [15;5]
% 2.64/0.98  --res_forward_subs                      full
% 2.64/0.98  --res_backward_subs                     full
% 2.64/0.98  --res_forward_subs_resolution           true
% 2.64/0.98  --res_backward_subs_resolution          true
% 2.64/0.98  --res_orphan_elimination                true
% 2.64/0.98  --res_time_limit                        2.
% 2.64/0.98  --res_out_proof                         true
% 2.64/0.98  
% 2.64/0.98  ------ Superposition Options
% 2.64/0.98  
% 2.64/0.98  --superposition_flag                    true
% 2.64/0.98  --sup_passive_queue_type                priority_queues
% 2.64/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.98  --demod_completeness_check              fast
% 2.64/0.98  --demod_use_ground                      true
% 2.64/0.98  --sup_to_prop_solver                    passive
% 2.64/0.98  --sup_prop_simpl_new                    true
% 2.64/0.98  --sup_prop_simpl_given                  true
% 2.64/0.98  --sup_fun_splitting                     false
% 2.64/0.98  --sup_smt_interval                      50000
% 2.64/0.98  
% 2.64/0.98  ------ Superposition Simplification Setup
% 2.64/0.98  
% 2.64/0.98  --sup_indices_passive                   []
% 2.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.98  --sup_full_bw                           [BwDemod]
% 2.64/0.98  --sup_immed_triv                        [TrivRules]
% 2.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.98  --sup_immed_bw_main                     []
% 2.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.98  
% 2.64/0.98  ------ Combination Options
% 2.64/0.98  
% 2.64/0.98  --comb_res_mult                         3
% 2.64/0.98  --comb_sup_mult                         2
% 2.64/0.98  --comb_inst_mult                        10
% 2.64/0.98  
% 2.64/0.98  ------ Debug Options
% 2.64/0.98  
% 2.64/0.98  --dbg_backtrace                         false
% 2.64/0.98  --dbg_dump_prop_clauses                 false
% 2.64/0.98  --dbg_dump_prop_clauses_file            -
% 2.64/0.98  --dbg_out_stat                          false
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  ------ Proving...
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  % SZS status Theorem for theBenchmark.p
% 2.64/0.98  
% 2.64/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/0.98  
% 2.64/0.98  fof(f8,axiom,(
% 2.64/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f22,plain,(
% 2.64/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.64/0.98    inference(ennf_transformation,[],[f8])).
% 2.64/0.98  
% 2.64/0.98  fof(f39,plain,(
% 2.64/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.64/0.98    inference(nnf_transformation,[],[f22])).
% 2.64/0.98  
% 2.64/0.98  fof(f59,plain,(
% 2.64/0.98    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f39])).
% 2.64/0.98  
% 2.64/0.98  fof(f9,axiom,(
% 2.64/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f23,plain,(
% 2.64/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.64/0.98    inference(ennf_transformation,[],[f9])).
% 2.64/0.98  
% 2.64/0.98  fof(f24,plain,(
% 2.64/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/0.98    inference(flattening,[],[f23])).
% 2.64/0.98  
% 2.64/0.98  fof(f60,plain,(
% 2.64/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f24])).
% 2.64/0.98  
% 2.64/0.98  fof(f7,axiom,(
% 2.64/0.98    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f21,plain,(
% 2.64/0.98    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.64/0.98    inference(ennf_transformation,[],[f7])).
% 2.64/0.98  
% 2.64/0.98  fof(f37,plain,(
% 2.64/0.98    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.64/0.98    inference(nnf_transformation,[],[f21])).
% 2.64/0.98  
% 2.64/0.98  fof(f38,plain,(
% 2.64/0.98    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.64/0.98    inference(flattening,[],[f37])).
% 2.64/0.98  
% 2.64/0.98  fof(f49,plain,(
% 2.64/0.98    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.64/0.98    inference(cnf_transformation,[],[f38])).
% 2.64/0.98  
% 2.64/0.98  fof(f3,axiom,(
% 2.64/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f45,plain,(
% 2.64/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f3])).
% 2.64/0.98  
% 2.64/0.98  fof(f4,axiom,(
% 2.64/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f46,plain,(
% 2.64/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f4])).
% 2.64/0.98  
% 2.64/0.98  fof(f82,plain,(
% 2.64/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.64/0.98    inference(definition_unfolding,[],[f46,f47])).
% 2.64/0.98  
% 2.64/0.98  fof(f83,plain,(
% 2.64/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.64/0.98    inference(definition_unfolding,[],[f45,f82])).
% 2.64/0.98  
% 2.64/0.98  fof(f5,axiom,(
% 2.64/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f47,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f5])).
% 2.64/0.98  
% 2.64/0.98  fof(f93,plain,(
% 2.64/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.64/0.98    inference(definition_unfolding,[],[f49,f47,f82,f82,f82,f83,f83,f83,f47])).
% 2.64/0.98  
% 2.64/0.98  fof(f18,conjecture,(
% 2.64/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f19,negated_conjecture,(
% 2.64/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.64/0.98    inference(negated_conjecture,[],[f18])).
% 2.64/0.98  
% 2.64/0.98  fof(f35,plain,(
% 2.64/0.98    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.64/0.98    inference(ennf_transformation,[],[f19])).
% 2.64/0.98  
% 2.64/0.98  fof(f36,plain,(
% 2.64/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.64/0.98    inference(flattening,[],[f35])).
% 2.64/0.98  
% 2.64/0.98  fof(f41,plain,(
% 2.64/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 2.64/0.98    introduced(choice_axiom,[])).
% 2.64/0.98  
% 2.64/0.98  fof(f42,plain,(
% 2.64/0.98    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 2.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f41])).
% 2.64/0.98  
% 2.64/0.98  fof(f78,plain,(
% 2.64/0.98    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 2.64/0.98    inference(cnf_transformation,[],[f42])).
% 2.64/0.98  
% 2.64/0.98  fof(f97,plain,(
% 2.64/0.98    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.64/0.98    inference(definition_unfolding,[],[f78,f83])).
% 2.64/0.98  
% 2.64/0.98  fof(f16,axiom,(
% 2.64/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f31,plain,(
% 2.64/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.98    inference(ennf_transformation,[],[f16])).
% 2.64/0.98  
% 2.64/0.98  fof(f32,plain,(
% 2.64/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.98    inference(flattening,[],[f31])).
% 2.64/0.98  
% 2.64/0.98  fof(f40,plain,(
% 2.64/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.98    inference(nnf_transformation,[],[f32])).
% 2.64/0.98  
% 2.64/0.98  fof(f69,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/0.98    inference(cnf_transformation,[],[f40])).
% 2.64/0.98  
% 2.64/0.98  fof(f110,plain,(
% 2.64/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.64/0.98    inference(equality_resolution,[],[f69])).
% 2.64/0.98  
% 2.64/0.98  fof(f17,axiom,(
% 2.64/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f33,plain,(
% 2.64/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/0.98    inference(ennf_transformation,[],[f17])).
% 2.64/0.98  
% 2.64/0.98  fof(f34,plain,(
% 2.64/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/0.98    inference(flattening,[],[f33])).
% 2.64/0.98  
% 2.64/0.98  fof(f76,plain,(
% 2.64/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f34])).
% 2.64/0.98  
% 2.64/0.98  fof(f77,plain,(
% 2.64/0.98    v1_funct_1(sK2)),
% 2.64/0.98    inference(cnf_transformation,[],[f42])).
% 2.64/0.98  
% 2.64/0.98  fof(f1,axiom,(
% 2.64/0.98    v1_xboole_0(o_0_0_xboole_0)),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f43,plain,(
% 2.64/0.98    v1_xboole_0(o_0_0_xboole_0)),
% 2.64/0.98    inference(cnf_transformation,[],[f1])).
% 2.64/0.98  
% 2.64/0.98  fof(f6,axiom,(
% 2.64/0.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f48,plain,(
% 2.64/0.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.64/0.98    inference(cnf_transformation,[],[f6])).
% 2.64/0.98  
% 2.64/0.98  fof(f84,plain,(
% 2.64/0.98    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.64/0.98    inference(definition_unfolding,[],[f48,f83])).
% 2.64/0.98  
% 2.64/0.98  fof(f2,axiom,(
% 2.64/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f20,plain,(
% 2.64/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.64/0.98    inference(ennf_transformation,[],[f2])).
% 2.64/0.98  
% 2.64/0.98  fof(f44,plain,(
% 2.64/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f20])).
% 2.64/0.98  
% 2.64/0.98  fof(f14,axiom,(
% 2.64/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f29,plain,(
% 2.64/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.98    inference(ennf_transformation,[],[f14])).
% 2.64/0.98  
% 2.64/0.98  fof(f66,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/0.98    inference(cnf_transformation,[],[f29])).
% 2.64/0.98  
% 2.64/0.98  fof(f79,plain,(
% 2.64/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.64/0.98    inference(cnf_transformation,[],[f42])).
% 2.64/0.98  
% 2.64/0.98  fof(f96,plain,(
% 2.64/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.64/0.98    inference(definition_unfolding,[],[f79,f83])).
% 2.64/0.98  
% 2.64/0.98  fof(f68,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/0.98    inference(cnf_transformation,[],[f40])).
% 2.64/0.98  
% 2.64/0.98  fof(f80,plain,(
% 2.64/0.98    k1_xboole_0 != sK1),
% 2.64/0.98    inference(cnf_transformation,[],[f42])).
% 2.64/0.98  
% 2.64/0.98  fof(f56,plain,(
% 2.64/0.98    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k2_tarski(X0,X2) != X3) )),
% 2.64/0.98    inference(cnf_transformation,[],[f38])).
% 2.64/0.98  
% 2.64/0.98  fof(f86,plain,(
% 2.64/0.98    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X2) != X3) )),
% 2.64/0.98    inference(definition_unfolding,[],[f56,f47,f82])).
% 2.64/0.98  
% 2.64/0.98  fof(f99,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X0,X0,X1,X2))) )),
% 2.64/0.98    inference(equality_resolution,[],[f86])).
% 2.64/0.98  
% 2.64/0.98  fof(f13,axiom,(
% 2.64/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f28,plain,(
% 2.64/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.64/0.98    inference(ennf_transformation,[],[f13])).
% 2.64/0.98  
% 2.64/0.98  fof(f65,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f28])).
% 2.64/0.98  
% 2.64/0.98  fof(f15,axiom,(
% 2.64/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f30,plain,(
% 2.64/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.98    inference(ennf_transformation,[],[f15])).
% 2.64/0.98  
% 2.64/0.98  fof(f67,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/0.98    inference(cnf_transformation,[],[f30])).
% 2.64/0.98  
% 2.64/0.98  fof(f12,axiom,(
% 2.64/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f27,plain,(
% 2.64/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.98    inference(ennf_transformation,[],[f12])).
% 2.64/0.98  
% 2.64/0.98  fof(f64,plain,(
% 2.64/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/0.98    inference(cnf_transformation,[],[f27])).
% 2.64/0.98  
% 2.64/0.98  fof(f11,axiom,(
% 2.64/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f25,plain,(
% 2.64/0.98    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.64/0.98    inference(ennf_transformation,[],[f11])).
% 2.64/0.98  
% 2.64/0.98  fof(f26,plain,(
% 2.64/0.98    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.64/0.98    inference(flattening,[],[f25])).
% 2.64/0.98  
% 2.64/0.98  fof(f63,plain,(
% 2.64/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.64/0.98    inference(cnf_transformation,[],[f26])).
% 2.64/0.98  
% 2.64/0.98  fof(f94,plain,(
% 2.64/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.64/0.98    inference(definition_unfolding,[],[f63,f83,f83])).
% 2.64/0.98  
% 2.64/0.98  fof(f81,plain,(
% 2.64/0.98    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)),
% 2.64/0.98    inference(cnf_transformation,[],[f42])).
% 2.64/0.98  
% 2.64/0.98  fof(f95,plain,(
% 2.64/0.98    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 2.64/0.98    inference(definition_unfolding,[],[f81,f83,f83])).
% 2.64/0.98  
% 2.64/0.98  fof(f10,axiom,(
% 2.64/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.98  
% 2.64/0.98  fof(f61,plain,(
% 2.64/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.64/0.98    inference(cnf_transformation,[],[f10])).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3458,plain,
% 2.64/0.98      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 2.64/0.98      theory(equality) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4523,plain,
% 2.64/0.98      ( k2_relat_1(sK2) != X0_49
% 2.64/0.98      | k1_xboole_0 != X0_49
% 2.64/0.98      | k1_xboole_0 = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6929,plain,
% 2.64/0.98      ( k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k1_xboole_0 != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k1_xboole_0 = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4523]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6933,plain,
% 2.64/0.98      ( k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
% 2.64/0.98      | k1_xboole_0 != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
% 2.64/0.98      | k1_xboole_0 = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_6929]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4346,plain,
% 2.64/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_49
% 2.64/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
% 2.64/0.98      | k2_relat_1(sK2) != X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6930,plain,
% 2.64/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
% 2.64/0.98      | k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4346]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6932,plain,
% 2.64/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
% 2.64/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
% 2.64/0.98      | k2_relat_1(sK2) != k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_6930]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4336,plain,
% 2.64/0.98      ( X0_49 != X1_49
% 2.64/0.98      | k2_relat_1(sK2) != X1_49
% 2.64/0.98      | k2_relat_1(sK2) = X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4608,plain,
% 2.64/0.98      ( X0_49 != k2_relat_1(sK2)
% 2.64/0.98      | k2_relat_1(sK2) = X0_49
% 2.64/0.98      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4336]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6578,plain,
% 2.64/0.98      ( k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) != k2_relat_1(sK2)
% 2.64/0.98      | k2_relat_1(sK2) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4608]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6580,plain,
% 2.64/0.98      ( k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(sK2)
% 2.64/0.98      | k2_relat_1(sK2) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
% 2.64/0.98      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_6578]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3466,plain,
% 2.64/0.98      ( X0_49 != X1_49 | k2_relat_1(X0_49) = k2_relat_1(X1_49) ),
% 2.64/0.98      theory(equality) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4903,plain,
% 2.64/0.98      ( X0_49 != sK2 | k2_relat_1(X0_49) = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3466]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6483,plain,
% 2.64/0.98      ( k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X1_50,X2_50)) != sK2
% 2.64/0.98      | k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X1_50,X2_50))) = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4903]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6489,plain,
% 2.64/0.98      ( k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) != sK2
% 2.64/0.98      | k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_6483]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3463,plain,
% 2.64/0.98      ( X0_49 != X1_49 | k1_relat_1(X0_49) = k1_relat_1(X1_49) ),
% 2.64/0.98      theory(equality) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5597,plain,
% 2.64/0.98      ( X0_49 != sK2 | k1_relat_1(X0_49) = k1_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3463]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5599,plain,
% 2.64/0.98      ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK2) | k1_xboole_0 != sK2 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_5597]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4329,plain,
% 2.64/0.98      ( X0_49 != X1_49
% 2.64/0.98      | k1_relat_1(sK2) != X1_49
% 2.64/0.98      | k1_relat_1(sK2) = X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4602,plain,
% 2.64/0.98      ( X0_49 != k1_relat_1(sK2)
% 2.64/0.98      | k1_relat_1(sK2) = X0_49
% 2.64/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4329]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5596,plain,
% 2.64/0.98      ( k1_relat_1(X0_49) != k1_relat_1(sK2)
% 2.64/0.98      | k1_relat_1(sK2) = k1_relat_1(X0_49)
% 2.64/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4602]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5598,plain,
% 2.64/0.98      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.64/0.98      | k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
% 2.64/0.98      | k1_relat_1(k1_xboole_0) != k1_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_5596]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_12,plain,
% 2.64/0.98      ( v4_relat_1(X0,X1)
% 2.64/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.64/0.98      | ~ v1_relat_1(X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_14,plain,
% 2.64/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.64/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_389,plain,
% 2.64/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.64/0.98      | ~ v1_relat_1(X0)
% 2.64/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.64/0.98      inference(resolution,[status(thm)],[c_12,c_14]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3433,plain,
% 2.64/0.98      ( ~ r1_tarski(k1_relat_1(X0_49),X1_49)
% 2.64/0.98      | ~ v1_relat_1(X0_49)
% 2.64/0.98      | k7_relat_1(X0_49,X1_49) = X0_49 ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_389]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4234,plain,
% 2.64/0.98      ( ~ r1_tarski(k1_relat_1(sK2),X0_49)
% 2.64/0.98      | ~ v1_relat_1(sK2)
% 2.64/0.98      | k7_relat_1(sK2,X0_49) = sK2 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3433]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5504,plain,
% 2.64/0.98      ( ~ r1_tarski(k1_relat_1(sK2),k2_enumset1(X0_50,X0_50,X1_50,X2_50))
% 2.64/0.98      | ~ v1_relat_1(sK2)
% 2.64/0.98      | k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X1_50,X2_50)) = sK2 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4234]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5508,plain,
% 2.64/0.98      ( ~ r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
% 2.64/0.98      | ~ v1_relat_1(sK2)
% 2.64/0.98      | k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = sK2 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_5504]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_11,plain,
% 2.64/0.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.64/0.98      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.64/0.98      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.64/0.98      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.64/0.98      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.64/0.98      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.64/0.98      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.64/0.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.64/0.98      | k1_xboole_0 = X0 ),
% 2.64/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3439,plain,
% 2.64/0.98      ( ~ r1_tarski(X0_49,k2_enumset1(X0_50,X0_50,X1_50,X2_50))
% 2.64/0.98      | k2_enumset1(X1_50,X1_50,X1_50,X2_50) = X0_49
% 2.64/0.98      | k2_enumset1(X2_50,X2_50,X2_50,X2_50) = X0_49
% 2.64/0.98      | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = X0_49
% 2.64/0.98      | k2_enumset1(X0_50,X0_50,X1_50,X2_50) = X0_49
% 2.64/0.98      | k2_enumset1(X0_50,X0_50,X0_50,X2_50) = X0_49
% 2.64/0.98      | k2_enumset1(X0_50,X0_50,X0_50,X1_50) = X0_49
% 2.64/0.98      | k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_49
% 2.64/0.98      | k1_xboole_0 = X0_49 ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4386,plain,
% 2.64/0.98      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(X1_50,X1_50,X2_50,X3_50))
% 2.64/0.98      | k2_enumset1(X2_50,X2_50,X2_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_enumset1(X3_50,X3_50,X3_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_enumset1(X2_50,X2_50,X2_50,X2_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_enumset1(X1_50,X1_50,X2_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_enumset1(X1_50,X1_50,X1_50,X3_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_enumset1(X1_50,X1_50,X1_50,X2_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3439]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5174,plain,
% 2.64/0.98      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)))
% 2.64/0.98      | k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50)))
% 2.64/0.98      | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4386]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5176,plain,
% 2.64/0.98      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)))
% 2.64/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))
% 2.64/0.98      | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_5174]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3460,plain,
% 2.64/0.98      ( ~ v1_xboole_0(X0_49) | v1_xboole_0(X1_49) | X1_49 != X0_49 ),
% 2.64/0.98      theory(equality) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5001,plain,
% 2.64/0.98      ( ~ v1_xboole_0(X0_49)
% 2.64/0.98      | v1_xboole_0(k2_relat_1(sK2))
% 2.64/0.98      | k2_relat_1(sK2) != X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3460]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5003,plain,
% 2.64/0.98      ( v1_xboole_0(k2_relat_1(sK2))
% 2.64/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.64/0.98      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_5001]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_34,negated_conjecture,
% 2.64/0.98      ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 2.64/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_26,plain,
% 2.64/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.64/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.64/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.64/0.98      inference(cnf_transformation,[],[f110]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_28,plain,
% 2.64/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.64/0.98      | ~ v1_funct_1(X0)
% 2.64/0.98      | ~ v1_relat_1(X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_35,negated_conjecture,
% 2.64/0.98      ( v1_funct_1(sK2) ),
% 2.64/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_358,plain,
% 2.64/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.64/0.98      | ~ v1_relat_1(X0)
% 2.64/0.98      | sK2 != X0 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_359,plain,
% 2.64/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.64/0.98      | ~ v1_relat_1(sK2) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_358]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_746,plain,
% 2.64/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.64/0.98      | ~ v1_relat_1(sK2)
% 2.64/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))
% 2.64/0.98      | sK2 != X0 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_359]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_747,plain,
% 2.64/0.98      ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
% 2.64/0.98      | ~ v1_relat_1(sK2)
% 2.64/0.98      | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_746]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1615,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
% 2.64/0.98      | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 2.64/0.98      | sK1 != X0
% 2.64/0.98      | sK2 != sK2 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_747]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1616,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
% 2.64/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_1615]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3423,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 2.64/0.98      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
% 2.64/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0 ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_1616]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3913,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 2.64/0.98      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
% 2.64/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.64/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_3423]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_0,plain,
% 2.64/0.98      ( v1_xboole_0(o_0_0_xboole_0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_2,plain,
% 2.64/0.98      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 2.64/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3448,plain,
% 2.64/0.98      ( ~ v1_xboole_0(k2_enumset1(X0_50,X0_50,X0_50,X0_50)) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3492,plain,
% 2.64/0.98      ( ~ v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3448]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4210,plain,
% 2.64/0.98      ( v1_xboole_0(X0_49)
% 2.64/0.98      | ~ v1_xboole_0(o_0_0_xboole_0)
% 2.64/0.98      | X0_49 != o_0_0_xboole_0 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3460]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4217,plain,
% 2.64/0.98      ( v1_xboole_0(k1_xboole_0)
% 2.64/0.98      | ~ v1_xboole_0(o_0_0_xboole_0)
% 2.64/0.98      | k1_xboole_0 != o_0_0_xboole_0 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4210]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3450,plain,
% 2.64/0.98      ( v1_xboole_0(o_0_0_xboole_0) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3892,plain,
% 2.64/0.98      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_3450]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1,plain,
% 2.64/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.64/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3449,plain,
% 2.64/0.98      ( ~ v1_xboole_0(X0_49) | k1_xboole_0 = X0_49 ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3893,plain,
% 2.64/0.98      ( k1_xboole_0 = X0_49 | v1_xboole_0(X0_49) != iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_3449]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4269,plain,
% 2.64/0.98      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 2.64/0.98      inference(superposition,[status(thm)],[c_3892,c_3893]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4371,plain,
% 2.64/0.98      ( ~ v1_xboole_0(X0_49)
% 2.64/0.98      | v1_xboole_0(k2_enumset1(X0_50,X0_50,X0_50,X0_50))
% 2.64/0.98      | k2_enumset1(X0_50,X0_50,X0_50,X0_50) != X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3460]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4373,plain,
% 2.64/0.98      ( v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
% 2.64/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.64/0.98      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4371]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4980,plain,
% 2.64/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0 ),
% 2.64/0.98      inference(global_propositional_subsumption,
% 2.64/0.98                [status(thm)],
% 2.64/0.98                [c_3913,c_0,c_3492,c_4217,c_4269,c_4373]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_20,plain,
% 2.64/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_33,negated_conjecture,
% 2.64/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.64/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_512,plain,
% 2.64/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.98      | sK2 != X2 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_513,plain,
% 2.64/0.98      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_512]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3431,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.64/0.98      | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_513]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4140,plain,
% 2.64/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
% 2.64/0.98      inference(equality_resolution,[status(thm)],[c_3431]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_27,plain,
% 2.64/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.64/0.98      | k1_xboole_0 = X2 ),
% 2.64/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_548,plain,
% 2.64/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/0.98      | ~ v1_relat_1(sK2)
% 2.64/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.64/0.98      | sK2 != X0
% 2.64/0.98      | k1_xboole_0 = X2 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_359]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_549,plain,
% 2.64/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.64/0.98      | ~ v1_relat_1(sK2)
% 2.64/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.98      | k1_xboole_0 = X1 ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_548]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1555,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | k2_enumset1(sK0,sK0,sK0,sK0) != X0
% 2.64/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.98      | sK1 != X1
% 2.64/0.98      | sK2 != sK2
% 2.64/0.98      | k1_xboole_0 = X1 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_549]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1556,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.64/0.98      | k1_xboole_0 = sK1 ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_1555]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_32,negated_conjecture,
% 2.64/0.98      ( k1_xboole_0 != sK1 ),
% 2.64/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1558,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.64/0.98      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.64/0.98      | ~ v1_relat_1(sK2) ),
% 2.64/0.98      inference(global_propositional_subsumption,
% 2.64/0.98                [status(thm)],
% 2.64/0.98                [c_1556,c_32]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1559,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.98      inference(renaming,[status(thm)],[c_1558]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_467,plain,
% 2.64/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.64/0.98      | sK2 != X0
% 2.64/0.98      | k1_xboole_0 = X2 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_468,plain,
% 2.64/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.64/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.98      | k1_xboole_0 = X1 ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_467]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1572,plain,
% 2.64/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
% 2.64/0.98      | k1_relset_1(X0,X1,sK2) = X0
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.98      | sK1 != X1
% 2.64/0.98      | sK2 != sK2
% 2.64/0.98      | k1_xboole_0 = X1 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_468]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1573,plain,
% 2.64/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.64/0.98      | k1_xboole_0 = sK1 ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_1572]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1574,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.64/0.98      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.64/0.98      inference(global_propositional_subsumption,
% 2.64/0.98                [status(thm)],
% 2.64/0.98                [c_1573,c_32]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1575,plain,
% 2.64/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.98      inference(renaming,[status(thm)],[c_1574]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1984,plain,
% 2.64/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.64/0.98      inference(equality_resolution_simp,[status(thm)],[c_1575]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1986,plain,
% 2.64/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.64/0.98      inference(global_propositional_subsumption,
% 2.64/0.98                [status(thm)],
% 2.64/0.98                [c_1559,c_1984]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3417,plain,
% 2.64/0.98      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_1986]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4172,plain,
% 2.64/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
% 2.64/0.98      inference(demodulation,[status(thm)],[c_4140,c_3417]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4982,plain,
% 2.64/0.98      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 2.64/0.98      inference(light_normalisation,[status(thm)],[c_4980,c_4172]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4,plain,
% 2.64/0.98      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X2,X1)) ),
% 2.64/0.98      inference(cnf_transformation,[],[f99]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3446,plain,
% 2.64/0.98      ( r1_tarski(k2_enumset1(X0_50,X0_50,X0_50,X1_50),k2_enumset1(X0_50,X0_50,X2_50,X1_50)) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3896,plain,
% 2.64/0.98      ( r1_tarski(k2_enumset1(X0_50,X0_50,X0_50,X1_50),k2_enumset1(X0_50,X0_50,X2_50,X1_50)) = iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_3446]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4750,plain,
% 2.64/0.98      ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,X0_50,sK0)) = iProver_top ),
% 2.64/0.98      inference(superposition,[status(thm)],[c_4172,c_3896]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4756,plain,
% 2.64/0.98      ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,X0_50,sK0)) ),
% 2.64/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4750]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4758,plain,
% 2.64/0.98      ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4756]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_19,plain,
% 2.64/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/0.98      | ~ v1_xboole_0(X2)
% 2.64/0.98      | v1_xboole_0(X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_620,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | ~ v1_xboole_0(X0)
% 2.64/0.98      | v1_xboole_0(X1)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X0))
% 2.64/0.98      | sK2 != X1 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_359]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_621,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | ~ v1_xboole_0(X0)
% 2.64/0.98      | v1_xboole_0(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_620]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3426,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2)
% 2.64/0.98      | ~ v1_xboole_0(X0_49)
% 2.64/0.98      | v1_xboole_0(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_621]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3451,plain,
% 2.64/0.98      ( ~ v1_xboole_0(X0_49)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))
% 2.64/0.98      | ~ sP0_iProver_split ),
% 2.64/0.98      inference(splitting,
% 2.64/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.64/0.98                [c_3426]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4740,plain,
% 2.64/0.98      ( ~ v1_xboole_0(k2_relat_1(sK2))
% 2.64/0.98      | ~ sP0_iProver_split
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3451]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4536,plain,
% 2.64/0.98      ( k1_relat_1(X0_49) != X1_49
% 2.64/0.98      | k1_xboole_0 != X1_49
% 2.64/0.98      | k1_xboole_0 = k1_relat_1(X0_49) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4537,plain,
% 2.64/0.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.64/0.98      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.64/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4536]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4436,plain,
% 2.64/0.98      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3449]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3454,plain,( X0_49 = X0_49 ),theory(equality) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4335,plain,
% 2.64/0.98      ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3454]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4159,plain,
% 2.64/0.98      ( k2_relat_1(sK2) != X0_49
% 2.64/0.98      | k2_relat_1(sK2) = k1_xboole_0
% 2.64/0.98      | k1_xboole_0 != X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4334,plain,
% 2.64/0.98      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 2.64/0.98      | k2_relat_1(sK2) = k1_xboole_0
% 2.64/0.98      | k1_xboole_0 != k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4159]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4158,plain,
% 2.64/0.98      ( k1_relat_1(sK2) != X0_49
% 2.64/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 2.64/0.98      | k1_xboole_0 != X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4330,plain,
% 2.64/0.98      ( k1_relat_1(sK2) != k1_relat_1(X0_49)
% 2.64/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 2.64/0.98      | k1_xboole_0 != k1_relat_1(X0_49) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4158]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4332,plain,
% 2.64/0.98      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 2.64/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 2.64/0.98      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4330]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4328,plain,
% 2.64/0.98      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3454]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3456,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4306,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3456]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4164,plain,
% 2.64/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_49
% 2.64/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 2.64/0.98      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0_49 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4230,plain,
% 2.64/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 2.64/0.98      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.64/0.98      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_4164]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_21,plain,
% 2.64/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_503,plain,
% 2.64/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.98      | sK2 != X2 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_504,plain,
% 2.64/0.98      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_503]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3432,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.64/0.98      | k2_relset_1(X0_49,X1_49,sK2) = k2_relat_1(sK2) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_504]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4145,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.64/0.98      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3432]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_18,plain,
% 2.64/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/0.98      | v1_relat_1(X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_536,plain,
% 2.64/0.98      ( v1_relat_1(X0)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.64/0.98      | sK2 != X0 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_537,plain,
% 2.64/0.98      ( v1_relat_1(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_536]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3429,plain,
% 2.64/0.98      ( v1_relat_1(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_537]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4147,plain,
% 2.64/0.98      ( v1_relat_1(sK2)
% 2.64/0.98      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3429]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4144,plain,
% 2.64/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3456]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3452,plain,
% 2.64/0.98      ( ~ v1_relat_1(sK2) | v1_xboole_0(sK2) | sP0_iProver_split ),
% 2.64/0.98      inference(splitting,
% 2.64/0.98                [splitting(split),new_symbols(definition,[])],
% 2.64/0.98                [c_3426]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_17,plain,
% 2.64/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
% 2.64/0.98      | ~ v1_funct_1(X0)
% 2.64/0.98      | ~ v1_relat_1(X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_368,plain,
% 2.64/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
% 2.64/0.98      | ~ v1_relat_1(X0)
% 2.64/0.98      | sK2 != X0 ),
% 2.64/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_369,plain,
% 2.64/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)))
% 2.64/0.98      | ~ v1_relat_1(sK2) ),
% 2.64/0.98      inference(unflattening,[status(thm)],[c_368]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3434,plain,
% 2.64/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50),k1_funct_1(sK2,X0_50)))
% 2.64/0.98      | ~ v1_relat_1(sK2) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_369]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3508,plain,
% 2.64/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)))
% 2.64/0.98      | ~ v1_relat_1(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3434]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_31,negated_conjecture,
% 2.64/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 2.64/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3436,negated_conjecture,
% 2.64/0.98      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_31]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_16,plain,
% 2.64/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3437,plain,
% 2.64/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3485,plain,
% 2.64/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_3454]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(contradiction,plain,
% 2.64/0.98      ( $false ),
% 2.64/0.98      inference(minisat,
% 2.64/0.98                [status(thm)],
% 2.64/0.98                [c_6933,c_6932,c_6580,c_6489,c_5599,c_5598,c_5508,c_5176,
% 2.64/0.98                 c_5003,c_4982,c_4758,c_4740,c_4537,c_4436,c_4335,c_4334,
% 2.64/0.98                 c_4332,c_4328,c_4306,c_4269,c_4230,c_4217,c_4145,c_4147,
% 2.64/0.98                 c_4144,c_3452,c_3508,c_3436,c_3437,c_3485,c_0]) ).
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/0.98  
% 2.64/0.98  ------                               Statistics
% 2.64/0.98  
% 2.64/0.98  ------ General
% 2.64/0.98  
% 2.64/0.98  abstr_ref_over_cycles:                  0
% 2.64/0.98  abstr_ref_under_cycles:                 0
% 2.64/0.98  gc_basic_clause_elim:                   0
% 2.64/0.98  forced_gc_time:                         0
% 2.64/0.98  parsing_time:                           0.009
% 2.64/0.98  unif_index_cands_time:                  0.
% 2.64/0.98  unif_index_add_time:                    0.
% 2.64/0.98  orderings_time:                         0.
% 2.64/0.98  out_proof_time:                         0.011
% 2.64/0.98  total_time:                             0.218
% 2.64/0.98  num_of_symbols:                         57
% 2.64/0.98  num_of_terms:                           5250
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing
% 2.64/0.98  
% 2.64/0.98  num_of_splits:                          1
% 2.64/0.98  num_of_split_atoms:                     1
% 2.64/0.98  num_of_reused_defs:                     0
% 2.64/0.98  num_eq_ax_congr_red:                    6
% 2.64/0.98  num_of_sem_filtered_clauses:            1
% 2.64/0.98  num_of_subtypes:                        4
% 2.64/0.98  monotx_restored_types:                  0
% 2.64/0.98  sat_num_of_epr_types:                   0
% 2.64/0.98  sat_num_of_non_cyclic_types:            0
% 2.64/0.98  sat_guarded_non_collapsed_types:        1
% 2.64/0.98  num_pure_diseq_elim:                    0
% 2.64/0.98  simp_replaced_by:                       0
% 2.64/0.98  res_preprocessed:                       210
% 2.64/0.98  prep_upred:                             0
% 2.64/0.98  prep_unflattend:                        150
% 2.64/0.98  smt_new_axioms:                         0
% 2.64/0.98  pred_elim_cands:                        3
% 2.64/0.98  pred_elim:                              4
% 2.64/0.98  pred_elim_cl:                           0
% 2.64/0.98  pred_elim_cycles:                       12
% 2.64/0.98  merged_defs:                            0
% 2.64/0.98  merged_defs_ncl:                        0
% 2.64/0.98  bin_hyper_res:                          0
% 2.64/0.98  prep_cycles:                            5
% 2.64/0.98  pred_elim_time:                         0.058
% 2.64/0.98  splitting_time:                         0.
% 2.64/0.98  sem_filter_time:                        0.
% 2.64/0.98  monotx_time:                            0.
% 2.64/0.98  subtype_inf_time:                       0.
% 2.64/0.98  
% 2.64/0.98  ------ Problem properties
% 2.64/0.98  
% 2.64/0.98  clauses:                                35
% 2.64/0.98  conjectures:                            2
% 2.64/0.98  epr:                                    4
% 2.64/0.98  horn:                                   29
% 2.64/0.98  ground:                                 15
% 2.64/0.98  unary:                                  15
% 2.64/0.98  binary:                                 5
% 2.64/0.98  lits:                                   84
% 2.64/0.98  lits_eq:                                54
% 2.64/0.98  fd_pure:                                0
% 2.64/0.98  fd_pseudo:                              0
% 2.64/0.98  fd_cond:                                1
% 2.64/0.98  fd_pseudo_cond:                         1
% 2.64/0.98  ac_symbols:                             0
% 2.64/0.98  
% 2.64/0.98  ------ Propositional Solver
% 2.64/0.98  
% 2.64/0.98  prop_solver_calls:                      32
% 2.64/0.98  prop_fast_solver_calls:                 1737
% 2.64/0.98  smt_solver_calls:                       0
% 2.64/0.98  smt_fast_solver_calls:                  0
% 2.64/0.98  prop_num_of_clauses:                    1442
% 2.64/0.98  prop_preprocess_simplified:             7009
% 2.64/0.98  prop_fo_subsumed:                       31
% 2.64/0.98  prop_solver_time:                       0.
% 2.64/0.98  smt_solver_time:                        0.
% 2.64/0.98  smt_fast_solver_time:                   0.
% 2.64/0.98  prop_fast_solver_time:                  0.
% 2.64/0.98  prop_unsat_core_time:                   0.
% 2.64/0.98  
% 2.64/0.98  ------ QBF
% 2.64/0.98  
% 2.64/0.98  qbf_q_res:                              0
% 2.64/0.98  qbf_num_tautologies:                    0
% 2.64/0.98  qbf_prep_cycles:                        0
% 2.64/0.98  
% 2.64/0.98  ------ BMC1
% 2.64/0.98  
% 2.64/0.98  bmc1_current_bound:                     -1
% 2.64/0.98  bmc1_last_solved_bound:                 -1
% 2.64/0.98  bmc1_unsat_core_size:                   -1
% 2.64/0.98  bmc1_unsat_core_parents_size:           -1
% 2.64/0.98  bmc1_merge_next_fun:                    0
% 2.64/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.64/0.98  
% 2.64/0.98  ------ Instantiation
% 2.64/0.98  
% 2.64/0.98  inst_num_of_clauses:                    504
% 2.64/0.98  inst_num_in_passive:                    172
% 2.64/0.98  inst_num_in_active:                     288
% 2.64/0.98  inst_num_in_unprocessed:                43
% 2.64/0.98  inst_num_of_loops:                      315
% 2.64/0.98  inst_num_of_learning_restarts:          0
% 2.64/0.98  inst_num_moves_active_passive:          23
% 2.64/0.98  inst_lit_activity:                      0
% 2.64/0.98  inst_lit_activity_moves:                0
% 2.64/0.98  inst_num_tautologies:                   0
% 2.64/0.98  inst_num_prop_implied:                  0
% 2.64/0.98  inst_num_existing_simplified:           0
% 2.64/0.98  inst_num_eq_res_simplified:             0
% 2.64/0.98  inst_num_child_elim:                    0
% 2.64/0.98  inst_num_of_dismatching_blockings:      409
% 2.64/0.98  inst_num_of_non_proper_insts:           539
% 2.64/0.98  inst_num_of_duplicates:                 0
% 2.64/0.98  inst_inst_num_from_inst_to_res:         0
% 2.64/0.98  inst_dismatching_checking_time:         0.
% 2.64/0.98  
% 2.64/0.98  ------ Resolution
% 2.64/0.98  
% 2.64/0.98  res_num_of_clauses:                     0
% 2.64/0.98  res_num_in_passive:                     0
% 2.64/0.98  res_num_in_active:                      0
% 2.64/0.98  res_num_of_loops:                       215
% 2.64/0.98  res_forward_subset_subsumed:            81
% 2.64/0.98  res_backward_subset_subsumed:           0
% 2.64/0.98  res_forward_subsumed:                   2
% 2.64/0.98  res_backward_subsumed:                  0
% 2.64/0.98  res_forward_subsumption_resolution:     2
% 2.64/0.98  res_backward_subsumption_resolution:    0
% 2.64/0.98  res_clause_to_clause_subsumption:       411
% 2.64/0.98  res_orphan_elimination:                 0
% 2.64/0.98  res_tautology_del:                      111
% 2.64/0.98  res_num_eq_res_simplified:              1
% 2.64/0.98  res_num_sel_changes:                    0
% 2.64/0.98  res_moves_from_active_to_pass:          0
% 2.64/0.98  
% 2.64/0.98  ------ Superposition
% 2.64/0.98  
% 2.64/0.98  sup_time_total:                         0.
% 2.64/0.98  sup_time_generating:                    0.
% 2.64/0.98  sup_time_sim_full:                      0.
% 2.64/0.98  sup_time_sim_immed:                     0.
% 2.64/0.98  
% 2.64/0.98  sup_num_of_clauses:                     68
% 2.64/0.98  sup_num_in_active:                      43
% 2.64/0.98  sup_num_in_passive:                     25
% 2.64/0.98  sup_num_of_loops:                       62
% 2.64/0.98  sup_fw_superposition:                   53
% 2.64/0.98  sup_bw_superposition:                   20
% 2.64/0.98  sup_immediate_simplified:               18
% 2.64/0.98  sup_given_eliminated:                   0
% 2.64/0.98  comparisons_done:                       0
% 2.64/0.98  comparisons_avoided:                    0
% 2.64/0.98  
% 2.64/0.98  ------ Simplifications
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  sim_fw_subset_subsumed:                 6
% 2.64/0.98  sim_bw_subset_subsumed:                 0
% 2.64/0.98  sim_fw_subsumed:                        3
% 2.64/0.98  sim_bw_subsumed:                        4
% 2.64/0.98  sim_fw_subsumption_res:                 0
% 2.64/0.98  sim_bw_subsumption_res:                 1
% 2.64/0.98  sim_tautology_del:                      0
% 2.64/0.98  sim_eq_tautology_del:                   9
% 2.64/0.98  sim_eq_res_simp:                        0
% 2.64/0.98  sim_fw_demodulated:                     2
% 2.64/0.98  sim_bw_demodulated:                     19
% 2.64/0.98  sim_light_normalised:                   9
% 2.64/0.98  sim_joinable_taut:                      0
% 2.64/0.98  sim_joinable_simp:                      0
% 2.64/0.98  sim_ac_normalised:                      0
% 2.64/0.98  sim_smt_subsumption:                    0
% 2.64/0.98  
%------------------------------------------------------------------------------
