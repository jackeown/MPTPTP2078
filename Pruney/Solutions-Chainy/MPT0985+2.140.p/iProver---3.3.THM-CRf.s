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
% DateTime   : Thu Dec  3 12:02:48 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  235 (4638 expanded)
%              Number of clauses        :  161 (1780 expanded)
%              Number of leaves         :   21 ( 853 expanded)
%              Depth                    :   27
%              Number of atoms          :  692 (21409 expanded)
%              Number of equality atoms :  320 (4343 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f42])).

fof(f49,plain,
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

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f49])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1045,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2207,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_44083,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != X0
    | sK1 != X0
    | sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_44084,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | sK1 = k1_relat_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_44083])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37759,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_24109,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != X0
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_37758,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != k1_relat_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 != k1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_24109])).

cnf(c_9594,plain,
    ( X0 != X1
    | k2_relat_1(X2) != X1
    | k2_relat_1(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_21457,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != X0
    | k2_relat_1(k2_funct_1(sK2)) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_9594])).

cnf(c_21458,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21457])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2397,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK1)
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_17201,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),X0)
    | r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_17202,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17201])).

cnf(c_17204,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) = iProver_top
    | r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17202])).

cnf(c_17203,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_17201])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_667,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_669,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_33])).

cnf(c_1765,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1769,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2700,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1765,c_1769])).

cnf(c_2784,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_669,c_2700])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1773,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2424,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1773])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_263,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_325,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_264])).

cnf(c_1763,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_4737,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_1763])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1772,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4752,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4737,c_1772])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_456,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_457,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_459,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_35])).

cnf(c_1760,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_4757,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4752,c_1760])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3427,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1773])).

cnf(c_7946,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4757,c_3427])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1768,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2618,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1765,c_1768])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2620,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2618,c_31])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_442,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_443,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_445,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_35])).

cnf(c_1761,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_2693,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2620,c_1761])).

cnf(c_4756,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_4752,c_2693])).

cnf(c_8015,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7946,c_4756])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2039,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2040,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2039])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2042,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2043,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2042])).

cnf(c_11052,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8015,c_36,c_2040,c_2043,c_4752])).

cnf(c_11057,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2784,c_11052])).

cnf(c_1774,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_677,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_678,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_1750,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_4832,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4756,c_1750])).

cnf(c_5675,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4832])).

cnf(c_679,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_5677,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5675,c_36,c_679,c_2040,c_2043,c_2693,c_4752])).

cnf(c_5681,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5677,c_4757])).

cnf(c_5685,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2784,c_5681])).

cnf(c_5690,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_5685])).

cnf(c_11203,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11057,c_5690])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK0 != X1
    | sK1 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_554,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1756,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_11240,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11203,c_1756])).

cnf(c_11281,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11240])).

cnf(c_11246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11203,c_1765])).

cnf(c_11285,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11281,c_11246])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_10])).

cnf(c_1759,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_5102,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1759])).

cnf(c_5291,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5102,c_4752])).

cnf(c_12051,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11285,c_5291])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2082,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2085,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2082])).

cnf(c_2087,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_2432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_2435,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_2089,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2849,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2089])).

cnf(c_2854,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2849])).

cnf(c_2856,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2854])).

cnf(c_1046,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2449,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | X3 != X0 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_4224,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(sK2,k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_4225,plain,
    ( sK2 != X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4224])).

cnf(c_4227,plain,
    ( sK2 != k1_xboole_0
    | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4225])).

cnf(c_11518,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_11519,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11518])).

cnf(c_11521,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11519])).

cnf(c_12770,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12051,c_2087,c_2435,c_2856,c_4227,c_4752,c_11521])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1776,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1779,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3309,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1779])).

cnf(c_12782,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12770,c_3309])).

cnf(c_13019,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12782,c_4757])).

cnf(c_6636,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X1)
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_9598,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
    | ~ r1_tarski(k1_relat_1(sK2),X0)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6636])).

cnf(c_11549,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9598])).

cnf(c_11552,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11549])).

cnf(c_4834,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4756,c_1766])).

cnf(c_11428,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4834,c_36,c_2040,c_2043,c_4752])).

cnf(c_11432,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11428,c_4757,c_11203])).

cnf(c_11439,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11432,c_1759])).

cnf(c_11449,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11439])).

cnf(c_11227,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11203,c_4756])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7302,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7306,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7302])).

cnf(c_5127,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5102])).

cnf(c_4753,plain,
    ( v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4752])).

cnf(c_2787,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2790,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_2391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2391])).

cnf(c_2394,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_2393,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_1044,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2200,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_2079,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_2199,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_651,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_652,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_458,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44084,c_37759,c_37758,c_21458,c_17204,c_17203,c_13019,c_11552,c_11549,c_11449,c_11439,c_11227,c_11203,c_7306,c_7302,c_5127,c_5102,c_4753,c_4752,c_2790,c_2787,c_2693,c_2394,c_2393,c_2200,c_2199,c_2043,c_2042,c_2040,c_2039,c_678,c_652,c_458,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.11/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/1.49  
% 7.11/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.11/1.49  
% 7.11/1.49  ------  iProver source info
% 7.11/1.49  
% 7.11/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.11/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.11/1.49  git: non_committed_changes: false
% 7.11/1.49  git: last_make_outside_of_git: false
% 7.11/1.49  
% 7.11/1.49  ------ 
% 7.11/1.49  
% 7.11/1.49  ------ Input Options
% 7.11/1.49  
% 7.11/1.49  --out_options                           all
% 7.11/1.49  --tptp_safe_out                         true
% 7.11/1.49  --problem_path                          ""
% 7.11/1.49  --include_path                          ""
% 7.11/1.49  --clausifier                            res/vclausify_rel
% 7.11/1.49  --clausifier_options                    --mode clausify
% 7.11/1.49  --stdin                                 false
% 7.11/1.49  --stats_out                             all
% 7.11/1.49  
% 7.11/1.49  ------ General Options
% 7.11/1.49  
% 7.11/1.49  --fof                                   false
% 7.11/1.49  --time_out_real                         305.
% 7.11/1.49  --time_out_virtual                      -1.
% 7.11/1.49  --symbol_type_check                     false
% 7.11/1.49  --clausify_out                          false
% 7.11/1.49  --sig_cnt_out                           false
% 7.11/1.49  --trig_cnt_out                          false
% 7.11/1.49  --trig_cnt_out_tolerance                1.
% 7.11/1.49  --trig_cnt_out_sk_spl                   false
% 7.11/1.49  --abstr_cl_out                          false
% 7.11/1.49  
% 7.11/1.49  ------ Global Options
% 7.11/1.49  
% 7.11/1.49  --schedule                              default
% 7.11/1.49  --add_important_lit                     false
% 7.11/1.49  --prop_solver_per_cl                    1000
% 7.11/1.49  --min_unsat_core                        false
% 7.11/1.49  --soft_assumptions                      false
% 7.11/1.49  --soft_lemma_size                       3
% 7.11/1.49  --prop_impl_unit_size                   0
% 7.11/1.49  --prop_impl_unit                        []
% 7.11/1.49  --share_sel_clauses                     true
% 7.11/1.49  --reset_solvers                         false
% 7.11/1.49  --bc_imp_inh                            [conj_cone]
% 7.11/1.49  --conj_cone_tolerance                   3.
% 7.11/1.49  --extra_neg_conj                        none
% 7.11/1.49  --large_theory_mode                     true
% 7.11/1.49  --prolific_symb_bound                   200
% 7.11/1.49  --lt_threshold                          2000
% 7.11/1.49  --clause_weak_htbl                      true
% 7.11/1.49  --gc_record_bc_elim                     false
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing Options
% 7.11/1.49  
% 7.11/1.49  --preprocessing_flag                    true
% 7.11/1.49  --time_out_prep_mult                    0.1
% 7.11/1.49  --splitting_mode                        input
% 7.11/1.49  --splitting_grd                         true
% 7.11/1.49  --splitting_cvd                         false
% 7.11/1.49  --splitting_cvd_svl                     false
% 7.11/1.49  --splitting_nvd                         32
% 7.11/1.49  --sub_typing                            true
% 7.11/1.49  --prep_gs_sim                           true
% 7.11/1.49  --prep_unflatten                        true
% 7.11/1.49  --prep_res_sim                          true
% 7.11/1.49  --prep_upred                            true
% 7.11/1.49  --prep_sem_filter                       exhaustive
% 7.11/1.49  --prep_sem_filter_out                   false
% 7.11/1.49  --pred_elim                             true
% 7.11/1.49  --res_sim_input                         true
% 7.11/1.49  --eq_ax_congr_red                       true
% 7.11/1.49  --pure_diseq_elim                       true
% 7.11/1.49  --brand_transform                       false
% 7.11/1.49  --non_eq_to_eq                          false
% 7.11/1.49  --prep_def_merge                        true
% 7.11/1.49  --prep_def_merge_prop_impl              false
% 7.11/1.49  --prep_def_merge_mbd                    true
% 7.11/1.49  --prep_def_merge_tr_red                 false
% 7.11/1.49  --prep_def_merge_tr_cl                  false
% 7.11/1.49  --smt_preprocessing                     true
% 7.11/1.49  --smt_ac_axioms                         fast
% 7.11/1.49  --preprocessed_out                      false
% 7.11/1.49  --preprocessed_stats                    false
% 7.11/1.49  
% 7.11/1.49  ------ Abstraction refinement Options
% 7.11/1.49  
% 7.11/1.49  --abstr_ref                             []
% 7.11/1.49  --abstr_ref_prep                        false
% 7.11/1.49  --abstr_ref_until_sat                   false
% 7.11/1.49  --abstr_ref_sig_restrict                funpre
% 7.11/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.49  --abstr_ref_under                       []
% 7.11/1.49  
% 7.11/1.49  ------ SAT Options
% 7.11/1.49  
% 7.11/1.49  --sat_mode                              false
% 7.11/1.49  --sat_fm_restart_options                ""
% 7.11/1.49  --sat_gr_def                            false
% 7.11/1.49  --sat_epr_types                         true
% 7.11/1.49  --sat_non_cyclic_types                  false
% 7.11/1.49  --sat_finite_models                     false
% 7.11/1.49  --sat_fm_lemmas                         false
% 7.11/1.49  --sat_fm_prep                           false
% 7.11/1.49  --sat_fm_uc_incr                        true
% 7.11/1.49  --sat_out_model                         small
% 7.11/1.49  --sat_out_clauses                       false
% 7.11/1.49  
% 7.11/1.49  ------ QBF Options
% 7.11/1.49  
% 7.11/1.49  --qbf_mode                              false
% 7.11/1.49  --qbf_elim_univ                         false
% 7.11/1.49  --qbf_dom_inst                          none
% 7.11/1.49  --qbf_dom_pre_inst                      false
% 7.11/1.49  --qbf_sk_in                             false
% 7.11/1.49  --qbf_pred_elim                         true
% 7.11/1.49  --qbf_split                             512
% 7.11/1.49  
% 7.11/1.49  ------ BMC1 Options
% 7.11/1.49  
% 7.11/1.49  --bmc1_incremental                      false
% 7.11/1.49  --bmc1_axioms                           reachable_all
% 7.11/1.49  --bmc1_min_bound                        0
% 7.11/1.49  --bmc1_max_bound                        -1
% 7.11/1.49  --bmc1_max_bound_default                -1
% 7.11/1.49  --bmc1_symbol_reachability              true
% 7.11/1.49  --bmc1_property_lemmas                  false
% 7.11/1.49  --bmc1_k_induction                      false
% 7.11/1.49  --bmc1_non_equiv_states                 false
% 7.11/1.49  --bmc1_deadlock                         false
% 7.11/1.49  --bmc1_ucm                              false
% 7.11/1.49  --bmc1_add_unsat_core                   none
% 7.11/1.49  --bmc1_unsat_core_children              false
% 7.11/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.49  --bmc1_out_stat                         full
% 7.11/1.49  --bmc1_ground_init                      false
% 7.11/1.49  --bmc1_pre_inst_next_state              false
% 7.11/1.49  --bmc1_pre_inst_state                   false
% 7.11/1.49  --bmc1_pre_inst_reach_state             false
% 7.11/1.49  --bmc1_out_unsat_core                   false
% 7.11/1.49  --bmc1_aig_witness_out                  false
% 7.11/1.49  --bmc1_verbose                          false
% 7.11/1.49  --bmc1_dump_clauses_tptp                false
% 7.11/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.49  --bmc1_dump_file                        -
% 7.11/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.49  --bmc1_ucm_extend_mode                  1
% 7.11/1.49  --bmc1_ucm_init_mode                    2
% 7.11/1.49  --bmc1_ucm_cone_mode                    none
% 7.11/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.49  --bmc1_ucm_relax_model                  4
% 7.11/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.49  --bmc1_ucm_layered_model                none
% 7.11/1.49  --bmc1_ucm_max_lemma_size               10
% 7.11/1.49  
% 7.11/1.49  ------ AIG Options
% 7.11/1.49  
% 7.11/1.49  --aig_mode                              false
% 7.11/1.49  
% 7.11/1.49  ------ Instantiation Options
% 7.11/1.49  
% 7.11/1.49  --instantiation_flag                    true
% 7.11/1.49  --inst_sos_flag                         false
% 7.11/1.49  --inst_sos_phase                        true
% 7.11/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel_side                     num_symb
% 7.11/1.49  --inst_solver_per_active                1400
% 7.11/1.49  --inst_solver_calls_frac                1.
% 7.11/1.49  --inst_passive_queue_type               priority_queues
% 7.11/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.49  --inst_passive_queues_freq              [25;2]
% 7.11/1.49  --inst_dismatching                      true
% 7.11/1.49  --inst_eager_unprocessed_to_passive     true
% 7.11/1.49  --inst_prop_sim_given                   true
% 7.11/1.49  --inst_prop_sim_new                     false
% 7.11/1.49  --inst_subs_new                         false
% 7.11/1.49  --inst_eq_res_simp                      false
% 7.11/1.49  --inst_subs_given                       false
% 7.11/1.49  --inst_orphan_elimination               true
% 7.11/1.49  --inst_learning_loop_flag               true
% 7.11/1.49  --inst_learning_start                   3000
% 7.11/1.49  --inst_learning_factor                  2
% 7.11/1.49  --inst_start_prop_sim_after_learn       3
% 7.11/1.49  --inst_sel_renew                        solver
% 7.11/1.49  --inst_lit_activity_flag                true
% 7.11/1.49  --inst_restr_to_given                   false
% 7.11/1.49  --inst_activity_threshold               500
% 7.11/1.49  --inst_out_proof                        true
% 7.11/1.49  
% 7.11/1.49  ------ Resolution Options
% 7.11/1.49  
% 7.11/1.49  --resolution_flag                       true
% 7.11/1.49  --res_lit_sel                           adaptive
% 7.11/1.49  --res_lit_sel_side                      none
% 7.11/1.49  --res_ordering                          kbo
% 7.11/1.49  --res_to_prop_solver                    active
% 7.11/1.49  --res_prop_simpl_new                    false
% 7.11/1.49  --res_prop_simpl_given                  true
% 7.11/1.49  --res_passive_queue_type                priority_queues
% 7.11/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.49  --res_passive_queues_freq               [15;5]
% 7.11/1.49  --res_forward_subs                      full
% 7.11/1.49  --res_backward_subs                     full
% 7.11/1.49  --res_forward_subs_resolution           true
% 7.11/1.49  --res_backward_subs_resolution          true
% 7.11/1.49  --res_orphan_elimination                true
% 7.11/1.49  --res_time_limit                        2.
% 7.11/1.49  --res_out_proof                         true
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Options
% 7.11/1.49  
% 7.11/1.49  --superposition_flag                    true
% 7.11/1.49  --sup_passive_queue_type                priority_queues
% 7.11/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.49  --demod_completeness_check              fast
% 7.11/1.49  --demod_use_ground                      true
% 7.11/1.49  --sup_to_prop_solver                    passive
% 7.11/1.49  --sup_prop_simpl_new                    true
% 7.11/1.49  --sup_prop_simpl_given                  true
% 7.11/1.49  --sup_fun_splitting                     false
% 7.11/1.49  --sup_smt_interval                      50000
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Simplification Setup
% 7.11/1.49  
% 7.11/1.49  --sup_indices_passive                   []
% 7.11/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_full_bw                           [BwDemod]
% 7.11/1.49  --sup_immed_triv                        [TrivRules]
% 7.11/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_immed_bw_main                     []
% 7.11/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  
% 7.11/1.49  ------ Combination Options
% 7.11/1.49  
% 7.11/1.49  --comb_res_mult                         3
% 7.11/1.49  --comb_sup_mult                         2
% 7.11/1.49  --comb_inst_mult                        10
% 7.11/1.49  
% 7.11/1.49  ------ Debug Options
% 7.11/1.49  
% 7.11/1.49  --dbg_backtrace                         false
% 7.11/1.49  --dbg_dump_prop_clauses                 false
% 7.11/1.49  --dbg_dump_prop_clauses_file            -
% 7.11/1.49  --dbg_out_stat                          false
% 7.11/1.49  ------ Parsing...
% 7.11/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.11/1.49  ------ Proving...
% 7.11/1.49  ------ Problem Properties 
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  clauses                                 33
% 7.11/1.49  conjectures                             3
% 7.11/1.49  EPR                                     7
% 7.11/1.49  Horn                                    29
% 7.11/1.49  unary                                   7
% 7.11/1.49  binary                                  7
% 7.11/1.49  lits                                    95
% 7.11/1.49  lits eq                                 31
% 7.11/1.49  fd_pure                                 0
% 7.11/1.49  fd_pseudo                               0
% 7.11/1.49  fd_cond                                 1
% 7.11/1.49  fd_pseudo_cond                          1
% 7.11/1.49  AC symbols                              0
% 7.11/1.49  
% 7.11/1.49  ------ Schedule dynamic 5 is on 
% 7.11/1.49  
% 7.11/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  ------ 
% 7.11/1.49  Current options:
% 7.11/1.49  ------ 
% 7.11/1.49  
% 7.11/1.49  ------ Input Options
% 7.11/1.49  
% 7.11/1.49  --out_options                           all
% 7.11/1.49  --tptp_safe_out                         true
% 7.11/1.49  --problem_path                          ""
% 7.11/1.49  --include_path                          ""
% 7.11/1.49  --clausifier                            res/vclausify_rel
% 7.11/1.49  --clausifier_options                    --mode clausify
% 7.11/1.49  --stdin                                 false
% 7.11/1.49  --stats_out                             all
% 7.11/1.49  
% 7.11/1.49  ------ General Options
% 7.11/1.49  
% 7.11/1.49  --fof                                   false
% 7.11/1.49  --time_out_real                         305.
% 7.11/1.49  --time_out_virtual                      -1.
% 7.11/1.49  --symbol_type_check                     false
% 7.11/1.49  --clausify_out                          false
% 7.11/1.49  --sig_cnt_out                           false
% 7.11/1.49  --trig_cnt_out                          false
% 7.11/1.49  --trig_cnt_out_tolerance                1.
% 7.11/1.49  --trig_cnt_out_sk_spl                   false
% 7.11/1.49  --abstr_cl_out                          false
% 7.11/1.49  
% 7.11/1.49  ------ Global Options
% 7.11/1.49  
% 7.11/1.49  --schedule                              default
% 7.11/1.49  --add_important_lit                     false
% 7.11/1.49  --prop_solver_per_cl                    1000
% 7.11/1.49  --min_unsat_core                        false
% 7.11/1.49  --soft_assumptions                      false
% 7.11/1.49  --soft_lemma_size                       3
% 7.11/1.49  --prop_impl_unit_size                   0
% 7.11/1.49  --prop_impl_unit                        []
% 7.11/1.49  --share_sel_clauses                     true
% 7.11/1.49  --reset_solvers                         false
% 7.11/1.49  --bc_imp_inh                            [conj_cone]
% 7.11/1.49  --conj_cone_tolerance                   3.
% 7.11/1.49  --extra_neg_conj                        none
% 7.11/1.49  --large_theory_mode                     true
% 7.11/1.49  --prolific_symb_bound                   200
% 7.11/1.49  --lt_threshold                          2000
% 7.11/1.49  --clause_weak_htbl                      true
% 7.11/1.49  --gc_record_bc_elim                     false
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing Options
% 7.11/1.49  
% 7.11/1.49  --preprocessing_flag                    true
% 7.11/1.49  --time_out_prep_mult                    0.1
% 7.11/1.49  --splitting_mode                        input
% 7.11/1.49  --splitting_grd                         true
% 7.11/1.49  --splitting_cvd                         false
% 7.11/1.49  --splitting_cvd_svl                     false
% 7.11/1.49  --splitting_nvd                         32
% 7.11/1.49  --sub_typing                            true
% 7.11/1.49  --prep_gs_sim                           true
% 7.11/1.49  --prep_unflatten                        true
% 7.11/1.49  --prep_res_sim                          true
% 7.11/1.49  --prep_upred                            true
% 7.11/1.49  --prep_sem_filter                       exhaustive
% 7.11/1.49  --prep_sem_filter_out                   false
% 7.11/1.49  --pred_elim                             true
% 7.11/1.49  --res_sim_input                         true
% 7.11/1.49  --eq_ax_congr_red                       true
% 7.11/1.49  --pure_diseq_elim                       true
% 7.11/1.49  --brand_transform                       false
% 7.11/1.49  --non_eq_to_eq                          false
% 7.11/1.49  --prep_def_merge                        true
% 7.11/1.49  --prep_def_merge_prop_impl              false
% 7.11/1.49  --prep_def_merge_mbd                    true
% 7.11/1.49  --prep_def_merge_tr_red                 false
% 7.11/1.49  --prep_def_merge_tr_cl                  false
% 7.11/1.49  --smt_preprocessing                     true
% 7.11/1.49  --smt_ac_axioms                         fast
% 7.11/1.49  --preprocessed_out                      false
% 7.11/1.49  --preprocessed_stats                    false
% 7.11/1.49  
% 7.11/1.49  ------ Abstraction refinement Options
% 7.11/1.49  
% 7.11/1.49  --abstr_ref                             []
% 7.11/1.49  --abstr_ref_prep                        false
% 7.11/1.49  --abstr_ref_until_sat                   false
% 7.11/1.49  --abstr_ref_sig_restrict                funpre
% 7.11/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.49  --abstr_ref_under                       []
% 7.11/1.49  
% 7.11/1.49  ------ SAT Options
% 7.11/1.49  
% 7.11/1.49  --sat_mode                              false
% 7.11/1.49  --sat_fm_restart_options                ""
% 7.11/1.49  --sat_gr_def                            false
% 7.11/1.49  --sat_epr_types                         true
% 7.11/1.49  --sat_non_cyclic_types                  false
% 7.11/1.49  --sat_finite_models                     false
% 7.11/1.49  --sat_fm_lemmas                         false
% 7.11/1.49  --sat_fm_prep                           false
% 7.11/1.49  --sat_fm_uc_incr                        true
% 7.11/1.49  --sat_out_model                         small
% 7.11/1.49  --sat_out_clauses                       false
% 7.11/1.49  
% 7.11/1.49  ------ QBF Options
% 7.11/1.49  
% 7.11/1.49  --qbf_mode                              false
% 7.11/1.49  --qbf_elim_univ                         false
% 7.11/1.49  --qbf_dom_inst                          none
% 7.11/1.49  --qbf_dom_pre_inst                      false
% 7.11/1.49  --qbf_sk_in                             false
% 7.11/1.49  --qbf_pred_elim                         true
% 7.11/1.49  --qbf_split                             512
% 7.11/1.49  
% 7.11/1.49  ------ BMC1 Options
% 7.11/1.49  
% 7.11/1.49  --bmc1_incremental                      false
% 7.11/1.49  --bmc1_axioms                           reachable_all
% 7.11/1.49  --bmc1_min_bound                        0
% 7.11/1.49  --bmc1_max_bound                        -1
% 7.11/1.49  --bmc1_max_bound_default                -1
% 7.11/1.49  --bmc1_symbol_reachability              true
% 7.11/1.49  --bmc1_property_lemmas                  false
% 7.11/1.49  --bmc1_k_induction                      false
% 7.11/1.49  --bmc1_non_equiv_states                 false
% 7.11/1.49  --bmc1_deadlock                         false
% 7.11/1.49  --bmc1_ucm                              false
% 7.11/1.49  --bmc1_add_unsat_core                   none
% 7.11/1.49  --bmc1_unsat_core_children              false
% 7.11/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.49  --bmc1_out_stat                         full
% 7.11/1.49  --bmc1_ground_init                      false
% 7.11/1.49  --bmc1_pre_inst_next_state              false
% 7.11/1.49  --bmc1_pre_inst_state                   false
% 7.11/1.49  --bmc1_pre_inst_reach_state             false
% 7.11/1.49  --bmc1_out_unsat_core                   false
% 7.11/1.49  --bmc1_aig_witness_out                  false
% 7.11/1.49  --bmc1_verbose                          false
% 7.11/1.49  --bmc1_dump_clauses_tptp                false
% 7.11/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.49  --bmc1_dump_file                        -
% 7.11/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.49  --bmc1_ucm_extend_mode                  1
% 7.11/1.49  --bmc1_ucm_init_mode                    2
% 7.11/1.49  --bmc1_ucm_cone_mode                    none
% 7.11/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.49  --bmc1_ucm_relax_model                  4
% 7.11/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.49  --bmc1_ucm_layered_model                none
% 7.11/1.49  --bmc1_ucm_max_lemma_size               10
% 7.11/1.49  
% 7.11/1.49  ------ AIG Options
% 7.11/1.49  
% 7.11/1.49  --aig_mode                              false
% 7.11/1.49  
% 7.11/1.49  ------ Instantiation Options
% 7.11/1.49  
% 7.11/1.49  --instantiation_flag                    true
% 7.11/1.49  --inst_sos_flag                         false
% 7.11/1.49  --inst_sos_phase                        true
% 7.11/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel_side                     none
% 7.11/1.49  --inst_solver_per_active                1400
% 7.11/1.49  --inst_solver_calls_frac                1.
% 7.11/1.49  --inst_passive_queue_type               priority_queues
% 7.11/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.49  --inst_passive_queues_freq              [25;2]
% 7.11/1.49  --inst_dismatching                      true
% 7.11/1.49  --inst_eager_unprocessed_to_passive     true
% 7.11/1.49  --inst_prop_sim_given                   true
% 7.11/1.49  --inst_prop_sim_new                     false
% 7.11/1.49  --inst_subs_new                         false
% 7.11/1.49  --inst_eq_res_simp                      false
% 7.11/1.49  --inst_subs_given                       false
% 7.11/1.49  --inst_orphan_elimination               true
% 7.11/1.49  --inst_learning_loop_flag               true
% 7.11/1.49  --inst_learning_start                   3000
% 7.11/1.49  --inst_learning_factor                  2
% 7.11/1.49  --inst_start_prop_sim_after_learn       3
% 7.11/1.49  --inst_sel_renew                        solver
% 7.11/1.49  --inst_lit_activity_flag                true
% 7.11/1.49  --inst_restr_to_given                   false
% 7.11/1.49  --inst_activity_threshold               500
% 7.11/1.49  --inst_out_proof                        true
% 7.11/1.49  
% 7.11/1.49  ------ Resolution Options
% 7.11/1.49  
% 7.11/1.49  --resolution_flag                       false
% 7.11/1.49  --res_lit_sel                           adaptive
% 7.11/1.49  --res_lit_sel_side                      none
% 7.11/1.49  --res_ordering                          kbo
% 7.11/1.49  --res_to_prop_solver                    active
% 7.11/1.49  --res_prop_simpl_new                    false
% 7.11/1.49  --res_prop_simpl_given                  true
% 7.11/1.49  --res_passive_queue_type                priority_queues
% 7.11/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.49  --res_passive_queues_freq               [15;5]
% 7.11/1.49  --res_forward_subs                      full
% 7.11/1.49  --res_backward_subs                     full
% 7.11/1.49  --res_forward_subs_resolution           true
% 7.11/1.49  --res_backward_subs_resolution          true
% 7.11/1.49  --res_orphan_elimination                true
% 7.11/1.49  --res_time_limit                        2.
% 7.11/1.49  --res_out_proof                         true
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Options
% 7.11/1.49  
% 7.11/1.49  --superposition_flag                    true
% 7.11/1.49  --sup_passive_queue_type                priority_queues
% 7.11/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.49  --demod_completeness_check              fast
% 7.11/1.49  --demod_use_ground                      true
% 7.11/1.49  --sup_to_prop_solver                    passive
% 7.11/1.49  --sup_prop_simpl_new                    true
% 7.11/1.49  --sup_prop_simpl_given                  true
% 7.11/1.49  --sup_fun_splitting                     false
% 7.11/1.49  --sup_smt_interval                      50000
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Simplification Setup
% 7.11/1.49  
% 7.11/1.49  --sup_indices_passive                   []
% 7.11/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_full_bw                           [BwDemod]
% 7.11/1.49  --sup_immed_triv                        [TrivRules]
% 7.11/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_immed_bw_main                     []
% 7.11/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  
% 7.11/1.49  ------ Combination Options
% 7.11/1.49  
% 7.11/1.49  --comb_res_mult                         3
% 7.11/1.49  --comb_sup_mult                         2
% 7.11/1.49  --comb_inst_mult                        10
% 7.11/1.49  
% 7.11/1.49  ------ Debug Options
% 7.11/1.49  
% 7.11/1.49  --dbg_backtrace                         false
% 7.11/1.49  --dbg_dump_prop_clauses                 false
% 7.11/1.49  --dbg_dump_prop_clauses_file            -
% 7.11/1.49  --dbg_out_stat                          false
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  ------ Proving...
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  % SZS status Theorem for theBenchmark.p
% 7.11/1.49  
% 7.11/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.11/1.49  
% 7.11/1.49  fof(f14,axiom,(
% 7.11/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f34,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.49    inference(ennf_transformation,[],[f14])).
% 7.11/1.49  
% 7.11/1.49  fof(f69,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f34])).
% 7.11/1.49  
% 7.11/1.49  fof(f2,axiom,(
% 7.11/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f23,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.11/1.49    inference(ennf_transformation,[],[f2])).
% 7.11/1.49  
% 7.11/1.49  fof(f24,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.11/1.49    inference(flattening,[],[f23])).
% 7.11/1.49  
% 7.11/1.49  fof(f54,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f24])).
% 7.11/1.49  
% 7.11/1.49  fof(f17,axiom,(
% 7.11/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f38,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.49    inference(ennf_transformation,[],[f17])).
% 7.11/1.49  
% 7.11/1.49  fof(f39,plain,(
% 7.11/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.49    inference(flattening,[],[f38])).
% 7.11/1.49  
% 7.11/1.49  fof(f48,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.49    inference(nnf_transformation,[],[f39])).
% 7.11/1.49  
% 7.11/1.49  fof(f72,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f48])).
% 7.11/1.49  
% 7.11/1.49  fof(f19,conjecture,(
% 7.11/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f20,negated_conjecture,(
% 7.11/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.11/1.49    inference(negated_conjecture,[],[f19])).
% 7.11/1.49  
% 7.11/1.49  fof(f42,plain,(
% 7.11/1.49    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.11/1.49    inference(ennf_transformation,[],[f20])).
% 7.11/1.49  
% 7.11/1.49  fof(f43,plain,(
% 7.11/1.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.11/1.49    inference(flattening,[],[f42])).
% 7.11/1.49  
% 7.11/1.49  fof(f49,plain,(
% 7.11/1.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.11/1.49    introduced(choice_axiom,[])).
% 7.11/1.49  
% 7.11/1.49  fof(f50,plain,(
% 7.11/1.49    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.11/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f49])).
% 7.11/1.49  
% 7.11/1.49  fof(f82,plain,(
% 7.11/1.49    v1_funct_2(sK2,sK0,sK1)),
% 7.11/1.49    inference(cnf_transformation,[],[f50])).
% 7.11/1.49  
% 7.11/1.49  fof(f83,plain,(
% 7.11/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.11/1.49    inference(cnf_transformation,[],[f50])).
% 7.11/1.49  
% 7.11/1.49  fof(f5,axiom,(
% 7.11/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f46,plain,(
% 7.11/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.11/1.49    inference(nnf_transformation,[],[f5])).
% 7.11/1.49  
% 7.11/1.49  fof(f57,plain,(
% 7.11/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f46])).
% 7.11/1.49  
% 7.11/1.49  fof(f7,axiom,(
% 7.11/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f25,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.11/1.49    inference(ennf_transformation,[],[f7])).
% 7.11/1.49  
% 7.11/1.49  fof(f59,plain,(
% 7.11/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f25])).
% 7.11/1.49  
% 7.11/1.49  fof(f58,plain,(
% 7.11/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f46])).
% 7.11/1.49  
% 7.11/1.49  fof(f9,axiom,(
% 7.11/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f62,plain,(
% 7.11/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f9])).
% 7.11/1.49  
% 7.11/1.49  fof(f12,axiom,(
% 7.11/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f31,plain,(
% 7.11/1.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.11/1.49    inference(ennf_transformation,[],[f12])).
% 7.11/1.49  
% 7.11/1.49  fof(f32,plain,(
% 7.11/1.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.11/1.49    inference(flattening,[],[f31])).
% 7.11/1.49  
% 7.11/1.49  fof(f67,plain,(
% 7.11/1.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f32])).
% 7.11/1.49  
% 7.11/1.49  fof(f84,plain,(
% 7.11/1.49    v2_funct_1(sK2)),
% 7.11/1.49    inference(cnf_transformation,[],[f50])).
% 7.11/1.49  
% 7.11/1.49  fof(f81,plain,(
% 7.11/1.49    v1_funct_1(sK2)),
% 7.11/1.49    inference(cnf_transformation,[],[f50])).
% 7.11/1.49  
% 7.11/1.49  fof(f18,axiom,(
% 7.11/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f40,plain,(
% 7.11/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.11/1.49    inference(ennf_transformation,[],[f18])).
% 7.11/1.49  
% 7.11/1.49  fof(f41,plain,(
% 7.11/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.11/1.49    inference(flattening,[],[f40])).
% 7.11/1.49  
% 7.11/1.49  fof(f80,plain,(
% 7.11/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f41])).
% 7.11/1.49  
% 7.11/1.49  fof(f15,axiom,(
% 7.11/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f35,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.49    inference(ennf_transformation,[],[f15])).
% 7.11/1.49  
% 7.11/1.49  fof(f70,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f35])).
% 7.11/1.49  
% 7.11/1.49  fof(f85,plain,(
% 7.11/1.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.11/1.49    inference(cnf_transformation,[],[f50])).
% 7.11/1.49  
% 7.11/1.49  fof(f66,plain,(
% 7.11/1.49    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f32])).
% 7.11/1.49  
% 7.11/1.49  fof(f11,axiom,(
% 7.11/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f29,plain,(
% 7.11/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.11/1.49    inference(ennf_transformation,[],[f11])).
% 7.11/1.49  
% 7.11/1.49  fof(f30,plain,(
% 7.11/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.11/1.49    inference(flattening,[],[f29])).
% 7.11/1.49  
% 7.11/1.49  fof(f65,plain,(
% 7.11/1.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f30])).
% 7.11/1.49  
% 7.11/1.49  fof(f64,plain,(
% 7.11/1.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f30])).
% 7.11/1.49  
% 7.11/1.49  fof(f79,plain,(
% 7.11/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f41])).
% 7.11/1.49  
% 7.11/1.49  fof(f86,plain,(
% 7.11/1.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 7.11/1.49    inference(cnf_transformation,[],[f50])).
% 7.11/1.49  
% 7.11/1.49  fof(f76,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f48])).
% 7.11/1.49  
% 7.11/1.49  fof(f91,plain,(
% 7.11/1.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.11/1.49    inference(equality_resolution,[],[f76])).
% 7.11/1.49  
% 7.11/1.49  fof(f13,axiom,(
% 7.11/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f21,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.11/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.11/1.49  
% 7.11/1.49  fof(f33,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.11/1.49    inference(ennf_transformation,[],[f21])).
% 7.11/1.49  
% 7.11/1.49  fof(f68,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f33])).
% 7.11/1.49  
% 7.11/1.49  fof(f8,axiom,(
% 7.11/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f26,plain,(
% 7.11/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.11/1.49    inference(ennf_transformation,[],[f8])).
% 7.11/1.49  
% 7.11/1.49  fof(f47,plain,(
% 7.11/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.11/1.49    inference(nnf_transformation,[],[f26])).
% 7.11/1.49  
% 7.11/1.49  fof(f60,plain,(
% 7.11/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f47])).
% 7.11/1.49  
% 7.11/1.49  fof(f4,axiom,(
% 7.11/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f56,plain,(
% 7.11/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f4])).
% 7.11/1.49  
% 7.11/1.49  fof(f3,axiom,(
% 7.11/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f55,plain,(
% 7.11/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f3])).
% 7.11/1.49  
% 7.11/1.49  fof(f1,axiom,(
% 7.11/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f44,plain,(
% 7.11/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.49    inference(nnf_transformation,[],[f1])).
% 7.11/1.49  
% 7.11/1.49  fof(f45,plain,(
% 7.11/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.49    inference(flattening,[],[f44])).
% 7.11/1.49  
% 7.11/1.49  fof(f53,plain,(
% 7.11/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f16,axiom,(
% 7.11/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.11/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f36,plain,(
% 7.11/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.11/1.49    inference(ennf_transformation,[],[f16])).
% 7.11/1.49  
% 7.11/1.49  fof(f37,plain,(
% 7.11/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.11/1.49    inference(flattening,[],[f36])).
% 7.11/1.49  
% 7.11/1.49  fof(f71,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f37])).
% 7.11/1.49  
% 7.11/1.49  fof(f74,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.11/1.49    inference(cnf_transformation,[],[f48])).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1045,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2207,plain,
% 7.11/1.49      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1045]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_44083,plain,
% 7.11/1.49      ( k1_relat_1(k2_funct_1(sK2)) != X0
% 7.11/1.49      | sK1 != X0
% 7.11/1.49      | sK1 = k1_relat_1(k2_funct_1(sK2)) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2207]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_44084,plain,
% 7.11/1.49      ( k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 7.11/1.49      | sK1 = k1_relat_1(k2_funct_1(sK2))
% 7.11/1.49      | sK1 != k1_xboole_0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_44083]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_18,plain,
% 7.11/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_37759,plain,
% 7.11/1.49      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.11/1.49      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_24109,plain,
% 7.11/1.49      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != X0
% 7.11/1.49      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
% 7.11/1.49      | sK1 != X0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1045]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_37758,plain,
% 7.11/1.49      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != k1_relat_1(k2_funct_1(sK2))
% 7.11/1.49      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
% 7.11/1.49      | sK1 != k1_relat_1(k2_funct_1(sK2)) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_24109]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_9594,plain,
% 7.11/1.49      ( X0 != X1 | k2_relat_1(X2) != X1 | k2_relat_1(X2) = X0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1045]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_21457,plain,
% 7.11/1.49      ( k2_relat_1(k2_funct_1(sK2)) != X0
% 7.11/1.49      | k2_relat_1(k2_funct_1(sK2)) = sK0
% 7.11/1.49      | sK0 != X0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_9594]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_21458,plain,
% 7.11/1.49      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 7.11/1.49      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 7.11/1.49      | sK0 != k1_xboole_0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_21457]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2397,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK1) | r1_tarski(X0,sK1) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_17201,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,sK1)
% 7.11/1.49      | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),X0)
% 7.11/1.49      | r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2397]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_17202,plain,
% 7.11/1.49      ( r1_tarski(X0,sK1) != iProver_top
% 7.11/1.49      | r1_tarski(k1_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 7.11/1.49      | r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_17201]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_17204,plain,
% 7.11/1.49      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) = iProver_top
% 7.11/1.49      | r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0) != iProver_top
% 7.11/1.49      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_17202]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_17203,plain,
% 7.11/1.49      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1)
% 7.11/1.49      | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0)
% 7.11/1.49      | ~ r1_tarski(k1_xboole_0,sK1) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_17201]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_26,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.11/1.49      | k1_xboole_0 = X2 ),
% 7.11/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_34,negated_conjecture,
% 7.11/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.11/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_666,plain,
% 7.11/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.11/1.49      | sK0 != X1
% 7.11/1.49      | sK1 != X2
% 7.11/1.49      | sK2 != X0
% 7.11/1.49      | k1_xboole_0 = X2 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_667,plain,
% 7.11/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.11/1.49      | k1_relset_1(sK0,sK1,sK2) = sK0
% 7.11/1.49      | k1_xboole_0 = sK1 ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_666]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_33,negated_conjecture,
% 7.11/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.11/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_669,plain,
% 7.11/1.49      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_667,c_33]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1765,plain,
% 7.11/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1769,plain,
% 7.11/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.11/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2700,plain,
% 7.11/1.49      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1765,c_1769]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2784,plain,
% 7.11/1.49      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_669,c_2700]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7,plain,
% 7.11/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.11/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1773,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.11/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2424,plain,
% 7.11/1.49      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1765,c_1773]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_8,plain,
% 7.11/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.11/1.49      | ~ v1_relat_1(X1)
% 7.11/1.49      | v1_relat_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.11/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_263,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.11/1.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_264,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_263]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_325,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.11/1.49      inference(bin_hyper_res,[status(thm)],[c_8,c_264]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1763,plain,
% 7.11/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.11/1.49      | v1_relat_1(X1) != iProver_top
% 7.11/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4737,plain,
% 7.11/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.11/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_2424,c_1763]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_11,plain,
% 7.11/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.11/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1772,plain,
% 7.11/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4752,plain,
% 7.11/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.11/1.49      inference(forward_subsumption_resolution,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_4737,c_1772]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_15,plain,
% 7.11/1.49      ( ~ v2_funct_1(X0)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_relat_1(X0)
% 7.11/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_32,negated_conjecture,
% 7.11/1.49      ( v2_funct_1(sK2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_456,plain,
% 7.11/1.49      ( ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_relat_1(X0)
% 7.11/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.11/1.49      | sK2 != X0 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_457,plain,
% 7.11/1.49      ( ~ v1_funct_1(sK2)
% 7.11/1.49      | ~ v1_relat_1(sK2)
% 7.11/1.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_456]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_35,negated_conjecture,
% 7.11/1.49      ( v1_funct_1(sK2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_459,plain,
% 7.11/1.49      ( ~ v1_relat_1(sK2)
% 7.11/1.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_457,c_35]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1760,plain,
% 7.11/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.11/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4757,plain,
% 7.11/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4752,c_1760]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_27,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_relat_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1766,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3427,plain,
% 7.11/1.49      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1766,c_1773]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7946,plain,
% 7.11/1.49      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))) = iProver_top
% 7.11/1.49      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.11/1.49      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4757,c_3427]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_19,plain,
% 7.11/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1768,plain,
% 7.11/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.11/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2618,plain,
% 7.11/1.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1765,c_1768]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_31,negated_conjecture,
% 7.11/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.11/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2620,plain,
% 7.11/1.49      ( k2_relat_1(sK2) = sK1 ),
% 7.11/1.49      inference(light_normalisation,[status(thm)],[c_2618,c_31]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_16,plain,
% 7.11/1.49      ( ~ v2_funct_1(X0)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_relat_1(X0)
% 7.11/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_442,plain,
% 7.11/1.49      ( ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_relat_1(X0)
% 7.11/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.11/1.49      | sK2 != X0 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_443,plain,
% 7.11/1.50      ( ~ v1_funct_1(sK2)
% 7.11/1.50      | ~ v1_relat_1(sK2)
% 7.11/1.50      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_442]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_445,plain,
% 7.11/1.50      ( ~ v1_relat_1(sK2)
% 7.11/1.50      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_443,c_35]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1761,plain,
% 7.11/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2693,plain,
% 7.11/1.50      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(demodulation,[status(thm)],[c_2620,c_1761]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4756,plain,
% 7.11/1.50      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_4752,c_2693]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_8015,plain,
% 7.11/1.50      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top
% 7.11/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(light_normalisation,[status(thm)],[c_7946,c_4756]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_36,plain,
% 7.11/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_13,plain,
% 7.11/1.50      ( ~ v1_funct_1(X0)
% 7.11/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.11/1.50      | ~ v1_relat_1(X0) ),
% 7.11/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2039,plain,
% 7.11/1.50      ( v1_funct_1(k2_funct_1(sK2))
% 7.11/1.50      | ~ v1_funct_1(sK2)
% 7.11/1.50      | ~ v1_relat_1(sK2) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2040,plain,
% 7.11/1.50      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.11/1.50      | v1_funct_1(sK2) != iProver_top
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_2039]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_14,plain,
% 7.11/1.50      ( ~ v1_funct_1(X0)
% 7.11/1.50      | ~ v1_relat_1(X0)
% 7.11/1.50      | v1_relat_1(k2_funct_1(X0)) ),
% 7.11/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2042,plain,
% 7.11/1.50      ( ~ v1_funct_1(sK2)
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2))
% 7.11/1.50      | ~ v1_relat_1(sK2) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2043,plain,
% 7.11/1.50      ( v1_funct_1(sK2) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_2042]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11052,plain,
% 7.11/1.50      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_8015,c_36,c_2040,c_2043,c_4752]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11057,plain,
% 7.11/1.50      ( sK1 = k1_xboole_0
% 7.11/1.50      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_2784,c_11052]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1774,plain,
% 7.11/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.11/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_28,plain,
% 7.11/1.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.11/1.50      | ~ v1_funct_1(X0)
% 7.11/1.50      | ~ v1_relat_1(X0) ),
% 7.11/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_30,negated_conjecture,
% 7.11/1.50      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 7.11/1.50      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.11/1.50      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 7.11/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_677,plain,
% 7.11/1.50      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.11/1.50      | ~ v1_funct_1(X0)
% 7.11/1.50      | ~ v1_funct_1(k2_funct_1(sK2))
% 7.11/1.50      | ~ v1_relat_1(X0)
% 7.11/1.50      | k2_relat_1(X0) != sK0
% 7.11/1.50      | k2_funct_1(sK2) != X0
% 7.11/1.50      | k1_relat_1(X0) != sK1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_678,plain,
% 7.11/1.50      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.11/1.50      | ~ v1_funct_1(k2_funct_1(sK2))
% 7.11/1.50      | ~ v1_relat_1(k2_funct_1(sK2))
% 7.11/1.50      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 7.11/1.50      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_677]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1750,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 7.11/1.50      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.11/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4832,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 7.11/1.50      | sK1 != sK1
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.11/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(demodulation,[status(thm)],[c_4756,c_1750]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5675,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.11/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(equality_resolution_simp,[status(thm)],[c_4832]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_679,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 7.11/1.50      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.11/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5677,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_5675,c_36,c_679,c_2040,c_2043,c_2693,c_4752]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5681,plain,
% 7.11/1.50      ( k1_relat_1(sK2) != sK0
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 7.11/1.50      inference(light_normalisation,[status(thm)],[c_5677,c_4757]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5685,plain,
% 7.11/1.50      ( sK1 = k1_xboole_0
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_2784,c_5681]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5690,plain,
% 7.11/1.50      ( sK1 = k1_xboole_0
% 7.11/1.50      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_1774,c_5685]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11203,plain,
% 7.11/1.50      ( sK1 = k1_xboole_0 ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_11057,c_5690]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_22,plain,
% 7.11/1.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.11/1.50      | k1_xboole_0 = X1
% 7.11/1.50      | k1_xboole_0 = X0 ),
% 7.11/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_553,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.11/1.50      | sK0 != X1
% 7.11/1.50      | sK1 != k1_xboole_0
% 7.11/1.50      | sK2 != X0
% 7.11/1.50      | k1_xboole_0 = X0
% 7.11/1.50      | k1_xboole_0 = X1 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_554,plain,
% 7.11/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 7.11/1.50      | sK1 != k1_xboole_0
% 7.11/1.50      | k1_xboole_0 = sK0
% 7.11/1.50      | k1_xboole_0 = sK2 ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_553]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1756,plain,
% 7.11/1.50      ( sK1 != k1_xboole_0
% 7.11/1.50      | k1_xboole_0 = sK0
% 7.11/1.50      | k1_xboole_0 = sK2
% 7.11/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11240,plain,
% 7.11/1.50      ( sK0 = k1_xboole_0
% 7.11/1.50      | sK2 = k1_xboole_0
% 7.11/1.50      | k1_xboole_0 != k1_xboole_0
% 7.11/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 7.11/1.50      inference(demodulation,[status(thm)],[c_11203,c_1756]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11281,plain,
% 7.11/1.50      ( sK0 = k1_xboole_0
% 7.11/1.50      | sK2 = k1_xboole_0
% 7.11/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 7.11/1.50      inference(equality_resolution_simp,[status(thm)],[c_11240]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11246,plain,
% 7.11/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.11/1.50      inference(demodulation,[status(thm)],[c_11203,c_1765]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11285,plain,
% 7.11/1.50      ( sK0 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.11/1.50      inference(forward_subsumption_resolution,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_11281,c_11246]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_17,plain,
% 7.11/1.50      ( v4_relat_1(X0,X1)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.11/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_10,plain,
% 7.11/1.50      ( ~ v4_relat_1(X0,X1)
% 7.11/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.11/1.50      | ~ v1_relat_1(X0) ),
% 7.11/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_476,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.11/1.50      | ~ v1_relat_1(X0) ),
% 7.11/1.50      inference(resolution,[status(thm)],[c_17,c_10]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1759,plain,
% 7.11/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.11/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.11/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5102,plain,
% 7.11/1.50      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_1765,c_1759]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5291,plain,
% 7.11/1.50      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_5102,c_4752]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_12051,plain,
% 7.11/1.50      ( sK2 = k1_xboole_0
% 7.11/1.50      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_11285,c_5291]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.11/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2082,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2085,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_2082]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2087,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2085]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2432,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.50      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2433,plain,
% 7.11/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.11/1.50      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2435,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.11/1.50      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2433]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2089,plain,
% 7.11/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.50      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2849,plain,
% 7.11/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.11/1.50      | ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2089]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2854,plain,
% 7.11/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 7.11/1.50      | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_2849]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2856,plain,
% 7.11/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 7.11/1.50      | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2854]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1046,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.11/1.50      theory(equality) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2449,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.11/1.50      | r1_tarski(X3,k2_zfmisc_1(X1,X2))
% 7.11/1.50      | X3 != X0 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_1046]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4224,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.11/1.50      | r1_tarski(sK2,k2_zfmisc_1(X1,X2))
% 7.11/1.50      | sK2 != X0 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2449]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4225,plain,
% 7.11/1.50      ( sK2 != X0
% 7.11/1.50      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.11/1.50      | r1_tarski(sK2,k2_zfmisc_1(X1,X2)) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_4224]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4227,plain,
% 7.11/1.50      ( sK2 != k1_xboole_0
% 7.11/1.50      | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.11/1.50      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_4225]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11518,plain,
% 7.11/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.11/1.50      | r1_tarski(k1_relat_1(sK2),X0)
% 7.11/1.50      | ~ v1_relat_1(sK2) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_476]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11519,plain,
% 7.11/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.11/1.50      | r1_tarski(k1_relat_1(sK2),X0) = iProver_top
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_11518]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11521,plain,
% 7.11/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.11/1.50      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_11519]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_12770,plain,
% 7.11/1.50      ( r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_12051,c_2087,c_2435,c_2856,c_4227,c_4752,c_11521]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4,plain,
% 7.11/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.11/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1776,plain,
% 7.11/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_0,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.11/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1779,plain,
% 7.11/1.50      ( X0 = X1
% 7.11/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_3309,plain,
% 7.11/1.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_1776,c_1779]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_12782,plain,
% 7.11/1.50      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_12770,c_3309]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_13019,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 7.11/1.50      inference(demodulation,[status(thm)],[c_12782,c_4757]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_6636,plain,
% 7.11/1.50      ( ~ r1_tarski(X0,X1)
% 7.11/1.50      | r1_tarski(k2_relat_1(X2),X1)
% 7.11/1.50      | k2_relat_1(X2) != X0 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_1046]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_9598,plain,
% 7.11/1.50      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
% 7.11/1.50      | ~ r1_tarski(k1_relat_1(sK2),X0)
% 7.11/1.50      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_6636]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11549,plain,
% 7.11/1.50      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 7.11/1.50      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 7.11/1.50      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_9598]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11552,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 7.11/1.50      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) = iProver_top
% 7.11/1.50      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_11549]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4834,plain,
% 7.11/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 7.11/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_4756,c_1766]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11428,plain,
% 7.11/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 7.11/1.50      inference(global_propositional_subsumption,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_4834,c_36,c_2040,c_2043,c_4752]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11432,plain,
% 7.11/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 7.11/1.50      inference(light_normalisation,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_11428,c_4757,c_11203]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11439,plain,
% 7.11/1.50      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0) = iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(superposition,[status(thm)],[c_11432,c_1759]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11449,plain,
% 7.11/1.50      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),k1_xboole_0)
% 7.11/1.50      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 7.11/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_11439]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_11227,plain,
% 7.11/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 7.11/1.50      inference(demodulation,[status(thm)],[c_11203,c_4756]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_20,plain,
% 7.11/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.50      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.11/1.50      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.11/1.50      | ~ v1_relat_1(X0) ),
% 7.11/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_7302,plain,
% 7.11/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.11/1.50      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 7.11/1.50      | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1)
% 7.11/1.50      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_7306,plain,
% 7.11/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.11/1.50      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 7.11/1.50      | r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK1) != iProver_top
% 7.11/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_7302]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_5127,plain,
% 7.11/1.50      ( r1_tarski(k1_relat_1(sK2),sK0) | ~ v1_relat_1(sK2) ),
% 7.11/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5102]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_4753,plain,
% 7.11/1.50      ( v1_relat_1(sK2) ),
% 7.11/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4752]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2787,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2790,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2391,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) | r1_tarski(X0,sK1) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2392,plain,
% 7.11/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 7.11/1.50      | r1_tarski(X0,sK1) = iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_2391]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2394,plain,
% 7.11/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) != iProver_top
% 7.11/1.50      | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2392]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2393,plain,
% 7.11/1.50      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
% 7.11/1.50      | r1_tarski(k1_xboole_0,sK1) ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2391]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_1044,plain,( X0 = X0 ),theory(equality) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2200,plain,
% 7.11/1.50      ( sK0 = sK0 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_1044]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2079,plain,
% 7.11/1.50      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_1045]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_2199,plain,
% 7.11/1.50      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 7.11/1.50      inference(instantiation,[status(thm)],[c_2079]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_24,plain,
% 7.11/1.50      ( v1_funct_2(X0,X1,X2)
% 7.11/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.50      | k1_relset_1(X1,X2,X0) != X1
% 7.11/1.50      | k1_xboole_0 = X2 ),
% 7.11/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_650,plain,
% 7.11/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.50      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.11/1.50      | ~ v1_funct_1(k2_funct_1(sK2))
% 7.11/1.50      | k1_relset_1(X1,X2,X0) != X1
% 7.11/1.50      | k2_funct_1(sK2) != X0
% 7.11/1.50      | sK0 != X2
% 7.11/1.50      | sK1 != X1
% 7.11/1.50      | k1_xboole_0 = X2 ),
% 7.11/1.50      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_651,plain,
% 7.11/1.50      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.11/1.50      | ~ v1_funct_1(k2_funct_1(sK2))
% 7.11/1.50      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 7.11/1.50      | k1_xboole_0 = sK0 ),
% 7.11/1.50      inference(unflattening,[status(thm)],[c_650]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_652,plain,
% 7.11/1.50      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 7.11/1.50      | k1_xboole_0 = sK0
% 7.11/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.11/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(c_458,plain,
% 7.11/1.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.11/1.50      | v1_funct_1(sK2) != iProver_top
% 7.11/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.11/1.50      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 7.11/1.50  
% 7.11/1.50  cnf(contradiction,plain,
% 7.11/1.50      ( $false ),
% 7.11/1.50      inference(minisat,
% 7.11/1.50                [status(thm)],
% 7.11/1.50                [c_44084,c_37759,c_37758,c_21458,c_17204,c_17203,c_13019,
% 7.11/1.50                 c_11552,c_11549,c_11449,c_11439,c_11227,c_11203,c_7306,
% 7.11/1.50                 c_7302,c_5127,c_5102,c_4753,c_4752,c_2790,c_2787,c_2693,
% 7.11/1.50                 c_2394,c_2393,c_2200,c_2199,c_2043,c_2042,c_2040,c_2039,
% 7.11/1.50                 c_678,c_652,c_458,c_36,c_35]) ).
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.11/1.50  
% 7.11/1.50  ------                               Statistics
% 7.11/1.50  
% 7.11/1.50  ------ General
% 7.11/1.50  
% 7.11/1.50  abstr_ref_over_cycles:                  0
% 7.11/1.50  abstr_ref_under_cycles:                 0
% 7.11/1.50  gc_basic_clause_elim:                   0
% 7.11/1.50  forced_gc_time:                         0
% 7.11/1.50  parsing_time:                           0.007
% 7.11/1.50  unif_index_cands_time:                  0.
% 7.11/1.50  unif_index_add_time:                    0.
% 7.11/1.50  orderings_time:                         0.
% 7.11/1.50  out_proof_time:                         0.015
% 7.11/1.50  total_time:                             0.925
% 7.11/1.50  num_of_symbols:                         49
% 7.11/1.50  num_of_terms:                           22556
% 7.11/1.50  
% 7.11/1.50  ------ Preprocessing
% 7.11/1.50  
% 7.11/1.50  num_of_splits:                          0
% 7.11/1.50  num_of_split_atoms:                     0
% 7.11/1.50  num_of_reused_defs:                     0
% 7.11/1.50  num_eq_ax_congr_red:                    7
% 7.11/1.50  num_of_sem_filtered_clauses:            1
% 7.11/1.50  num_of_subtypes:                        0
% 7.11/1.50  monotx_restored_types:                  0
% 7.11/1.50  sat_num_of_epr_types:                   0
% 7.11/1.50  sat_num_of_non_cyclic_types:            0
% 7.11/1.50  sat_guarded_non_collapsed_types:        0
% 7.11/1.50  num_pure_diseq_elim:                    0
% 7.11/1.50  simp_replaced_by:                       0
% 7.11/1.50  res_preprocessed:                       160
% 7.11/1.50  prep_upred:                             0
% 7.11/1.50  prep_unflattend:                        43
% 7.11/1.50  smt_new_axioms:                         0
% 7.11/1.50  pred_elim_cands:                        4
% 7.11/1.50  pred_elim:                              3
% 7.11/1.50  pred_elim_cl:                           1
% 7.11/1.50  pred_elim_cycles:                       5
% 7.11/1.50  merged_defs:                            8
% 7.11/1.50  merged_defs_ncl:                        0
% 7.11/1.50  bin_hyper_res:                          10
% 7.11/1.50  prep_cycles:                            4
% 7.11/1.50  pred_elim_time:                         0.006
% 7.11/1.50  splitting_time:                         0.
% 7.11/1.50  sem_filter_time:                        0.
% 7.11/1.50  monotx_time:                            0.
% 7.11/1.50  subtype_inf_time:                       0.
% 7.11/1.50  
% 7.11/1.50  ------ Problem properties
% 7.11/1.50  
% 7.11/1.50  clauses:                                33
% 7.11/1.50  conjectures:                            3
% 7.11/1.50  epr:                                    7
% 7.11/1.50  horn:                                   29
% 7.11/1.50  ground:                                 13
% 7.11/1.50  unary:                                  7
% 7.11/1.50  binary:                                 7
% 7.11/1.50  lits:                                   95
% 7.11/1.50  lits_eq:                                31
% 7.11/1.50  fd_pure:                                0
% 7.11/1.50  fd_pseudo:                              0
% 7.11/1.50  fd_cond:                                1
% 7.11/1.50  fd_pseudo_cond:                         1
% 7.11/1.50  ac_symbols:                             0
% 7.11/1.50  
% 7.11/1.50  ------ Propositional Solver
% 7.11/1.50  
% 7.11/1.50  prop_solver_calls:                      34
% 7.11/1.50  prop_fast_solver_calls:                 2796
% 7.11/1.50  smt_solver_calls:                       0
% 7.11/1.50  smt_fast_solver_calls:                  0
% 7.11/1.50  prop_num_of_clauses:                    12914
% 7.11/1.50  prop_preprocess_simplified:             22382
% 7.11/1.50  prop_fo_subsumed:                       348
% 7.11/1.50  prop_solver_time:                       0.
% 7.11/1.50  smt_solver_time:                        0.
% 7.11/1.50  smt_fast_solver_time:                   0.
% 7.11/1.50  prop_fast_solver_time:                  0.
% 7.11/1.50  prop_unsat_core_time:                   0.001
% 7.11/1.50  
% 7.11/1.50  ------ QBF
% 7.11/1.50  
% 7.11/1.50  qbf_q_res:                              0
% 7.11/1.50  qbf_num_tautologies:                    0
% 7.11/1.50  qbf_prep_cycles:                        0
% 7.11/1.50  
% 7.11/1.50  ------ BMC1
% 7.11/1.50  
% 7.11/1.50  bmc1_current_bound:                     -1
% 7.11/1.50  bmc1_last_solved_bound:                 -1
% 7.11/1.50  bmc1_unsat_core_size:                   -1
% 7.11/1.50  bmc1_unsat_core_parents_size:           -1
% 7.11/1.50  bmc1_merge_next_fun:                    0
% 7.11/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.11/1.50  
% 7.11/1.50  ------ Instantiation
% 7.11/1.50  
% 7.11/1.50  inst_num_of_clauses:                    3191
% 7.11/1.50  inst_num_in_passive:                    1423
% 7.11/1.50  inst_num_in_active:                     1749
% 7.11/1.50  inst_num_in_unprocessed:                18
% 7.11/1.50  inst_num_of_loops:                      2054
% 7.11/1.50  inst_num_of_learning_restarts:          0
% 7.11/1.50  inst_num_moves_active_passive:          298
% 7.11/1.50  inst_lit_activity:                      0
% 7.11/1.50  inst_lit_activity_moves:                0
% 7.11/1.50  inst_num_tautologies:                   0
% 7.11/1.50  inst_num_prop_implied:                  0
% 7.11/1.50  inst_num_existing_simplified:           0
% 7.11/1.50  inst_num_eq_res_simplified:             0
% 7.11/1.50  inst_num_child_elim:                    0
% 7.11/1.50  inst_num_of_dismatching_blockings:      3830
% 7.11/1.50  inst_num_of_non_proper_insts:           6703
% 7.11/1.50  inst_num_of_duplicates:                 0
% 7.11/1.50  inst_inst_num_from_inst_to_res:         0
% 7.11/1.50  inst_dismatching_checking_time:         0.
% 7.11/1.50  
% 7.11/1.50  ------ Resolution
% 7.11/1.50  
% 7.11/1.50  res_num_of_clauses:                     0
% 7.11/1.50  res_num_in_passive:                     0
% 7.11/1.50  res_num_in_active:                      0
% 7.11/1.50  res_num_of_loops:                       164
% 7.11/1.50  res_forward_subset_subsumed:            205
% 7.11/1.50  res_backward_subset_subsumed:           12
% 7.11/1.50  res_forward_subsumed:                   0
% 7.11/1.50  res_backward_subsumed:                  0
% 7.11/1.50  res_forward_subsumption_resolution:     1
% 7.11/1.50  res_backward_subsumption_resolution:    0
% 7.11/1.50  res_clause_to_clause_subsumption:       7066
% 7.11/1.50  res_orphan_elimination:                 0
% 7.11/1.50  res_tautology_del:                      1083
% 7.11/1.50  res_num_eq_res_simplified:              0
% 7.11/1.50  res_num_sel_changes:                    0
% 7.11/1.50  res_moves_from_active_to_pass:          0
% 7.11/1.50  
% 7.11/1.50  ------ Superposition
% 7.11/1.50  
% 7.11/1.50  sup_time_total:                         0.
% 7.11/1.50  sup_time_generating:                    0.
% 7.11/1.50  sup_time_sim_full:                      0.
% 7.11/1.50  sup_time_sim_immed:                     0.
% 7.11/1.50  
% 7.11/1.50  sup_num_of_clauses:                     760
% 7.11/1.50  sup_num_in_active:                      253
% 7.11/1.50  sup_num_in_passive:                     507
% 7.11/1.50  sup_num_of_loops:                       410
% 7.11/1.50  sup_fw_superposition:                   713
% 7.11/1.50  sup_bw_superposition:                   943
% 7.11/1.50  sup_immediate_simplified:               418
% 7.11/1.50  sup_given_eliminated:                   10
% 7.11/1.50  comparisons_done:                       0
% 7.11/1.50  comparisons_avoided:                    26
% 7.11/1.50  
% 7.11/1.50  ------ Simplifications
% 7.11/1.50  
% 7.11/1.50  
% 7.11/1.50  sim_fw_subset_subsumed:                 171
% 7.11/1.50  sim_bw_subset_subsumed:                 152
% 7.11/1.50  sim_fw_subsumed:                        135
% 7.11/1.50  sim_bw_subsumed:                        19
% 7.11/1.50  sim_fw_subsumption_res:                 12
% 7.11/1.50  sim_bw_subsumption_res:                 2
% 7.11/1.50  sim_tautology_del:                      12
% 7.11/1.50  sim_eq_tautology_del:                   95
% 7.11/1.50  sim_eq_res_simp:                        4
% 7.11/1.50  sim_fw_demodulated:                     52
% 7.11/1.50  sim_bw_demodulated:                     157
% 7.11/1.50  sim_light_normalised:                   176
% 7.11/1.50  sim_joinable_taut:                      0
% 7.11/1.50  sim_joinable_simp:                      0
% 7.11/1.50  sim_ac_normalised:                      0
% 7.11/1.50  sim_smt_subsumption:                    0
% 7.11/1.50  
%------------------------------------------------------------------------------
