%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:31 EST 2020

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 389 expanded)
%              Number of clauses        :  119 ( 172 expanded)
%              Number of leaves         :   19 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  538 (1655 expanded)
%              Number of equality atoms :  221 ( 496 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f47])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f32])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1573,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_6756,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),X3)
    | X2 != X3
    | X1 != k1_relat_1(sK4)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_17521,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),X0)
    | v1_funct_2(sK4,sK1,sK3)
    | sK3 != X0
    | sK1 != k1_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6756])).

cnf(c_60013,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
    | v1_funct_2(sK4,sK1,sK3)
    | sK3 != k2_relat_1(sK4)
    | sK1 != k1_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_17521])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2473,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_27344,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(sK3,k2_relat_1(sK4))
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2473])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7204,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_relat_1(sK4))
    | r1_tarski(X0,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16878,plain,
    ( r1_tarski(X0,k2_relat_1(sK4))
    | ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_7204])).

cnf(c_27336,plain,
    ( r1_tarski(sK3,k2_relat_1(sK4))
    | ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_16878])).

cnf(c_26929,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | v1_funct_2(sK4,sK1,sK3)
    | sK3 != sK3
    | sK1 != k1_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_17521])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14581,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14443,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | k1_relset_1(k1_relat_1(sK4),sK3,sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_13364,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2337,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2320,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2322,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4534,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_2322])).

cnf(c_2330,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3390,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2320,c_2330])).

cnf(c_4540,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4534,c_3390])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_39,plain,
    ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5122,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4540,c_39])).

cnf(c_5123,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5122])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_459,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_12])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_459])).

cnf(c_2317,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_3901,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_2317])).

cnf(c_2336,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4137,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3901,c_2336])).

cnf(c_2338,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4305,plain,
    ( k1_relat_1(sK4) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4137,c_2338])).

cnf(c_5531,plain,
    ( k1_relat_1(sK4) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_4305])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_110,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_116,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_115,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_117,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_125,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1563,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2408,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_2409,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2408])).

cnf(c_1562,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3100,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_2760,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_3250,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_3251,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_3250])).

cnf(c_1564,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3417,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_3418,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3417])).

cnf(c_3420,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3418])).

cnf(c_4136,plain,
    ( k1_relat_1(sK4) = sK1
    | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3901,c_2338])).

cnf(c_6117,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6118,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6117])).

cnf(c_6732,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | X0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6733,plain,
    ( X0 = sK1
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6732])).

cnf(c_2996,plain,
    ( X0 != X1
    | k1_relat_1(sK4) != X1
    | k1_relat_1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_9146,plain,
    ( X0 != sK1
    | k1_relat_1(sK4) = X0
    | k1_relat_1(sK4) != sK1 ),
    inference(instantiation,[status(thm)],[c_2996])).

cnf(c_3568,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_relat_1(sK4))
    | r1_tarski(X0,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11752,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_11753,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11752])).

cnf(c_11755,plain,
    ( r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11753])).

cnf(c_13175,plain,
    ( k1_relat_1(sK4) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5531,c_33,c_110,c_111,c_116,c_117,c_125,c_2409,c_3100,c_3251,c_3420,c_4136,c_6118,c_6733,c_9146,c_11755])).

cnf(c_13181,plain,
    ( k1_relat_1(sK4) = sK1
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2337,c_13175])).

cnf(c_13194,plain,
    ( ~ r1_tarski(sK1,sK1)
    | k1_relat_1(sK4) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13181])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2517,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK4),X1)
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4204,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_7062,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4204])).

cnf(c_6361,plain,
    ( k1_relat_1(sK4) != sK1
    | sK1 = k1_relat_1(sK4)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3250])).

cnf(c_2707,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_3253,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_5741,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK3)
    | X0 != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3253])).

cnf(c_5743,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_5741])).

cnf(c_2328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_206,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_37])).

cnf(c_207,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_2318,plain,
    ( v1_funct_2(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_4896,plain,
    ( v1_funct_2(sK4,sK1,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2328,c_2318])).

cnf(c_4905,plain,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4896])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3054,plain,
    ( v1_funct_2(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | k1_relset_1(X1,sK3,X0) != X1
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4180,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | k1_relset_1(k1_relat_1(sK4),sK3,sK4) != k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3054])).

cnf(c_3888,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_2854,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(k1_relat_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_3528,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK4),sK1) ),
    inference(instantiation,[status(thm)],[c_2854])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2329,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3375,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2320,c_2329])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2321,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3464,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3375,c_2321])).

cnf(c_3465,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3464])).

cnf(c_3403,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3366,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2420,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2509,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_2493,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_536,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_37])).

cnf(c_537,plain,
    ( v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60013,c_27344,c_27336,c_26929,c_14581,c_14443,c_13364,c_13194,c_7062,c_6361,c_5743,c_4905,c_4180,c_3888,c_3528,c_3465,c_3403,c_3366,c_3100,c_2509,c_2493,c_537,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.51/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/2.00  
% 11.51/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.51/2.00  
% 11.51/2.00  ------  iProver source info
% 11.51/2.00  
% 11.51/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.51/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.51/2.00  git: non_committed_changes: false
% 11.51/2.00  git: last_make_outside_of_git: false
% 11.51/2.00  
% 11.51/2.00  ------ 
% 11.51/2.00  
% 11.51/2.00  ------ Input Options
% 11.51/2.00  
% 11.51/2.00  --out_options                           all
% 11.51/2.00  --tptp_safe_out                         true
% 11.51/2.00  --problem_path                          ""
% 11.51/2.00  --include_path                          ""
% 11.51/2.00  --clausifier                            res/vclausify_rel
% 11.51/2.00  --clausifier_options                    ""
% 11.51/2.00  --stdin                                 false
% 11.51/2.00  --stats_out                             all
% 11.51/2.00  
% 11.51/2.00  ------ General Options
% 11.51/2.00  
% 11.51/2.00  --fof                                   false
% 11.51/2.00  --time_out_real                         305.
% 11.51/2.00  --time_out_virtual                      -1.
% 11.51/2.00  --symbol_type_check                     false
% 11.51/2.00  --clausify_out                          false
% 11.51/2.00  --sig_cnt_out                           false
% 11.51/2.00  --trig_cnt_out                          false
% 11.51/2.00  --trig_cnt_out_tolerance                1.
% 11.51/2.00  --trig_cnt_out_sk_spl                   false
% 11.51/2.00  --abstr_cl_out                          false
% 11.51/2.00  
% 11.51/2.00  ------ Global Options
% 11.51/2.00  
% 11.51/2.00  --schedule                              default
% 11.51/2.00  --add_important_lit                     false
% 11.51/2.00  --prop_solver_per_cl                    1000
% 11.51/2.00  --min_unsat_core                        false
% 11.51/2.00  --soft_assumptions                      false
% 11.51/2.00  --soft_lemma_size                       3
% 11.51/2.00  --prop_impl_unit_size                   0
% 11.51/2.00  --prop_impl_unit                        []
% 11.51/2.00  --share_sel_clauses                     true
% 11.51/2.00  --reset_solvers                         false
% 11.51/2.00  --bc_imp_inh                            [conj_cone]
% 11.51/2.00  --conj_cone_tolerance                   3.
% 11.51/2.00  --extra_neg_conj                        none
% 11.51/2.00  --large_theory_mode                     true
% 11.51/2.00  --prolific_symb_bound                   200
% 11.51/2.00  --lt_threshold                          2000
% 11.51/2.00  --clause_weak_htbl                      true
% 11.51/2.00  --gc_record_bc_elim                     false
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing Options
% 11.51/2.00  
% 11.51/2.00  --preprocessing_flag                    true
% 11.51/2.00  --time_out_prep_mult                    0.1
% 11.51/2.00  --splitting_mode                        input
% 11.51/2.00  --splitting_grd                         true
% 11.51/2.00  --splitting_cvd                         false
% 11.51/2.00  --splitting_cvd_svl                     false
% 11.51/2.00  --splitting_nvd                         32
% 11.51/2.00  --sub_typing                            true
% 11.51/2.00  --prep_gs_sim                           true
% 11.51/2.00  --prep_unflatten                        true
% 11.51/2.00  --prep_res_sim                          true
% 11.51/2.00  --prep_upred                            true
% 11.51/2.00  --prep_sem_filter                       exhaustive
% 11.51/2.00  --prep_sem_filter_out                   false
% 11.51/2.00  --pred_elim                             true
% 11.51/2.00  --res_sim_input                         true
% 11.51/2.00  --eq_ax_congr_red                       true
% 11.51/2.00  --pure_diseq_elim                       true
% 11.51/2.00  --brand_transform                       false
% 11.51/2.00  --non_eq_to_eq                          false
% 11.51/2.00  --prep_def_merge                        true
% 11.51/2.00  --prep_def_merge_prop_impl              false
% 11.51/2.00  --prep_def_merge_mbd                    true
% 11.51/2.00  --prep_def_merge_tr_red                 false
% 11.51/2.00  --prep_def_merge_tr_cl                  false
% 11.51/2.00  --smt_preprocessing                     true
% 11.51/2.00  --smt_ac_axioms                         fast
% 11.51/2.00  --preprocessed_out                      false
% 11.51/2.00  --preprocessed_stats                    false
% 11.51/2.00  
% 11.51/2.00  ------ Abstraction refinement Options
% 11.51/2.00  
% 11.51/2.00  --abstr_ref                             []
% 11.51/2.00  --abstr_ref_prep                        false
% 11.51/2.00  --abstr_ref_until_sat                   false
% 11.51/2.00  --abstr_ref_sig_restrict                funpre
% 11.51/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/2.00  --abstr_ref_under                       []
% 11.51/2.00  
% 11.51/2.00  ------ SAT Options
% 11.51/2.00  
% 11.51/2.00  --sat_mode                              false
% 11.51/2.00  --sat_fm_restart_options                ""
% 11.51/2.00  --sat_gr_def                            false
% 11.51/2.00  --sat_epr_types                         true
% 11.51/2.00  --sat_non_cyclic_types                  false
% 11.51/2.00  --sat_finite_models                     false
% 11.51/2.00  --sat_fm_lemmas                         false
% 11.51/2.00  --sat_fm_prep                           false
% 11.51/2.00  --sat_fm_uc_incr                        true
% 11.51/2.00  --sat_out_model                         small
% 11.51/2.00  --sat_out_clauses                       false
% 11.51/2.00  
% 11.51/2.00  ------ QBF Options
% 11.51/2.00  
% 11.51/2.00  --qbf_mode                              false
% 11.51/2.00  --qbf_elim_univ                         false
% 11.51/2.00  --qbf_dom_inst                          none
% 11.51/2.00  --qbf_dom_pre_inst                      false
% 11.51/2.00  --qbf_sk_in                             false
% 11.51/2.00  --qbf_pred_elim                         true
% 11.51/2.00  --qbf_split                             512
% 11.51/2.00  
% 11.51/2.00  ------ BMC1 Options
% 11.51/2.00  
% 11.51/2.00  --bmc1_incremental                      false
% 11.51/2.00  --bmc1_axioms                           reachable_all
% 11.51/2.00  --bmc1_min_bound                        0
% 11.51/2.00  --bmc1_max_bound                        -1
% 11.51/2.00  --bmc1_max_bound_default                -1
% 11.51/2.00  --bmc1_symbol_reachability              true
% 11.51/2.00  --bmc1_property_lemmas                  false
% 11.51/2.00  --bmc1_k_induction                      false
% 11.51/2.00  --bmc1_non_equiv_states                 false
% 11.51/2.00  --bmc1_deadlock                         false
% 11.51/2.00  --bmc1_ucm                              false
% 11.51/2.00  --bmc1_add_unsat_core                   none
% 11.51/2.00  --bmc1_unsat_core_children              false
% 11.51/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/2.00  --bmc1_out_stat                         full
% 11.51/2.00  --bmc1_ground_init                      false
% 11.51/2.00  --bmc1_pre_inst_next_state              false
% 11.51/2.00  --bmc1_pre_inst_state                   false
% 11.51/2.00  --bmc1_pre_inst_reach_state             false
% 11.51/2.00  --bmc1_out_unsat_core                   false
% 11.51/2.00  --bmc1_aig_witness_out                  false
% 11.51/2.00  --bmc1_verbose                          false
% 11.51/2.00  --bmc1_dump_clauses_tptp                false
% 11.51/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.51/2.00  --bmc1_dump_file                        -
% 11.51/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.51/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.51/2.00  --bmc1_ucm_extend_mode                  1
% 11.51/2.00  --bmc1_ucm_init_mode                    2
% 11.51/2.00  --bmc1_ucm_cone_mode                    none
% 11.51/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.51/2.00  --bmc1_ucm_relax_model                  4
% 11.51/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.51/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/2.00  --bmc1_ucm_layered_model                none
% 11.51/2.00  --bmc1_ucm_max_lemma_size               10
% 11.51/2.00  
% 11.51/2.00  ------ AIG Options
% 11.51/2.00  
% 11.51/2.00  --aig_mode                              false
% 11.51/2.00  
% 11.51/2.00  ------ Instantiation Options
% 11.51/2.00  
% 11.51/2.00  --instantiation_flag                    true
% 11.51/2.00  --inst_sos_flag                         true
% 11.51/2.00  --inst_sos_phase                        true
% 11.51/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/2.00  --inst_lit_sel_side                     num_symb
% 11.51/2.00  --inst_solver_per_active                1400
% 11.51/2.00  --inst_solver_calls_frac                1.
% 11.51/2.00  --inst_passive_queue_type               priority_queues
% 11.51/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/2.00  --inst_passive_queues_freq              [25;2]
% 11.51/2.00  --inst_dismatching                      true
% 11.51/2.00  --inst_eager_unprocessed_to_passive     true
% 11.51/2.00  --inst_prop_sim_given                   true
% 11.51/2.00  --inst_prop_sim_new                     false
% 11.51/2.00  --inst_subs_new                         false
% 11.51/2.00  --inst_eq_res_simp                      false
% 11.51/2.00  --inst_subs_given                       false
% 11.51/2.00  --inst_orphan_elimination               true
% 11.51/2.00  --inst_learning_loop_flag               true
% 11.51/2.00  --inst_learning_start                   3000
% 11.51/2.00  --inst_learning_factor                  2
% 11.51/2.00  --inst_start_prop_sim_after_learn       3
% 11.51/2.00  --inst_sel_renew                        solver
% 11.51/2.00  --inst_lit_activity_flag                true
% 11.51/2.00  --inst_restr_to_given                   false
% 11.51/2.00  --inst_activity_threshold               500
% 11.51/2.00  --inst_out_proof                        true
% 11.51/2.00  
% 11.51/2.00  ------ Resolution Options
% 11.51/2.00  
% 11.51/2.00  --resolution_flag                       true
% 11.51/2.00  --res_lit_sel                           adaptive
% 11.51/2.00  --res_lit_sel_side                      none
% 11.51/2.00  --res_ordering                          kbo
% 11.51/2.00  --res_to_prop_solver                    active
% 11.51/2.00  --res_prop_simpl_new                    false
% 11.51/2.00  --res_prop_simpl_given                  true
% 11.51/2.00  --res_passive_queue_type                priority_queues
% 11.51/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/2.00  --res_passive_queues_freq               [15;5]
% 11.51/2.00  --res_forward_subs                      full
% 11.51/2.00  --res_backward_subs                     full
% 11.51/2.00  --res_forward_subs_resolution           true
% 11.51/2.00  --res_backward_subs_resolution          true
% 11.51/2.00  --res_orphan_elimination                true
% 11.51/2.00  --res_time_limit                        2.
% 11.51/2.00  --res_out_proof                         true
% 11.51/2.00  
% 11.51/2.00  ------ Superposition Options
% 11.51/2.00  
% 11.51/2.00  --superposition_flag                    true
% 11.51/2.00  --sup_passive_queue_type                priority_queues
% 11.51/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.51/2.00  --demod_completeness_check              fast
% 11.51/2.00  --demod_use_ground                      true
% 11.51/2.00  --sup_to_prop_solver                    passive
% 11.51/2.00  --sup_prop_simpl_new                    true
% 11.51/2.00  --sup_prop_simpl_given                  true
% 11.51/2.00  --sup_fun_splitting                     true
% 11.51/2.00  --sup_smt_interval                      50000
% 11.51/2.00  
% 11.51/2.00  ------ Superposition Simplification Setup
% 11.51/2.00  
% 11.51/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.51/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.51/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.51/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.51/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.51/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.51/2.00  --sup_immed_triv                        [TrivRules]
% 11.51/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/2.00  --sup_immed_bw_main                     []
% 11.51/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.51/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/2.00  --sup_input_bw                          []
% 11.51/2.00  
% 11.51/2.00  ------ Combination Options
% 11.51/2.00  
% 11.51/2.00  --comb_res_mult                         3
% 11.51/2.00  --comb_sup_mult                         2
% 11.51/2.00  --comb_inst_mult                        10
% 11.51/2.00  
% 11.51/2.00  ------ Debug Options
% 11.51/2.00  
% 11.51/2.00  --dbg_backtrace                         false
% 11.51/2.00  --dbg_dump_prop_clauses                 false
% 11.51/2.00  --dbg_dump_prop_clauses_file            -
% 11.51/2.00  --dbg_out_stat                          false
% 11.51/2.00  ------ Parsing...
% 11.51/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.51/2.00  ------ Proving...
% 11.51/2.00  ------ Problem Properties 
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  clauses                                 37
% 11.51/2.00  conjectures                             5
% 11.51/2.00  EPR                                     6
% 11.51/2.00  Horn                                    27
% 11.51/2.00  unary                                   6
% 11.51/2.00  binary                                  10
% 11.51/2.00  lits                                    95
% 11.51/2.00  lits eq                                 18
% 11.51/2.00  fd_pure                                 0
% 11.51/2.00  fd_pseudo                               0
% 11.51/2.00  fd_cond                                 3
% 11.51/2.00  fd_pseudo_cond                          1
% 11.51/2.00  AC symbols                              0
% 11.51/2.00  
% 11.51/2.00  ------ Schedule dynamic 5 is on 
% 11.51/2.00  
% 11.51/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  ------ 
% 11.51/2.00  Current options:
% 11.51/2.00  ------ 
% 11.51/2.00  
% 11.51/2.00  ------ Input Options
% 11.51/2.00  
% 11.51/2.00  --out_options                           all
% 11.51/2.00  --tptp_safe_out                         true
% 11.51/2.00  --problem_path                          ""
% 11.51/2.00  --include_path                          ""
% 11.51/2.00  --clausifier                            res/vclausify_rel
% 11.51/2.00  --clausifier_options                    ""
% 11.51/2.00  --stdin                                 false
% 11.51/2.00  --stats_out                             all
% 11.51/2.00  
% 11.51/2.00  ------ General Options
% 11.51/2.00  
% 11.51/2.00  --fof                                   false
% 11.51/2.00  --time_out_real                         305.
% 11.51/2.00  --time_out_virtual                      -1.
% 11.51/2.00  --symbol_type_check                     false
% 11.51/2.00  --clausify_out                          false
% 11.51/2.00  --sig_cnt_out                           false
% 11.51/2.00  --trig_cnt_out                          false
% 11.51/2.00  --trig_cnt_out_tolerance                1.
% 11.51/2.00  --trig_cnt_out_sk_spl                   false
% 11.51/2.00  --abstr_cl_out                          false
% 11.51/2.00  
% 11.51/2.00  ------ Global Options
% 11.51/2.00  
% 11.51/2.00  --schedule                              default
% 11.51/2.00  --add_important_lit                     false
% 11.51/2.00  --prop_solver_per_cl                    1000
% 11.51/2.00  --min_unsat_core                        false
% 11.51/2.00  --soft_assumptions                      false
% 11.51/2.00  --soft_lemma_size                       3
% 11.51/2.00  --prop_impl_unit_size                   0
% 11.51/2.00  --prop_impl_unit                        []
% 11.51/2.00  --share_sel_clauses                     true
% 11.51/2.00  --reset_solvers                         false
% 11.51/2.00  --bc_imp_inh                            [conj_cone]
% 11.51/2.00  --conj_cone_tolerance                   3.
% 11.51/2.00  --extra_neg_conj                        none
% 11.51/2.00  --large_theory_mode                     true
% 11.51/2.00  --prolific_symb_bound                   200
% 11.51/2.00  --lt_threshold                          2000
% 11.51/2.00  --clause_weak_htbl                      true
% 11.51/2.00  --gc_record_bc_elim                     false
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing Options
% 11.51/2.00  
% 11.51/2.00  --preprocessing_flag                    true
% 11.51/2.00  --time_out_prep_mult                    0.1
% 11.51/2.00  --splitting_mode                        input
% 11.51/2.00  --splitting_grd                         true
% 11.51/2.00  --splitting_cvd                         false
% 11.51/2.00  --splitting_cvd_svl                     false
% 11.51/2.00  --splitting_nvd                         32
% 11.51/2.00  --sub_typing                            true
% 11.51/2.00  --prep_gs_sim                           true
% 11.51/2.00  --prep_unflatten                        true
% 11.51/2.00  --prep_res_sim                          true
% 11.51/2.00  --prep_upred                            true
% 11.51/2.00  --prep_sem_filter                       exhaustive
% 11.51/2.00  --prep_sem_filter_out                   false
% 11.51/2.00  --pred_elim                             true
% 11.51/2.00  --res_sim_input                         true
% 11.51/2.00  --eq_ax_congr_red                       true
% 11.51/2.00  --pure_diseq_elim                       true
% 11.51/2.00  --brand_transform                       false
% 11.51/2.00  --non_eq_to_eq                          false
% 11.51/2.00  --prep_def_merge                        true
% 11.51/2.00  --prep_def_merge_prop_impl              false
% 11.51/2.00  --prep_def_merge_mbd                    true
% 11.51/2.00  --prep_def_merge_tr_red                 false
% 11.51/2.00  --prep_def_merge_tr_cl                  false
% 11.51/2.00  --smt_preprocessing                     true
% 11.51/2.00  --smt_ac_axioms                         fast
% 11.51/2.00  --preprocessed_out                      false
% 11.51/2.00  --preprocessed_stats                    false
% 11.51/2.00  
% 11.51/2.00  ------ Abstraction refinement Options
% 11.51/2.00  
% 11.51/2.00  --abstr_ref                             []
% 11.51/2.00  --abstr_ref_prep                        false
% 11.51/2.00  --abstr_ref_until_sat                   false
% 11.51/2.00  --abstr_ref_sig_restrict                funpre
% 11.51/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.51/2.00  --abstr_ref_under                       []
% 11.51/2.00  
% 11.51/2.00  ------ SAT Options
% 11.51/2.00  
% 11.51/2.00  --sat_mode                              false
% 11.51/2.00  --sat_fm_restart_options                ""
% 11.51/2.00  --sat_gr_def                            false
% 11.51/2.00  --sat_epr_types                         true
% 11.51/2.00  --sat_non_cyclic_types                  false
% 11.51/2.00  --sat_finite_models                     false
% 11.51/2.00  --sat_fm_lemmas                         false
% 11.51/2.00  --sat_fm_prep                           false
% 11.51/2.00  --sat_fm_uc_incr                        true
% 11.51/2.00  --sat_out_model                         small
% 11.51/2.00  --sat_out_clauses                       false
% 11.51/2.00  
% 11.51/2.00  ------ QBF Options
% 11.51/2.00  
% 11.51/2.00  --qbf_mode                              false
% 11.51/2.00  --qbf_elim_univ                         false
% 11.51/2.00  --qbf_dom_inst                          none
% 11.51/2.00  --qbf_dom_pre_inst                      false
% 11.51/2.00  --qbf_sk_in                             false
% 11.51/2.00  --qbf_pred_elim                         true
% 11.51/2.00  --qbf_split                             512
% 11.51/2.00  
% 11.51/2.00  ------ BMC1 Options
% 11.51/2.00  
% 11.51/2.00  --bmc1_incremental                      false
% 11.51/2.00  --bmc1_axioms                           reachable_all
% 11.51/2.00  --bmc1_min_bound                        0
% 11.51/2.00  --bmc1_max_bound                        -1
% 11.51/2.00  --bmc1_max_bound_default                -1
% 11.51/2.00  --bmc1_symbol_reachability              true
% 11.51/2.00  --bmc1_property_lemmas                  false
% 11.51/2.00  --bmc1_k_induction                      false
% 11.51/2.01  --bmc1_non_equiv_states                 false
% 11.51/2.01  --bmc1_deadlock                         false
% 11.51/2.01  --bmc1_ucm                              false
% 11.51/2.01  --bmc1_add_unsat_core                   none
% 11.51/2.01  --bmc1_unsat_core_children              false
% 11.51/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.51/2.01  --bmc1_out_stat                         full
% 11.51/2.01  --bmc1_ground_init                      false
% 11.51/2.01  --bmc1_pre_inst_next_state              false
% 11.51/2.01  --bmc1_pre_inst_state                   false
% 11.51/2.01  --bmc1_pre_inst_reach_state             false
% 11.51/2.01  --bmc1_out_unsat_core                   false
% 11.51/2.01  --bmc1_aig_witness_out                  false
% 11.51/2.01  --bmc1_verbose                          false
% 11.51/2.01  --bmc1_dump_clauses_tptp                false
% 11.51/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.51/2.01  --bmc1_dump_file                        -
% 11.51/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.51/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.51/2.01  --bmc1_ucm_extend_mode                  1
% 11.51/2.01  --bmc1_ucm_init_mode                    2
% 11.51/2.01  --bmc1_ucm_cone_mode                    none
% 11.51/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.51/2.01  --bmc1_ucm_relax_model                  4
% 11.51/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.51/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.51/2.01  --bmc1_ucm_layered_model                none
% 11.51/2.01  --bmc1_ucm_max_lemma_size               10
% 11.51/2.01  
% 11.51/2.01  ------ AIG Options
% 11.51/2.01  
% 11.51/2.01  --aig_mode                              false
% 11.51/2.01  
% 11.51/2.01  ------ Instantiation Options
% 11.51/2.01  
% 11.51/2.01  --instantiation_flag                    true
% 11.51/2.01  --inst_sos_flag                         true
% 11.51/2.01  --inst_sos_phase                        true
% 11.51/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.51/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.51/2.01  --inst_lit_sel_side                     none
% 11.51/2.01  --inst_solver_per_active                1400
% 11.51/2.01  --inst_solver_calls_frac                1.
% 11.51/2.01  --inst_passive_queue_type               priority_queues
% 11.51/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.51/2.01  --inst_passive_queues_freq              [25;2]
% 11.51/2.01  --inst_dismatching                      true
% 11.51/2.01  --inst_eager_unprocessed_to_passive     true
% 11.51/2.01  --inst_prop_sim_given                   true
% 11.51/2.01  --inst_prop_sim_new                     false
% 11.51/2.01  --inst_subs_new                         false
% 11.51/2.01  --inst_eq_res_simp                      false
% 11.51/2.01  --inst_subs_given                       false
% 11.51/2.01  --inst_orphan_elimination               true
% 11.51/2.01  --inst_learning_loop_flag               true
% 11.51/2.01  --inst_learning_start                   3000
% 11.51/2.01  --inst_learning_factor                  2
% 11.51/2.01  --inst_start_prop_sim_after_learn       3
% 11.51/2.01  --inst_sel_renew                        solver
% 11.51/2.01  --inst_lit_activity_flag                true
% 11.51/2.01  --inst_restr_to_given                   false
% 11.51/2.01  --inst_activity_threshold               500
% 11.51/2.01  --inst_out_proof                        true
% 11.51/2.01  
% 11.51/2.01  ------ Resolution Options
% 11.51/2.01  
% 11.51/2.01  --resolution_flag                       false
% 11.51/2.01  --res_lit_sel                           adaptive
% 11.51/2.01  --res_lit_sel_side                      none
% 11.51/2.01  --res_ordering                          kbo
% 11.51/2.01  --res_to_prop_solver                    active
% 11.51/2.01  --res_prop_simpl_new                    false
% 11.51/2.01  --res_prop_simpl_given                  true
% 11.51/2.01  --res_passive_queue_type                priority_queues
% 11.51/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.51/2.01  --res_passive_queues_freq               [15;5]
% 11.51/2.01  --res_forward_subs                      full
% 11.51/2.01  --res_backward_subs                     full
% 11.51/2.01  --res_forward_subs_resolution           true
% 11.51/2.01  --res_backward_subs_resolution          true
% 11.51/2.01  --res_orphan_elimination                true
% 11.51/2.01  --res_time_limit                        2.
% 11.51/2.01  --res_out_proof                         true
% 11.51/2.01  
% 11.51/2.01  ------ Superposition Options
% 11.51/2.01  
% 11.51/2.01  --superposition_flag                    true
% 11.51/2.01  --sup_passive_queue_type                priority_queues
% 11.51/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.51/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.51/2.01  --demod_completeness_check              fast
% 11.51/2.01  --demod_use_ground                      true
% 11.51/2.01  --sup_to_prop_solver                    passive
% 11.51/2.01  --sup_prop_simpl_new                    true
% 11.51/2.01  --sup_prop_simpl_given                  true
% 11.51/2.01  --sup_fun_splitting                     true
% 11.51/2.01  --sup_smt_interval                      50000
% 11.51/2.01  
% 11.51/2.01  ------ Superposition Simplification Setup
% 11.51/2.01  
% 11.51/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.51/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.51/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.51/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.51/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.51/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.51/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.51/2.01  --sup_immed_triv                        [TrivRules]
% 11.51/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/2.01  --sup_immed_bw_main                     []
% 11.51/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.51/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.51/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.51/2.01  --sup_input_bw                          []
% 11.51/2.01  
% 11.51/2.01  ------ Combination Options
% 11.51/2.01  
% 11.51/2.01  --comb_res_mult                         3
% 11.51/2.01  --comb_sup_mult                         2
% 11.51/2.01  --comb_inst_mult                        10
% 11.51/2.01  
% 11.51/2.01  ------ Debug Options
% 11.51/2.01  
% 11.51/2.01  --dbg_backtrace                         false
% 11.51/2.01  --dbg_dump_prop_clauses                 false
% 11.51/2.01  --dbg_dump_prop_clauses_file            -
% 11.51/2.01  --dbg_out_stat                          false
% 11.51/2.01  
% 11.51/2.01  
% 11.51/2.01  
% 11.51/2.01  
% 11.51/2.01  ------ Proving...
% 11.51/2.01  
% 11.51/2.01  
% 11.51/2.01  % SZS status Theorem for theBenchmark.p
% 11.51/2.01  
% 11.51/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.51/2.01  
% 11.51/2.01  fof(f1,axiom,(
% 11.51/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f40,plain,(
% 11.51/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.51/2.01    inference(nnf_transformation,[],[f1])).
% 11.51/2.01  
% 11.51/2.01  fof(f41,plain,(
% 11.51/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.51/2.01    inference(flattening,[],[f40])).
% 11.51/2.01  
% 11.51/2.01  fof(f51,plain,(
% 11.51/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.51/2.01    inference(cnf_transformation,[],[f41])).
% 11.51/2.01  
% 11.51/2.01  fof(f2,axiom,(
% 11.51/2.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f20,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.51/2.01    inference(ennf_transformation,[],[f2])).
% 11.51/2.01  
% 11.51/2.01  fof(f21,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.51/2.01    inference(flattening,[],[f20])).
% 11.51/2.01  
% 11.51/2.01  fof(f52,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.51/2.01    inference(cnf_transformation,[],[f21])).
% 11.51/2.01  
% 11.51/2.01  fof(f3,axiom,(
% 11.51/2.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f53,plain,(
% 11.51/2.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.51/2.01    inference(cnf_transformation,[],[f3])).
% 11.51/2.01  
% 11.51/2.01  fof(f11,axiom,(
% 11.51/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f28,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.51/2.01    inference(ennf_transformation,[],[f11])).
% 11.51/2.01  
% 11.51/2.01  fof(f63,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f28])).
% 11.51/2.01  
% 11.51/2.01  fof(f50,plain,(
% 11.51/2.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.51/2.01    inference(cnf_transformation,[],[f41])).
% 11.51/2.01  
% 11.51/2.01  fof(f87,plain,(
% 11.51/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.51/2.01    inference(equality_resolution,[],[f50])).
% 11.51/2.01  
% 11.51/2.01  fof(f17,conjecture,(
% 11.51/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f18,negated_conjecture,(
% 11.51/2.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.51/2.01    inference(negated_conjecture,[],[f17])).
% 11.51/2.01  
% 11.51/2.01  fof(f38,plain,(
% 11.51/2.01    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 11.51/2.01    inference(ennf_transformation,[],[f18])).
% 11.51/2.01  
% 11.51/2.01  fof(f39,plain,(
% 11.51/2.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 11.51/2.01    inference(flattening,[],[f38])).
% 11.51/2.01  
% 11.51/2.01  fof(f47,plain,(
% 11.51/2.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 11.51/2.01    introduced(choice_axiom,[])).
% 11.51/2.01  
% 11.51/2.01  fof(f48,plain,(
% 11.51/2.01    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 11.51/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f47])).
% 11.51/2.01  
% 11.51/2.01  fof(f83,plain,(
% 11.51/2.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.51/2.01    inference(cnf_transformation,[],[f48])).
% 11.51/2.01  
% 11.51/2.01  fof(f14,axiom,(
% 11.51/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f32,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.51/2.01    inference(ennf_transformation,[],[f14])).
% 11.51/2.01  
% 11.51/2.01  fof(f33,plain,(
% 11.51/2.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.51/2.01    inference(flattening,[],[f32])).
% 11.51/2.01  
% 11.51/2.01  fof(f44,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.51/2.01    inference(nnf_transformation,[],[f33])).
% 11.51/2.01  
% 11.51/2.01  fof(f66,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f44])).
% 11.51/2.01  
% 11.51/2.01  fof(f82,plain,(
% 11.51/2.01    v1_funct_2(sK4,sK1,sK2)),
% 11.51/2.01    inference(cnf_transformation,[],[f48])).
% 11.51/2.01  
% 11.51/2.01  fof(f10,axiom,(
% 11.51/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f19,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.51/2.01    inference(pure_predicate_removal,[],[f10])).
% 11.51/2.01  
% 11.51/2.01  fof(f27,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.51/2.01    inference(ennf_transformation,[],[f19])).
% 11.51/2.01  
% 11.51/2.01  fof(f62,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f27])).
% 11.51/2.01  
% 11.51/2.01  fof(f7,axiom,(
% 11.51/2.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f24,plain,(
% 11.51/2.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.51/2.01    inference(ennf_transformation,[],[f7])).
% 11.51/2.01  
% 11.51/2.01  fof(f43,plain,(
% 11.51/2.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.51/2.01    inference(nnf_transformation,[],[f24])).
% 11.51/2.01  
% 11.51/2.01  fof(f58,plain,(
% 11.51/2.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.51/2.01    inference(cnf_transformation,[],[f43])).
% 11.51/2.01  
% 11.51/2.01  fof(f9,axiom,(
% 11.51/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f26,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.51/2.01    inference(ennf_transformation,[],[f9])).
% 11.51/2.01  
% 11.51/2.01  fof(f61,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f26])).
% 11.51/2.01  
% 11.51/2.01  fof(f85,plain,(
% 11.51/2.01    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 11.51/2.01    inference(cnf_transformation,[],[f48])).
% 11.51/2.01  
% 11.51/2.01  fof(f5,axiom,(
% 11.51/2.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f42,plain,(
% 11.51/2.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.51/2.01    inference(nnf_transformation,[],[f5])).
% 11.51/2.01  
% 11.51/2.01  fof(f55,plain,(
% 11.51/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f42])).
% 11.51/2.01  
% 11.51/2.01  fof(f4,axiom,(
% 11.51/2.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f54,plain,(
% 11.51/2.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f4])).
% 11.51/2.01  
% 11.51/2.01  fof(f13,axiom,(
% 11.51/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f30,plain,(
% 11.51/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 11.51/2.01    inference(ennf_transformation,[],[f13])).
% 11.51/2.01  
% 11.51/2.01  fof(f31,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 11.51/2.01    inference(flattening,[],[f30])).
% 11.51/2.01  
% 11.51/2.01  fof(f65,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 11.51/2.01    inference(cnf_transformation,[],[f31])).
% 11.51/2.01  
% 11.51/2.01  fof(f86,plain,(
% 11.51/2.01    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 11.51/2.01    inference(cnf_transformation,[],[f48])).
% 11.51/2.01  
% 11.51/2.01  fof(f81,plain,(
% 11.51/2.01    v1_funct_1(sK4)),
% 11.51/2.01    inference(cnf_transformation,[],[f48])).
% 11.51/2.01  
% 11.51/2.01  fof(f68,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f44])).
% 11.51/2.01  
% 11.51/2.01  fof(f12,axiom,(
% 11.51/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f29,plain,(
% 11.51/2.01    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.51/2.01    inference(ennf_transformation,[],[f12])).
% 11.51/2.01  
% 11.51/2.01  fof(f64,plain,(
% 11.51/2.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.51/2.01    inference(cnf_transformation,[],[f29])).
% 11.51/2.01  
% 11.51/2.01  fof(f84,plain,(
% 11.51/2.01    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 11.51/2.01    inference(cnf_transformation,[],[f48])).
% 11.51/2.01  
% 11.51/2.01  fof(f15,axiom,(
% 11.51/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.51/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.01  
% 11.51/2.01  fof(f34,plain,(
% 11.51/2.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.51/2.01    inference(ennf_transformation,[],[f15])).
% 11.51/2.01  
% 11.51/2.01  fof(f35,plain,(
% 11.51/2.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.51/2.01    inference(flattening,[],[f34])).
% 11.51/2.01  
% 11.51/2.01  fof(f73,plain,(
% 11.51/2.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.51/2.01    inference(cnf_transformation,[],[f35])).
% 11.51/2.01  
% 11.51/2.01  cnf(c_1573,plain,
% 11.51/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.51/2.01      | v1_funct_2(X3,X4,X5)
% 11.51/2.01      | X3 != X0
% 11.51/2.01      | X4 != X1
% 11.51/2.01      | X5 != X2 ),
% 11.51/2.01      theory(equality) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_6756,plain,
% 11.51/2.01      ( v1_funct_2(X0,X1,X2)
% 11.51/2.01      | ~ v1_funct_2(sK4,k1_relat_1(sK4),X3)
% 11.51/2.01      | X2 != X3
% 11.51/2.01      | X1 != k1_relat_1(sK4)
% 11.51/2.01      | X0 != sK4 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1573]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_17521,plain,
% 11.51/2.01      ( ~ v1_funct_2(sK4,k1_relat_1(sK4),X0)
% 11.51/2.01      | v1_funct_2(sK4,sK1,sK3)
% 11.51/2.01      | sK3 != X0
% 11.51/2.01      | sK1 != k1_relat_1(sK4)
% 11.51/2.01      | sK4 != sK4 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_6756]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_60013,plain,
% 11.51/2.01      ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
% 11.51/2.01      | v1_funct_2(sK4,sK1,sK3)
% 11.51/2.01      | sK3 != k2_relat_1(sK4)
% 11.51/2.01      | sK1 != k1_relat_1(sK4)
% 11.51/2.01      | sK4 != sK4 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_17521]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_0,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.51/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2473,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_27344,plain,
% 11.51/2.01      ( ~ r1_tarski(k2_relat_1(sK4),sK3)
% 11.51/2.01      | ~ r1_tarski(sK3,k2_relat_1(sK4))
% 11.51/2.01      | sK3 = k2_relat_1(sK4) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2473]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.51/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_7204,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,X1)
% 11.51/2.01      | ~ r1_tarski(X1,k2_relat_1(sK4))
% 11.51/2.01      | r1_tarski(X0,k2_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_16878,plain,
% 11.51/2.01      ( r1_tarski(X0,k2_relat_1(sK4))
% 11.51/2.01      | ~ r1_tarski(X0,k1_xboole_0)
% 11.51/2.01      | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_7204]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_27336,plain,
% 11.51/2.01      ( r1_tarski(sK3,k2_relat_1(sK4))
% 11.51/2.01      | ~ r1_tarski(sK3,k1_xboole_0)
% 11.51/2.01      | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_16878]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_26929,plain,
% 11.51/2.01      ( ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
% 11.51/2.01      | v1_funct_2(sK4,sK1,sK3)
% 11.51/2.01      | sK3 != sK3
% 11.51/2.01      | sK1 != k1_relat_1(sK4)
% 11.51/2.01      | sK4 != sK4 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_17521]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4,plain,
% 11.51/2.01      ( r1_tarski(k1_xboole_0,X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_14581,plain,
% 11.51/2.01      ( r1_tarski(k1_xboole_0,k2_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_14,plain,
% 11.51/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_14443,plain,
% 11.51/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
% 11.51/2.01      | k1_relset_1(k1_relat_1(sK4),sK3,sK4) = k1_relat_1(sK4) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_14]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_1,plain,
% 11.51/2.01      ( r1_tarski(X0,X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f87]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_13364,plain,
% 11.51/2.01      ( r1_tarski(sK1,sK1) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2337,plain,
% 11.51/2.01      ( r1_tarski(X0,X0) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_35,negated_conjecture,
% 11.51/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.51/2.01      inference(cnf_transformation,[],[f83]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2320,plain,
% 11.51/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_22,plain,
% 11.51/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.51/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | k1_relset_1(X1,X2,X0) = X1
% 11.51/2.01      | k1_xboole_0 = X2 ),
% 11.51/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2322,plain,
% 11.51/2.01      ( k1_relset_1(X0,X1,X2) = X0
% 11.51/2.01      | k1_xboole_0 = X1
% 11.51/2.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.51/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4534,plain,
% 11.51/2.01      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 11.51/2.01      | sK2 = k1_xboole_0
% 11.51/2.01      | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_2320,c_2322]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2330,plain,
% 11.51/2.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.51/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3390,plain,
% 11.51/2.01      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_2320,c_2330]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4540,plain,
% 11.51/2.01      ( k1_relat_1(sK4) = sK1
% 11.51/2.01      | sK2 = k1_xboole_0
% 11.51/2.01      | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
% 11.51/2.01      inference(demodulation,[status(thm)],[c_4534,c_3390]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_36,negated_conjecture,
% 11.51/2.01      ( v1_funct_2(sK4,sK1,sK2) ),
% 11.51/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_39,plain,
% 11.51/2.01      ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_5122,plain,
% 11.51/2.01      ( sK2 = k1_xboole_0 | k1_relat_1(sK4) = sK1 ),
% 11.51/2.01      inference(global_propositional_subsumption,
% 11.51/2.01                [status(thm)],
% 11.51/2.01                [c_4540,c_39]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_5123,plain,
% 11.51/2.01      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 11.51/2.01      inference(renaming,[status(thm)],[c_5122]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_13,plain,
% 11.51/2.01      ( v4_relat_1(X0,X1)
% 11.51/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.51/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_10,plain,
% 11.51/2.01      ( ~ v4_relat_1(X0,X1)
% 11.51/2.01      | r1_tarski(k1_relat_1(X0),X1)
% 11.51/2.01      | ~ v1_relat_1(X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_455,plain,
% 11.51/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | r1_tarski(k1_relat_1(X0),X1)
% 11.51/2.01      | ~ v1_relat_1(X0) ),
% 11.51/2.01      inference(resolution,[status(thm)],[c_13,c_10]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_12,plain,
% 11.51/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | v1_relat_1(X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_459,plain,
% 11.51/2.01      ( r1_tarski(k1_relat_1(X0),X1)
% 11.51/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.51/2.01      inference(global_propositional_subsumption,
% 11.51/2.01                [status(thm)],
% 11.51/2.01                [c_455,c_12]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_460,plain,
% 11.51/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.51/2.01      inference(renaming,[status(thm)],[c_459]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2317,plain,
% 11.51/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.51/2.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3901,plain,
% 11.51/2.01      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_2320,c_2317]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2336,plain,
% 11.51/2.01      ( r1_tarski(X0,X1) != iProver_top
% 11.51/2.01      | r1_tarski(X1,X2) != iProver_top
% 11.51/2.01      | r1_tarski(X0,X2) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4137,plain,
% 11.51/2.01      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 11.51/2.01      | r1_tarski(sK1,X0) != iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_3901,c_2336]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2338,plain,
% 11.51/2.01      ( X0 = X1
% 11.51/2.01      | r1_tarski(X1,X0) != iProver_top
% 11.51/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4305,plain,
% 11.51/2.01      ( k1_relat_1(sK4) = X0
% 11.51/2.01      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 11.51/2.01      | r1_tarski(sK1,X0) != iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_4137,c_2338]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_5531,plain,
% 11.51/2.01      ( k1_relat_1(sK4) = X0
% 11.51/2.01      | sK2 = k1_xboole_0
% 11.51/2.01      | r1_tarski(X0,sK1) != iProver_top
% 11.51/2.01      | r1_tarski(sK1,X0) != iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_5123,c_4305]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_33,negated_conjecture,
% 11.51/2.01      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 11.51/2.01      inference(cnf_transformation,[],[f85]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_7,plain,
% 11.51/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.51/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_110,plain,
% 11.51/2.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 11.51/2.01      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_109,plain,
% 11.51/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.51/2.01      | r1_tarski(X0,X1) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_111,plain,
% 11.51/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.51/2.01      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_109]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_5,plain,
% 11.51/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.51/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_116,plain,
% 11.51/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_5]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_115,plain,
% 11.51/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_117,plain,
% 11.51/2.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_115]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_125,plain,
% 11.51/2.01      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.51/2.01      | k1_xboole_0 = k1_xboole_0 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_1563,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2408,plain,
% 11.51/2.01      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1563]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2409,plain,
% 11.51/2.01      ( sK2 != k1_xboole_0
% 11.51/2.01      | k1_xboole_0 = sK2
% 11.51/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2408]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_1562,plain,( X0 = X0 ),theory(equality) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3100,plain,
% 11.51/2.01      ( sK1 = sK1 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1562]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2760,plain,
% 11.51/2.01      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1563]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3250,plain,
% 11.51/2.01      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2760]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3251,plain,
% 11.51/2.01      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3250]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_1564,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.51/2.01      theory(equality) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3417,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,X1)
% 11.51/2.01      | r1_tarski(sK1,k1_xboole_0)
% 11.51/2.01      | sK1 != X0
% 11.51/2.01      | k1_xboole_0 != X1 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1564]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3418,plain,
% 11.51/2.01      ( sK1 != X0
% 11.51/2.01      | k1_xboole_0 != X1
% 11.51/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.51/2.01      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_3417]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3420,plain,
% 11.51/2.01      ( sK1 != k1_xboole_0
% 11.51/2.01      | k1_xboole_0 != k1_xboole_0
% 11.51/2.01      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 11.51/2.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3418]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4136,plain,
% 11.51/2.01      ( k1_relat_1(sK4) = sK1
% 11.51/2.01      | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_3901,c_2338]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_6117,plain,
% 11.51/2.01      ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_6118,plain,
% 11.51/2.01      ( r1_tarski(k1_xboole_0,k1_relat_1(sK4)) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_6117]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_6732,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | X0 = sK1 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_6733,plain,
% 11.51/2.01      ( X0 = sK1
% 11.51/2.01      | r1_tarski(X0,sK1) != iProver_top
% 11.51/2.01      | r1_tarski(sK1,X0) != iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_6732]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2996,plain,
% 11.51/2.01      ( X0 != X1 | k1_relat_1(sK4) != X1 | k1_relat_1(sK4) = X0 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1563]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_9146,plain,
% 11.51/2.01      ( X0 != sK1 | k1_relat_1(sK4) = X0 | k1_relat_1(sK4) != sK1 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2996]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3568,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,X1)
% 11.51/2.01      | ~ r1_tarski(X1,k1_relat_1(sK4))
% 11.51/2.01      | r1_tarski(X0,k1_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_11752,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 11.51/2.01      | ~ r1_tarski(sK1,X0)
% 11.51/2.01      | r1_tarski(sK1,k1_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3568]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_11753,plain,
% 11.51/2.01      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 11.51/2.01      | r1_tarski(sK1,X0) != iProver_top
% 11.51/2.01      | r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_11752]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_11755,plain,
% 11.51/2.01      ( r1_tarski(sK1,k1_relat_1(sK4)) = iProver_top
% 11.51/2.01      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 11.51/2.01      | r1_tarski(k1_xboole_0,k1_relat_1(sK4)) != iProver_top ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_11753]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_13175,plain,
% 11.51/2.01      ( k1_relat_1(sK4) = X0
% 11.51/2.01      | r1_tarski(X0,sK1) != iProver_top
% 11.51/2.01      | r1_tarski(sK1,X0) != iProver_top ),
% 11.51/2.01      inference(global_propositional_subsumption,
% 11.51/2.01                [status(thm)],
% 11.51/2.01                [c_5531,c_33,c_110,c_111,c_116,c_117,c_125,c_2409,c_3100,
% 11.51/2.01                 c_3251,c_3420,c_4136,c_6118,c_6733,c_9146,c_11755]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_13181,plain,
% 11.51/2.01      ( k1_relat_1(sK4) = sK1 | r1_tarski(sK1,sK1) != iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_2337,c_13175]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_13194,plain,
% 11.51/2.01      ( ~ r1_tarski(sK1,sK1) | k1_relat_1(sK4) = sK1 ),
% 11.51/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_13181]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_16,plain,
% 11.51/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 11.51/2.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.51/2.01      | ~ v1_relat_1(X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2517,plain,
% 11.51/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.51/2.01      | ~ r1_tarski(k2_relat_1(sK4),X1)
% 11.51/2.01      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 11.51/2.01      | ~ v1_relat_1(sK4) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_16]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4204,plain,
% 11.51/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
% 11.51/2.01      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 11.51/2.01      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 11.51/2.01      | ~ v1_relat_1(sK4) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2517]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_7062,plain,
% 11.51/2.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
% 11.51/2.01      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 11.51/2.01      | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
% 11.51/2.01      | ~ v1_relat_1(sK4) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_4204]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_6361,plain,
% 11.51/2.01      ( k1_relat_1(sK4) != sK1 | sK1 = k1_relat_1(sK4) | sK1 != sK1 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3250]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2707,plain,
% 11.51/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1564]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3253,plain,
% 11.51/2.01      ( ~ r1_tarski(sK3,X0) | r1_tarski(sK3,X1) | X1 != X0 | sK3 != sK3 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2707]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_5741,plain,
% 11.51/2.01      ( r1_tarski(sK3,X0)
% 11.51/2.01      | ~ r1_tarski(sK3,sK3)
% 11.51/2.01      | X0 != sK3
% 11.51/2.01      | sK3 != sK3 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3253]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_5743,plain,
% 11.51/2.01      ( ~ r1_tarski(sK3,sK3)
% 11.51/2.01      | r1_tarski(sK3,k1_xboole_0)
% 11.51/2.01      | sK3 != sK3
% 11.51/2.01      | k1_xboole_0 != sK3 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_5741]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2328,plain,
% 11.51/2.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.51/2.01      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 11.51/2.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.51/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_32,negated_conjecture,
% 11.51/2.01      ( ~ v1_funct_2(sK4,sK1,sK3)
% 11.51/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 11.51/2.01      | ~ v1_funct_1(sK4) ),
% 11.51/2.01      inference(cnf_transformation,[],[f86]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_37,negated_conjecture,
% 11.51/2.01      ( v1_funct_1(sK4) ),
% 11.51/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_206,plain,
% 11.51/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 11.51/2.01      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 11.51/2.01      inference(global_propositional_subsumption,
% 11.51/2.01                [status(thm)],
% 11.51/2.01                [c_32,c_37]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_207,negated_conjecture,
% 11.51/2.01      ( ~ v1_funct_2(sK4,sK1,sK3)
% 11.51/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 11.51/2.01      inference(renaming,[status(thm)],[c_206]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2318,plain,
% 11.51/2.01      ( v1_funct_2(sK4,sK1,sK3) != iProver_top
% 11.51/2.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4896,plain,
% 11.51/2.01      ( v1_funct_2(sK4,sK1,sK3) != iProver_top
% 11.51/2.01      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 11.51/2.01      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 11.51/2.01      | v1_relat_1(sK4) != iProver_top ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_2328,c_2318]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4905,plain,
% 11.51/2.01      ( ~ v1_funct_2(sK4,sK1,sK3)
% 11.51/2.01      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 11.51/2.01      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 11.51/2.01      | ~ v1_relat_1(sK4) ),
% 11.51/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_4896]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_20,plain,
% 11.51/2.01      ( v1_funct_2(X0,X1,X2)
% 11.51/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | k1_relset_1(X1,X2,X0) != X1
% 11.51/2.01      | k1_xboole_0 = X2 ),
% 11.51/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3054,plain,
% 11.51/2.01      ( v1_funct_2(X0,X1,sK3)
% 11.51/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 11.51/2.01      | k1_relset_1(X1,sK3,X0) != X1
% 11.51/2.01      | k1_xboole_0 = sK3 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_20]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_4180,plain,
% 11.51/2.01      ( v1_funct_2(sK4,k1_relat_1(sK4),sK3)
% 11.51/2.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
% 11.51/2.01      | k1_relset_1(k1_relat_1(sK4),sK3,sK4) != k1_relat_1(sK4)
% 11.51/2.01      | k1_xboole_0 = sK3 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_3054]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3888,plain,
% 11.51/2.01      ( sK4 = sK4 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1562]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2854,plain,
% 11.51/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.51/2.01      | r1_tarski(k1_relat_1(sK4),X0) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_460]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3528,plain,
% 11.51/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.51/2.01      | r1_tarski(k1_relat_1(sK4),sK1) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2854]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_15,plain,
% 11.51/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.51/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2329,plain,
% 11.51/2.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.51/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3375,plain,
% 11.51/2.01      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 11.51/2.01      inference(superposition,[status(thm)],[c_2320,c_2329]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_34,negated_conjecture,
% 11.51/2.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 11.51/2.01      inference(cnf_transformation,[],[f84]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2321,plain,
% 11.51/2.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 11.51/2.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3464,plain,
% 11.51/2.01      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 11.51/2.01      inference(demodulation,[status(thm)],[c_3375,c_2321]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3465,plain,
% 11.51/2.01      ( r1_tarski(k2_relat_1(sK4),sK3) ),
% 11.51/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_3464]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3403,plain,
% 11.51/2.01      ( r1_tarski(sK3,sK3) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_3366,plain,
% 11.51/2.01      ( r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2420,plain,
% 11.51/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.51/2.01      | v1_relat_1(sK4) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_12]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2509,plain,
% 11.51/2.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.51/2.01      | v1_relat_1(sK4) ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_2420]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_2493,plain,
% 11.51/2.01      ( sK3 = sK3 ),
% 11.51/2.01      inference(instantiation,[status(thm)],[c_1562]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_24,plain,
% 11.51/2.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 11.51/2.01      | ~ v1_funct_1(X0)
% 11.51/2.01      | ~ v1_relat_1(X0) ),
% 11.51/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_536,plain,
% 11.51/2.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 11.51/2.01      | ~ v1_relat_1(X0)
% 11.51/2.01      | sK4 != X0 ),
% 11.51/2.01      inference(resolution_lifted,[status(thm)],[c_24,c_37]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(c_537,plain,
% 11.51/2.01      ( v1_funct_2(sK4,k1_relat_1(sK4),k2_relat_1(sK4))
% 11.51/2.01      | ~ v1_relat_1(sK4) ),
% 11.51/2.01      inference(unflattening,[status(thm)],[c_536]) ).
% 11.51/2.01  
% 11.51/2.01  cnf(contradiction,plain,
% 11.51/2.01      ( $false ),
% 11.51/2.01      inference(minisat,
% 11.51/2.01                [status(thm)],
% 11.51/2.01                [c_60013,c_27344,c_27336,c_26929,c_14581,c_14443,c_13364,
% 11.51/2.01                 c_13194,c_7062,c_6361,c_5743,c_4905,c_4180,c_3888,
% 11.51/2.01                 c_3528,c_3465,c_3403,c_3366,c_3100,c_2509,c_2493,c_537,
% 11.51/2.01                 c_35]) ).
% 11.51/2.01  
% 11.51/2.01  
% 11.51/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.51/2.01  
% 11.51/2.01  ------                               Statistics
% 11.51/2.01  
% 11.51/2.01  ------ General
% 11.51/2.01  
% 11.51/2.01  abstr_ref_over_cycles:                  0
% 11.51/2.01  abstr_ref_under_cycles:                 0
% 11.51/2.01  gc_basic_clause_elim:                   0
% 11.51/2.01  forced_gc_time:                         0
% 11.51/2.01  parsing_time:                           0.01
% 11.51/2.01  unif_index_cands_time:                  0.
% 11.51/2.01  unif_index_add_time:                    0.
% 11.51/2.01  orderings_time:                         0.
% 11.51/2.01  out_proof_time:                         0.012
% 11.51/2.01  total_time:                             1.449
% 11.51/2.01  num_of_symbols:                         53
% 11.51/2.01  num_of_terms:                           28898
% 11.51/2.01  
% 11.51/2.01  ------ Preprocessing
% 11.51/2.01  
% 11.51/2.01  num_of_splits:                          4
% 11.51/2.01  num_of_split_atoms:                     2
% 11.51/2.01  num_of_reused_defs:                     2
% 11.51/2.01  num_eq_ax_congr_red:                    14
% 11.51/2.01  num_of_sem_filtered_clauses:            1
% 11.51/2.01  num_of_subtypes:                        0
% 11.51/2.01  monotx_restored_types:                  0
% 11.51/2.01  sat_num_of_epr_types:                   0
% 11.51/2.01  sat_num_of_non_cyclic_types:            0
% 11.51/2.01  sat_guarded_non_collapsed_types:        0
% 11.51/2.01  num_pure_diseq_elim:                    0
% 11.51/2.01  simp_replaced_by:                       0
% 11.51/2.01  res_preprocessed:                       166
% 11.51/2.01  prep_upred:                             0
% 11.51/2.01  prep_unflattend:                        44
% 11.51/2.01  smt_new_axioms:                         0
% 11.51/2.01  pred_elim_cands:                        4
% 11.51/2.01  pred_elim:                              3
% 11.51/2.01  pred_elim_cl:                           1
% 11.51/2.01  pred_elim_cycles:                       6
% 11.51/2.01  merged_defs:                            8
% 11.51/2.01  merged_defs_ncl:                        0
% 11.51/2.01  bin_hyper_res:                          8
% 11.51/2.01  prep_cycles:                            4
% 11.51/2.01  pred_elim_time:                         0.016
% 11.51/2.01  splitting_time:                         0.
% 11.51/2.01  sem_filter_time:                        0.
% 11.51/2.01  monotx_time:                            0.001
% 11.51/2.01  subtype_inf_time:                       0.
% 11.51/2.01  
% 11.51/2.01  ------ Problem properties
% 11.51/2.01  
% 11.51/2.01  clauses:                                37
% 11.51/2.01  conjectures:                            5
% 11.51/2.01  epr:                                    6
% 11.51/2.01  horn:                                   27
% 11.51/2.01  ground:                                 11
% 11.51/2.01  unary:                                  6
% 11.51/2.01  binary:                                 10
% 11.51/2.01  lits:                                   95
% 11.51/2.01  lits_eq:                                18
% 11.51/2.01  fd_pure:                                0
% 11.51/2.01  fd_pseudo:                              0
% 11.51/2.01  fd_cond:                                3
% 11.51/2.01  fd_pseudo_cond:                         1
% 11.51/2.01  ac_symbols:                             0
% 11.51/2.01  
% 11.51/2.01  ------ Propositional Solver
% 11.51/2.01  
% 11.51/2.01  prop_solver_calls:                      34
% 11.51/2.01  prop_fast_solver_calls:                 3249
% 11.51/2.01  smt_solver_calls:                       0
% 11.51/2.01  smt_fast_solver_calls:                  0
% 11.51/2.01  prop_num_of_clauses:                    21684
% 11.51/2.01  prop_preprocess_simplified:             41991
% 11.51/2.01  prop_fo_subsumed:                       224
% 11.51/2.01  prop_solver_time:                       0.
% 11.51/2.01  smt_solver_time:                        0.
% 11.51/2.01  smt_fast_solver_time:                   0.
% 11.51/2.01  prop_fast_solver_time:                  0.
% 11.51/2.01  prop_unsat_core_time:                   0.002
% 11.51/2.01  
% 11.51/2.01  ------ QBF
% 11.51/2.01  
% 11.51/2.01  qbf_q_res:                              0
% 11.51/2.01  qbf_num_tautologies:                    0
% 11.51/2.01  qbf_prep_cycles:                        0
% 11.51/2.01  
% 11.51/2.01  ------ BMC1
% 11.51/2.01  
% 11.51/2.01  bmc1_current_bound:                     -1
% 11.51/2.01  bmc1_last_solved_bound:                 -1
% 11.51/2.01  bmc1_unsat_core_size:                   -1
% 11.51/2.01  bmc1_unsat_core_parents_size:           -1
% 11.51/2.01  bmc1_merge_next_fun:                    0
% 11.51/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.51/2.01  
% 11.51/2.01  ------ Instantiation
% 11.51/2.01  
% 11.51/2.01  inst_num_of_clauses:                    5151
% 11.51/2.01  inst_num_in_passive:                    2934
% 11.51/2.01  inst_num_in_active:                     2089
% 11.51/2.01  inst_num_in_unprocessed:                133
% 11.51/2.01  inst_num_of_loops:                      2543
% 11.51/2.01  inst_num_of_learning_restarts:          0
% 11.51/2.01  inst_num_moves_active_passive:          446
% 11.51/2.01  inst_lit_activity:                      0
% 11.51/2.01  inst_lit_activity_moves:                0
% 11.51/2.01  inst_num_tautologies:                   0
% 11.51/2.01  inst_num_prop_implied:                  0
% 11.51/2.01  inst_num_existing_simplified:           0
% 11.51/2.01  inst_num_eq_res_simplified:             0
% 11.51/2.01  inst_num_child_elim:                    0
% 11.51/2.01  inst_num_of_dismatching_blockings:      3610
% 11.51/2.01  inst_num_of_non_proper_insts:           8399
% 11.51/2.01  inst_num_of_duplicates:                 0
% 11.51/2.01  inst_inst_num_from_inst_to_res:         0
% 11.51/2.01  inst_dismatching_checking_time:         0.
% 11.51/2.01  
% 11.51/2.01  ------ Resolution
% 11.51/2.01  
% 11.51/2.01  res_num_of_clauses:                     0
% 11.51/2.01  res_num_in_passive:                     0
% 11.51/2.01  res_num_in_active:                      0
% 11.51/2.01  res_num_of_loops:                       170
% 11.51/2.01  res_forward_subset_subsumed:            599
% 11.51/2.01  res_backward_subset_subsumed:           22
% 11.51/2.01  res_forward_subsumed:                   0
% 11.51/2.01  res_backward_subsumed:                  0
% 11.51/2.01  res_forward_subsumption_resolution:     0
% 11.51/2.01  res_backward_subsumption_resolution:    0
% 11.51/2.01  res_clause_to_clause_subsumption:       14588
% 11.51/2.01  res_orphan_elimination:                 0
% 11.51/2.01  res_tautology_del:                      806
% 11.51/2.01  res_num_eq_res_simplified:              0
% 11.51/2.01  res_num_sel_changes:                    0
% 11.51/2.01  res_moves_from_active_to_pass:          0
% 11.51/2.01  
% 11.51/2.01  ------ Superposition
% 11.51/2.01  
% 11.51/2.01  sup_time_total:                         0.
% 11.51/2.01  sup_time_generating:                    0.
% 11.51/2.01  sup_time_sim_full:                      0.
% 11.51/2.01  sup_time_sim_immed:                     0.
% 11.51/2.01  
% 11.51/2.01  sup_num_of_clauses:                     1967
% 11.51/2.01  sup_num_in_active:                      378
% 11.51/2.01  sup_num_in_passive:                     1589
% 11.51/2.01  sup_num_of_loops:                       508
% 11.51/2.01  sup_fw_superposition:                   1565
% 11.51/2.01  sup_bw_superposition:                   2108
% 11.51/2.01  sup_immediate_simplified:               1211
% 11.51/2.01  sup_given_eliminated:                   2
% 11.51/2.01  comparisons_done:                       0
% 11.51/2.01  comparisons_avoided:                    30
% 11.51/2.01  
% 11.51/2.01  ------ Simplifications
% 11.51/2.01  
% 11.51/2.01  
% 11.51/2.01  sim_fw_subset_subsumed:                 200
% 11.51/2.01  sim_bw_subset_subsumed:                 101
% 11.51/2.01  sim_fw_subsumed:                        801
% 11.51/2.01  sim_bw_subsumed:                        127
% 11.51/2.01  sim_fw_subsumption_res:                 0
% 11.51/2.01  sim_bw_subsumption_res:                 0
% 11.51/2.01  sim_tautology_del:                      8
% 11.51/2.01  sim_eq_tautology_del:                   81
% 11.51/2.01  sim_eq_res_simp:                        1
% 11.51/2.01  sim_fw_demodulated:                     182
% 11.51/2.01  sim_bw_demodulated:                     79
% 11.51/2.01  sim_light_normalised:                   463
% 11.51/2.01  sim_joinable_taut:                      0
% 11.51/2.01  sim_joinable_simp:                      0
% 11.51/2.01  sim_ac_normalised:                      0
% 11.51/2.01  sim_smt_subsumption:                    0
% 11.51/2.01  
%------------------------------------------------------------------------------
