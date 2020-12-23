%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:07 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  165 (2275 expanded)
%              Number of clauses        :  101 ( 725 expanded)
%              Number of leaves         :   15 ( 430 expanded)
%              Depth                    :   30
%              Number of atoms          :  525 (9652 expanded)
%              Number of equality atoms :  263 (1993 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
      & r1_tarski(sK1,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
    & r1_tarski(sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f42])).

fof(f71,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] : k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X3,X2] :
      ( ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
     => k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f40])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2268,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2271,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2274,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5072,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_2274])).

cnf(c_6371,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_5072])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_61,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_63,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2409,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2410,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_2412,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_2662,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2665,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2662])).

cnf(c_2667,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2665])).

cnf(c_6978,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6371,c_63,c_2412,c_2667])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2265,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_947,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_949,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_947,c_26])).

cnf(c_2264,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2266,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3389,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2264,c_2266])).

cnf(c_3821,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_949,c_3389])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_409,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_2262,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_3825,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3821,c_2262])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2414,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2415,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_3929,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | sK2 = k1_xboole_0
    | k7_relat_1(sK4,X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3825,c_31,c_2415])).

cnf(c_3930,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3929])).

cnf(c_3939,plain,
    ( k7_relat_1(sK4,sK3) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2265,c_3930])).

cnf(c_16,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_349,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k1_funct_1(X3,sK0(X0,X3)) != k1_funct_1(X0,sK0(X0,X3))
    | sK4 != X3
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_24])).

cnf(c_350,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_352,plain,
    ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_28,c_27,c_26])).

cnf(c_353,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_352])).

cnf(c_386,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(resolution_lifted,[status(thm)],[c_28,c_353])).

cnf(c_862,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k2_partfun1(sK1,sK2,sK4,sK3) != k1_xboole_0
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | sK2 != k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_386])).

cnf(c_863,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k2_partfun1(sK1,sK2,sK4,sK3) != k1_xboole_0
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_976,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_386])).

cnf(c_1051,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_976])).

cnf(c_1066,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_863,c_1051])).

cnf(c_1067,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_2259,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_375,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_2263,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2431,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2264,c_2263])).

cnf(c_2512,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
    | k7_relat_1(sK4,sK3) != sK4
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2259,c_2431])).

cnf(c_3951,plain,
    ( k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
    | k7_relat_1(sK4,sK3) != sK4
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3939,c_2512])).

cnf(c_3957,plain,
    ( k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
    | sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3951,c_3939])).

cnf(c_4032,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3939,c_3957])).

cnf(c_4038,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3939,c_4032])).

cnf(c_4130,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4038,c_31])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_891,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X0
    | sK2 != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_892,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_891])).

cnf(c_2261,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2346,plain,
    ( sK4 = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2261,c_5])).

cnf(c_4137,plain,
    ( sK4 = k1_xboole_0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4130,c_2346])).

cnf(c_4161,plain,
    ( sK4 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4137])).

cnf(c_4142,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4130,c_2264])).

cnf(c_4144,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4142,c_5])).

cnf(c_4165,plain,
    ( sK4 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4161,c_4144])).

cnf(c_2590,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2591,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2590])).

cnf(c_2593,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2591])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2741,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2742,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2741])).

cnf(c_2744,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_2776,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2779,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2776])).

cnf(c_5148,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4165,c_2593,c_2744,c_2779,c_4144])).

cnf(c_4138,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
    | k7_relat_1(sK4,sK3) != sK4
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4130,c_2512])).

cnf(c_4157,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
    | k7_relat_1(sK4,sK3) != sK4
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4138,c_5])).

cnf(c_5151,plain,
    ( k1_funct_1(k7_relat_1(k1_xboole_0,sK3),sK0(k7_relat_1(k1_xboole_0,sK3),k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK0(k7_relat_1(k1_xboole_0,sK3),k1_xboole_0))
    | k7_relat_1(k1_xboole_0,sK3) != k1_xboole_0
    | m1_subset_1(k7_relat_1(k1_xboole_0,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5148,c_4157])).

cnf(c_6982,plain,
    ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6978,c_5151])).

cnf(c_6987,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6982])).

cnf(c_84,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_86,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_79,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_81,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6987,c_86,c_81])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.53/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.01  
% 2.53/1.01  ------  iProver source info
% 2.53/1.01  
% 2.53/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.01  git: non_committed_changes: false
% 2.53/1.01  git: last_make_outside_of_git: false
% 2.53/1.01  
% 2.53/1.01  ------ 
% 2.53/1.01  
% 2.53/1.01  ------ Input Options
% 2.53/1.01  
% 2.53/1.01  --out_options                           all
% 2.53/1.01  --tptp_safe_out                         true
% 2.53/1.01  --problem_path                          ""
% 2.53/1.01  --include_path                          ""
% 2.53/1.01  --clausifier                            res/vclausify_rel
% 2.53/1.01  --clausifier_options                    --mode clausify
% 2.53/1.01  --stdin                                 false
% 2.53/1.01  --stats_out                             all
% 2.53/1.01  
% 2.53/1.01  ------ General Options
% 2.53/1.01  
% 2.53/1.01  --fof                                   false
% 2.53/1.01  --time_out_real                         305.
% 2.53/1.01  --time_out_virtual                      -1.
% 2.53/1.01  --symbol_type_check                     false
% 2.53/1.01  --clausify_out                          false
% 2.53/1.01  --sig_cnt_out                           false
% 2.53/1.01  --trig_cnt_out                          false
% 2.53/1.01  --trig_cnt_out_tolerance                1.
% 2.53/1.01  --trig_cnt_out_sk_spl                   false
% 2.53/1.01  --abstr_cl_out                          false
% 2.53/1.01  
% 2.53/1.01  ------ Global Options
% 2.53/1.01  
% 2.53/1.01  --schedule                              default
% 2.53/1.01  --add_important_lit                     false
% 2.53/1.01  --prop_solver_per_cl                    1000
% 2.53/1.01  --min_unsat_core                        false
% 2.53/1.01  --soft_assumptions                      false
% 2.53/1.01  --soft_lemma_size                       3
% 2.53/1.01  --prop_impl_unit_size                   0
% 2.53/1.01  --prop_impl_unit                        []
% 2.53/1.01  --share_sel_clauses                     true
% 2.53/1.01  --reset_solvers                         false
% 2.53/1.01  --bc_imp_inh                            [conj_cone]
% 2.53/1.01  --conj_cone_tolerance                   3.
% 2.53/1.01  --extra_neg_conj                        none
% 2.53/1.01  --large_theory_mode                     true
% 2.53/1.01  --prolific_symb_bound                   200
% 2.53/1.01  --lt_threshold                          2000
% 2.53/1.01  --clause_weak_htbl                      true
% 2.53/1.01  --gc_record_bc_elim                     false
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing Options
% 2.53/1.01  
% 2.53/1.01  --preprocessing_flag                    true
% 2.53/1.01  --time_out_prep_mult                    0.1
% 2.53/1.01  --splitting_mode                        input
% 2.53/1.01  --splitting_grd                         true
% 2.53/1.01  --splitting_cvd                         false
% 2.53/1.01  --splitting_cvd_svl                     false
% 2.53/1.01  --splitting_nvd                         32
% 2.53/1.01  --sub_typing                            true
% 2.53/1.01  --prep_gs_sim                           true
% 2.53/1.01  --prep_unflatten                        true
% 2.53/1.01  --prep_res_sim                          true
% 2.53/1.01  --prep_upred                            true
% 2.53/1.01  --prep_sem_filter                       exhaustive
% 2.53/1.01  --prep_sem_filter_out                   false
% 2.53/1.01  --pred_elim                             true
% 2.53/1.01  --res_sim_input                         true
% 2.53/1.01  --eq_ax_congr_red                       true
% 2.53/1.01  --pure_diseq_elim                       true
% 2.53/1.01  --brand_transform                       false
% 2.53/1.01  --non_eq_to_eq                          false
% 2.53/1.01  --prep_def_merge                        true
% 2.53/1.01  --prep_def_merge_prop_impl              false
% 2.53/1.01  --prep_def_merge_mbd                    true
% 2.53/1.01  --prep_def_merge_tr_red                 false
% 2.53/1.01  --prep_def_merge_tr_cl                  false
% 2.53/1.01  --smt_preprocessing                     true
% 2.53/1.01  --smt_ac_axioms                         fast
% 2.53/1.01  --preprocessed_out                      false
% 2.53/1.01  --preprocessed_stats                    false
% 2.53/1.01  
% 2.53/1.01  ------ Abstraction refinement Options
% 2.53/1.01  
% 2.53/1.01  --abstr_ref                             []
% 2.53/1.01  --abstr_ref_prep                        false
% 2.53/1.01  --abstr_ref_until_sat                   false
% 2.53/1.01  --abstr_ref_sig_restrict                funpre
% 2.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.01  --abstr_ref_under                       []
% 2.53/1.01  
% 2.53/1.01  ------ SAT Options
% 2.53/1.01  
% 2.53/1.01  --sat_mode                              false
% 2.53/1.01  --sat_fm_restart_options                ""
% 2.53/1.01  --sat_gr_def                            false
% 2.53/1.01  --sat_epr_types                         true
% 2.53/1.01  --sat_non_cyclic_types                  false
% 2.53/1.01  --sat_finite_models                     false
% 2.53/1.01  --sat_fm_lemmas                         false
% 2.53/1.01  --sat_fm_prep                           false
% 2.53/1.01  --sat_fm_uc_incr                        true
% 2.53/1.01  --sat_out_model                         small
% 2.53/1.01  --sat_out_clauses                       false
% 2.53/1.01  
% 2.53/1.01  ------ QBF Options
% 2.53/1.01  
% 2.53/1.01  --qbf_mode                              false
% 2.53/1.01  --qbf_elim_univ                         false
% 2.53/1.01  --qbf_dom_inst                          none
% 2.53/1.01  --qbf_dom_pre_inst                      false
% 2.53/1.01  --qbf_sk_in                             false
% 2.53/1.01  --qbf_pred_elim                         true
% 2.53/1.01  --qbf_split                             512
% 2.53/1.01  
% 2.53/1.01  ------ BMC1 Options
% 2.53/1.01  
% 2.53/1.01  --bmc1_incremental                      false
% 2.53/1.01  --bmc1_axioms                           reachable_all
% 2.53/1.01  --bmc1_min_bound                        0
% 2.53/1.01  --bmc1_max_bound                        -1
% 2.53/1.01  --bmc1_max_bound_default                -1
% 2.53/1.01  --bmc1_symbol_reachability              true
% 2.53/1.01  --bmc1_property_lemmas                  false
% 2.53/1.01  --bmc1_k_induction                      false
% 2.53/1.01  --bmc1_non_equiv_states                 false
% 2.53/1.01  --bmc1_deadlock                         false
% 2.53/1.01  --bmc1_ucm                              false
% 2.53/1.01  --bmc1_add_unsat_core                   none
% 2.53/1.01  --bmc1_unsat_core_children              false
% 2.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.01  --bmc1_out_stat                         full
% 2.53/1.01  --bmc1_ground_init                      false
% 2.53/1.01  --bmc1_pre_inst_next_state              false
% 2.53/1.01  --bmc1_pre_inst_state                   false
% 2.53/1.01  --bmc1_pre_inst_reach_state             false
% 2.53/1.01  --bmc1_out_unsat_core                   false
% 2.53/1.01  --bmc1_aig_witness_out                  false
% 2.53/1.01  --bmc1_verbose                          false
% 2.53/1.01  --bmc1_dump_clauses_tptp                false
% 2.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.01  --bmc1_dump_file                        -
% 2.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.01  --bmc1_ucm_extend_mode                  1
% 2.53/1.01  --bmc1_ucm_init_mode                    2
% 2.53/1.01  --bmc1_ucm_cone_mode                    none
% 2.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.01  --bmc1_ucm_relax_model                  4
% 2.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.01  --bmc1_ucm_layered_model                none
% 2.53/1.01  --bmc1_ucm_max_lemma_size               10
% 2.53/1.01  
% 2.53/1.01  ------ AIG Options
% 2.53/1.01  
% 2.53/1.01  --aig_mode                              false
% 2.53/1.01  
% 2.53/1.01  ------ Instantiation Options
% 2.53/1.01  
% 2.53/1.01  --instantiation_flag                    true
% 2.53/1.01  --inst_sos_flag                         false
% 2.53/1.01  --inst_sos_phase                        true
% 2.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel_side                     num_symb
% 2.53/1.01  --inst_solver_per_active                1400
% 2.53/1.01  --inst_solver_calls_frac                1.
% 2.53/1.01  --inst_passive_queue_type               priority_queues
% 2.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.01  --inst_passive_queues_freq              [25;2]
% 2.53/1.01  --inst_dismatching                      true
% 2.53/1.01  --inst_eager_unprocessed_to_passive     true
% 2.53/1.01  --inst_prop_sim_given                   true
% 2.53/1.01  --inst_prop_sim_new                     false
% 2.53/1.01  --inst_subs_new                         false
% 2.53/1.01  --inst_eq_res_simp                      false
% 2.53/1.01  --inst_subs_given                       false
% 2.53/1.01  --inst_orphan_elimination               true
% 2.53/1.01  --inst_learning_loop_flag               true
% 2.53/1.01  --inst_learning_start                   3000
% 2.53/1.01  --inst_learning_factor                  2
% 2.53/1.01  --inst_start_prop_sim_after_learn       3
% 2.53/1.01  --inst_sel_renew                        solver
% 2.53/1.01  --inst_lit_activity_flag                true
% 2.53/1.01  --inst_restr_to_given                   false
% 2.53/1.01  --inst_activity_threshold               500
% 2.53/1.01  --inst_out_proof                        true
% 2.53/1.01  
% 2.53/1.01  ------ Resolution Options
% 2.53/1.01  
% 2.53/1.01  --resolution_flag                       true
% 2.53/1.01  --res_lit_sel                           adaptive
% 2.53/1.01  --res_lit_sel_side                      none
% 2.53/1.01  --res_ordering                          kbo
% 2.53/1.01  --res_to_prop_solver                    active
% 2.53/1.01  --res_prop_simpl_new                    false
% 2.53/1.01  --res_prop_simpl_given                  true
% 2.53/1.01  --res_passive_queue_type                priority_queues
% 2.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.01  --res_passive_queues_freq               [15;5]
% 2.53/1.01  --res_forward_subs                      full
% 2.53/1.01  --res_backward_subs                     full
% 2.53/1.01  --res_forward_subs_resolution           true
% 2.53/1.01  --res_backward_subs_resolution          true
% 2.53/1.01  --res_orphan_elimination                true
% 2.53/1.01  --res_time_limit                        2.
% 2.53/1.01  --res_out_proof                         true
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Options
% 2.53/1.01  
% 2.53/1.01  --superposition_flag                    true
% 2.53/1.01  --sup_passive_queue_type                priority_queues
% 2.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.01  --demod_completeness_check              fast
% 2.53/1.01  --demod_use_ground                      true
% 2.53/1.01  --sup_to_prop_solver                    passive
% 2.53/1.01  --sup_prop_simpl_new                    true
% 2.53/1.01  --sup_prop_simpl_given                  true
% 2.53/1.01  --sup_fun_splitting                     false
% 2.53/1.01  --sup_smt_interval                      50000
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Simplification Setup
% 2.53/1.01  
% 2.53/1.01  --sup_indices_passive                   []
% 2.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_full_bw                           [BwDemod]
% 2.53/1.01  --sup_immed_triv                        [TrivRules]
% 2.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_immed_bw_main                     []
% 2.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  
% 2.53/1.01  ------ Combination Options
% 2.53/1.01  
% 2.53/1.01  --comb_res_mult                         3
% 2.53/1.01  --comb_sup_mult                         2
% 2.53/1.01  --comb_inst_mult                        10
% 2.53/1.01  
% 2.53/1.01  ------ Debug Options
% 2.53/1.01  
% 2.53/1.01  --dbg_backtrace                         false
% 2.53/1.01  --dbg_dump_prop_clauses                 false
% 2.53/1.01  --dbg_dump_prop_clauses_file            -
% 2.53/1.01  --dbg_out_stat                          false
% 2.53/1.01  ------ Parsing...
% 2.53/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.01  ------ Proving...
% 2.53/1.01  ------ Problem Properties 
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  clauses                                 20
% 2.53/1.01  conjectures                             2
% 2.53/1.01  EPR                                     5
% 2.53/1.01  Horn                                    17
% 2.53/1.01  unary                                   6
% 2.53/1.01  binary                                  7
% 2.53/1.01  lits                                    42
% 2.53/1.01  lits eq                                 18
% 2.53/1.01  fd_pure                                 0
% 2.53/1.01  fd_pseudo                               0
% 2.53/1.01  fd_cond                                 1
% 2.53/1.01  fd_pseudo_cond                          1
% 2.53/1.01  AC symbols                              0
% 2.53/1.01  
% 2.53/1.01  ------ Schedule dynamic 5 is on 
% 2.53/1.01  
% 2.53/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  ------ 
% 2.53/1.01  Current options:
% 2.53/1.01  ------ 
% 2.53/1.01  
% 2.53/1.01  ------ Input Options
% 2.53/1.01  
% 2.53/1.01  --out_options                           all
% 2.53/1.01  --tptp_safe_out                         true
% 2.53/1.01  --problem_path                          ""
% 2.53/1.01  --include_path                          ""
% 2.53/1.01  --clausifier                            res/vclausify_rel
% 2.53/1.01  --clausifier_options                    --mode clausify
% 2.53/1.01  --stdin                                 false
% 2.53/1.01  --stats_out                             all
% 2.53/1.01  
% 2.53/1.01  ------ General Options
% 2.53/1.01  
% 2.53/1.01  --fof                                   false
% 2.53/1.01  --time_out_real                         305.
% 2.53/1.01  --time_out_virtual                      -1.
% 2.53/1.01  --symbol_type_check                     false
% 2.53/1.01  --clausify_out                          false
% 2.53/1.01  --sig_cnt_out                           false
% 2.53/1.01  --trig_cnt_out                          false
% 2.53/1.01  --trig_cnt_out_tolerance                1.
% 2.53/1.01  --trig_cnt_out_sk_spl                   false
% 2.53/1.01  --abstr_cl_out                          false
% 2.53/1.01  
% 2.53/1.01  ------ Global Options
% 2.53/1.01  
% 2.53/1.01  --schedule                              default
% 2.53/1.01  --add_important_lit                     false
% 2.53/1.01  --prop_solver_per_cl                    1000
% 2.53/1.01  --min_unsat_core                        false
% 2.53/1.01  --soft_assumptions                      false
% 2.53/1.01  --soft_lemma_size                       3
% 2.53/1.01  --prop_impl_unit_size                   0
% 2.53/1.01  --prop_impl_unit                        []
% 2.53/1.01  --share_sel_clauses                     true
% 2.53/1.01  --reset_solvers                         false
% 2.53/1.01  --bc_imp_inh                            [conj_cone]
% 2.53/1.01  --conj_cone_tolerance                   3.
% 2.53/1.01  --extra_neg_conj                        none
% 2.53/1.01  --large_theory_mode                     true
% 2.53/1.01  --prolific_symb_bound                   200
% 2.53/1.01  --lt_threshold                          2000
% 2.53/1.01  --clause_weak_htbl                      true
% 2.53/1.01  --gc_record_bc_elim                     false
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing Options
% 2.53/1.01  
% 2.53/1.01  --preprocessing_flag                    true
% 2.53/1.01  --time_out_prep_mult                    0.1
% 2.53/1.01  --splitting_mode                        input
% 2.53/1.01  --splitting_grd                         true
% 2.53/1.01  --splitting_cvd                         false
% 2.53/1.01  --splitting_cvd_svl                     false
% 2.53/1.01  --splitting_nvd                         32
% 2.53/1.01  --sub_typing                            true
% 2.53/1.01  --prep_gs_sim                           true
% 2.53/1.01  --prep_unflatten                        true
% 2.53/1.01  --prep_res_sim                          true
% 2.53/1.01  --prep_upred                            true
% 2.53/1.01  --prep_sem_filter                       exhaustive
% 2.53/1.01  --prep_sem_filter_out                   false
% 2.53/1.01  --pred_elim                             true
% 2.53/1.01  --res_sim_input                         true
% 2.53/1.01  --eq_ax_congr_red                       true
% 2.53/1.01  --pure_diseq_elim                       true
% 2.53/1.01  --brand_transform                       false
% 2.53/1.01  --non_eq_to_eq                          false
% 2.53/1.01  --prep_def_merge                        true
% 2.53/1.01  --prep_def_merge_prop_impl              false
% 2.53/1.01  --prep_def_merge_mbd                    true
% 2.53/1.01  --prep_def_merge_tr_red                 false
% 2.53/1.01  --prep_def_merge_tr_cl                  false
% 2.53/1.01  --smt_preprocessing                     true
% 2.53/1.01  --smt_ac_axioms                         fast
% 2.53/1.01  --preprocessed_out                      false
% 2.53/1.01  --preprocessed_stats                    false
% 2.53/1.01  
% 2.53/1.01  ------ Abstraction refinement Options
% 2.53/1.01  
% 2.53/1.01  --abstr_ref                             []
% 2.53/1.01  --abstr_ref_prep                        false
% 2.53/1.01  --abstr_ref_until_sat                   false
% 2.53/1.01  --abstr_ref_sig_restrict                funpre
% 2.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.01  --abstr_ref_under                       []
% 2.53/1.01  
% 2.53/1.01  ------ SAT Options
% 2.53/1.01  
% 2.53/1.01  --sat_mode                              false
% 2.53/1.01  --sat_fm_restart_options                ""
% 2.53/1.01  --sat_gr_def                            false
% 2.53/1.01  --sat_epr_types                         true
% 2.53/1.01  --sat_non_cyclic_types                  false
% 2.53/1.01  --sat_finite_models                     false
% 2.53/1.01  --sat_fm_lemmas                         false
% 2.53/1.01  --sat_fm_prep                           false
% 2.53/1.01  --sat_fm_uc_incr                        true
% 2.53/1.01  --sat_out_model                         small
% 2.53/1.01  --sat_out_clauses                       false
% 2.53/1.01  
% 2.53/1.01  ------ QBF Options
% 2.53/1.01  
% 2.53/1.01  --qbf_mode                              false
% 2.53/1.01  --qbf_elim_univ                         false
% 2.53/1.01  --qbf_dom_inst                          none
% 2.53/1.01  --qbf_dom_pre_inst                      false
% 2.53/1.01  --qbf_sk_in                             false
% 2.53/1.01  --qbf_pred_elim                         true
% 2.53/1.01  --qbf_split                             512
% 2.53/1.01  
% 2.53/1.01  ------ BMC1 Options
% 2.53/1.01  
% 2.53/1.01  --bmc1_incremental                      false
% 2.53/1.01  --bmc1_axioms                           reachable_all
% 2.53/1.01  --bmc1_min_bound                        0
% 2.53/1.01  --bmc1_max_bound                        -1
% 2.53/1.01  --bmc1_max_bound_default                -1
% 2.53/1.01  --bmc1_symbol_reachability              true
% 2.53/1.01  --bmc1_property_lemmas                  false
% 2.53/1.01  --bmc1_k_induction                      false
% 2.53/1.01  --bmc1_non_equiv_states                 false
% 2.53/1.01  --bmc1_deadlock                         false
% 2.53/1.01  --bmc1_ucm                              false
% 2.53/1.01  --bmc1_add_unsat_core                   none
% 2.53/1.01  --bmc1_unsat_core_children              false
% 2.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.01  --bmc1_out_stat                         full
% 2.53/1.01  --bmc1_ground_init                      false
% 2.53/1.01  --bmc1_pre_inst_next_state              false
% 2.53/1.01  --bmc1_pre_inst_state                   false
% 2.53/1.01  --bmc1_pre_inst_reach_state             false
% 2.53/1.01  --bmc1_out_unsat_core                   false
% 2.53/1.01  --bmc1_aig_witness_out                  false
% 2.53/1.01  --bmc1_verbose                          false
% 2.53/1.01  --bmc1_dump_clauses_tptp                false
% 2.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.01  --bmc1_dump_file                        -
% 2.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.01  --bmc1_ucm_extend_mode                  1
% 2.53/1.01  --bmc1_ucm_init_mode                    2
% 2.53/1.01  --bmc1_ucm_cone_mode                    none
% 2.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.01  --bmc1_ucm_relax_model                  4
% 2.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.01  --bmc1_ucm_layered_model                none
% 2.53/1.01  --bmc1_ucm_max_lemma_size               10
% 2.53/1.01  
% 2.53/1.01  ------ AIG Options
% 2.53/1.01  
% 2.53/1.01  --aig_mode                              false
% 2.53/1.01  
% 2.53/1.01  ------ Instantiation Options
% 2.53/1.01  
% 2.53/1.01  --instantiation_flag                    true
% 2.53/1.01  --inst_sos_flag                         false
% 2.53/1.01  --inst_sos_phase                        true
% 2.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel_side                     none
% 2.53/1.01  --inst_solver_per_active                1400
% 2.53/1.01  --inst_solver_calls_frac                1.
% 2.53/1.01  --inst_passive_queue_type               priority_queues
% 2.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.01  --inst_passive_queues_freq              [25;2]
% 2.53/1.01  --inst_dismatching                      true
% 2.53/1.01  --inst_eager_unprocessed_to_passive     true
% 2.53/1.01  --inst_prop_sim_given                   true
% 2.53/1.01  --inst_prop_sim_new                     false
% 2.53/1.01  --inst_subs_new                         false
% 2.53/1.01  --inst_eq_res_simp                      false
% 2.53/1.01  --inst_subs_given                       false
% 2.53/1.01  --inst_orphan_elimination               true
% 2.53/1.01  --inst_learning_loop_flag               true
% 2.53/1.01  --inst_learning_start                   3000
% 2.53/1.01  --inst_learning_factor                  2
% 2.53/1.01  --inst_start_prop_sim_after_learn       3
% 2.53/1.01  --inst_sel_renew                        solver
% 2.53/1.01  --inst_lit_activity_flag                true
% 2.53/1.01  --inst_restr_to_given                   false
% 2.53/1.01  --inst_activity_threshold               500
% 2.53/1.01  --inst_out_proof                        true
% 2.53/1.01  
% 2.53/1.01  ------ Resolution Options
% 2.53/1.01  
% 2.53/1.01  --resolution_flag                       false
% 2.53/1.01  --res_lit_sel                           adaptive
% 2.53/1.01  --res_lit_sel_side                      none
% 2.53/1.01  --res_ordering                          kbo
% 2.53/1.01  --res_to_prop_solver                    active
% 2.53/1.01  --res_prop_simpl_new                    false
% 2.53/1.01  --res_prop_simpl_given                  true
% 2.53/1.01  --res_passive_queue_type                priority_queues
% 2.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.01  --res_passive_queues_freq               [15;5]
% 2.53/1.01  --res_forward_subs                      full
% 2.53/1.01  --res_backward_subs                     full
% 2.53/1.01  --res_forward_subs_resolution           true
% 2.53/1.01  --res_backward_subs_resolution          true
% 2.53/1.01  --res_orphan_elimination                true
% 2.53/1.01  --res_time_limit                        2.
% 2.53/1.01  --res_out_proof                         true
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Options
% 2.53/1.01  
% 2.53/1.01  --superposition_flag                    true
% 2.53/1.01  --sup_passive_queue_type                priority_queues
% 2.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.01  --demod_completeness_check              fast
% 2.53/1.01  --demod_use_ground                      true
% 2.53/1.01  --sup_to_prop_solver                    passive
% 2.53/1.01  --sup_prop_simpl_new                    true
% 2.53/1.01  --sup_prop_simpl_given                  true
% 2.53/1.01  --sup_fun_splitting                     false
% 2.53/1.01  --sup_smt_interval                      50000
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Simplification Setup
% 2.53/1.01  
% 2.53/1.01  --sup_indices_passive                   []
% 2.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_full_bw                           [BwDemod]
% 2.53/1.01  --sup_immed_triv                        [TrivRules]
% 2.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_immed_bw_main                     []
% 2.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  
% 2.53/1.01  ------ Combination Options
% 2.53/1.01  
% 2.53/1.01  --comb_res_mult                         3
% 2.53/1.01  --comb_sup_mult                         2
% 2.53/1.01  --comb_inst_mult                        10
% 2.53/1.01  
% 2.53/1.01  ------ Debug Options
% 2.53/1.01  
% 2.53/1.01  --dbg_backtrace                         false
% 2.53/1.01  --dbg_dump_prop_clauses                 false
% 2.53/1.01  --dbg_dump_prop_clauses_file            -
% 2.53/1.01  --dbg_out_stat                          false
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  ------ Proving...
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  % SZS status Theorem for theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  fof(f8,axiom,(
% 2.53/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f22,plain,(
% 2.53/1.01    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.53/1.01    inference(ennf_transformation,[],[f8])).
% 2.53/1.01  
% 2.53/1.01  fof(f57,plain,(
% 2.53/1.01    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f22])).
% 2.53/1.01  
% 2.53/1.01  fof(f3,axiom,(
% 2.53/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f48,plain,(
% 2.53/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f3])).
% 2.53/1.01  
% 2.53/1.01  fof(f1,axiom,(
% 2.53/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f33,plain,(
% 2.53/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.53/1.01    inference(nnf_transformation,[],[f1])).
% 2.53/1.01  
% 2.53/1.01  fof(f34,plain,(
% 2.53/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.53/1.01    inference(flattening,[],[f33])).
% 2.53/1.01  
% 2.53/1.01  fof(f46,plain,(
% 2.53/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f34])).
% 2.53/1.01  
% 2.53/1.01  fof(f9,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f23,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(ennf_transformation,[],[f9])).
% 2.53/1.01  
% 2.53/1.01  fof(f58,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f23])).
% 2.53/1.01  
% 2.53/1.01  fof(f5,axiom,(
% 2.53/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f37,plain,(
% 2.53/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.53/1.01    inference(nnf_transformation,[],[f5])).
% 2.53/1.01  
% 2.53/1.01  fof(f53,plain,(
% 2.53/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f37])).
% 2.53/1.01  
% 2.53/1.01  fof(f14,conjecture,(
% 2.53/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f15,negated_conjecture,(
% 2.53/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 2.53/1.01    inference(negated_conjecture,[],[f14])).
% 2.53/1.01  
% 2.53/1.01  fof(f31,plain,(
% 2.53/1.01    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.53/1.01    inference(ennf_transformation,[],[f15])).
% 2.53/1.01  
% 2.53/1.01  fof(f32,plain,(
% 2.53/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.53/1.01    inference(flattening,[],[f31])).
% 2.53/1.01  
% 2.53/1.01  fof(f42,plain,(
% 2.53/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 2.53/1.01    introduced(choice_axiom,[])).
% 2.53/1.01  
% 2.53/1.01  fof(f43,plain,(
% 2.53/1.01    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 2.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f42])).
% 2.53/1.01  
% 2.53/1.01  fof(f71,plain,(
% 2.53/1.01    r1_tarski(sK1,sK3)),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  fof(f11,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f25,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(ennf_transformation,[],[f11])).
% 2.53/1.01  
% 2.53/1.01  fof(f26,plain,(
% 2.53/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(flattening,[],[f25])).
% 2.53/1.01  
% 2.53/1.01  fof(f39,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(nnf_transformation,[],[f26])).
% 2.53/1.01  
% 2.53/1.01  fof(f60,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f39])).
% 2.53/1.01  
% 2.53/1.01  fof(f69,plain,(
% 2.53/1.01    v1_funct_2(sK4,sK1,sK2)),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  fof(f70,plain,(
% 2.53/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  fof(f10,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f24,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(ennf_transformation,[],[f10])).
% 2.53/1.01  
% 2.53/1.01  fof(f59,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f24])).
% 2.53/1.01  
% 2.53/1.01  fof(f6,axiom,(
% 2.53/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f19,plain,(
% 2.53/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.53/1.01    inference(ennf_transformation,[],[f6])).
% 2.53/1.01  
% 2.53/1.01  fof(f38,plain,(
% 2.53/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.53/1.01    inference(nnf_transformation,[],[f19])).
% 2.53/1.01  
% 2.53/1.01  fof(f55,plain,(
% 2.53/1.01    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f38])).
% 2.53/1.01  
% 2.53/1.01  fof(f7,axiom,(
% 2.53/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f20,plain,(
% 2.53/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.53/1.01    inference(ennf_transformation,[],[f7])).
% 2.53/1.01  
% 2.53/1.01  fof(f21,plain,(
% 2.53/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.53/1.01    inference(flattening,[],[f20])).
% 2.53/1.01  
% 2.53/1.01  fof(f56,plain,(
% 2.53/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f21])).
% 2.53/1.01  
% 2.53/1.01  fof(f65,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f39])).
% 2.53/1.01  
% 2.53/1.01  fof(f77,plain,(
% 2.53/1.01    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(equality_resolution,[],[f65])).
% 2.53/1.01  
% 2.53/1.01  fof(f78,plain,(
% 2.53/1.01    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.53/1.01    inference(equality_resolution,[],[f77])).
% 2.53/1.01  
% 2.53/1.01  fof(f68,plain,(
% 2.53/1.01    v1_funct_1(sK4)),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  fof(f13,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f16,plain,(
% 2.53/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : k1_funct_1(X2,X4) = k1_funct_1(X3,X4) => r2_relset_1(X0,X1,X2,X3))))),
% 2.53/1.01    inference(pure_predicate_removal,[],[f13])).
% 2.53/1.01  
% 2.53/1.01  fof(f29,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.53/1.01    inference(ennf_transformation,[],[f16])).
% 2.53/1.01  
% 2.53/1.01  fof(f30,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.53/1.01    inference(flattening,[],[f29])).
% 2.53/1.01  
% 2.53/1.01  fof(f40,plain,(
% 2.53/1.01    ! [X3,X2] : (? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) => k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)))),
% 2.53/1.01    introduced(choice_axiom,[])).
% 2.53/1.01  
% 2.53/1.01  fof(f41,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f40])).
% 2.53/1.01  
% 2.53/1.01  fof(f67,plain,(
% 2.53/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f41])).
% 2.53/1.01  
% 2.53/1.01  fof(f72,plain,(
% 2.53/1.01    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  fof(f12,axiom,(
% 2.53/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f27,plain,(
% 2.53/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.53/1.01    inference(ennf_transformation,[],[f12])).
% 2.53/1.01  
% 2.53/1.01  fof(f28,plain,(
% 2.53/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.53/1.01    inference(flattening,[],[f27])).
% 2.53/1.01  
% 2.53/1.01  fof(f66,plain,(
% 2.53/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f28])).
% 2.53/1.01  
% 2.53/1.01  fof(f64,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f39])).
% 2.53/1.01  
% 2.53/1.01  fof(f79,plain,(
% 2.53/1.01    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.53/1.01    inference(equality_resolution,[],[f64])).
% 2.53/1.01  
% 2.53/1.01  fof(f4,axiom,(
% 2.53/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.53/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f35,plain,(
% 2.53/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.53/1.01    inference(nnf_transformation,[],[f4])).
% 2.53/1.01  
% 2.53/1.01  fof(f36,plain,(
% 2.53/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.53/1.01    inference(flattening,[],[f35])).
% 2.53/1.01  
% 2.53/1.01  fof(f51,plain,(
% 2.53/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.53/1.01    inference(cnf_transformation,[],[f36])).
% 2.53/1.01  
% 2.53/1.01  fof(f75,plain,(
% 2.53/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.53/1.01    inference(equality_resolution,[],[f51])).
% 2.53/1.01  
% 2.53/1.01  fof(f52,plain,(
% 2.53/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f37])).
% 2.53/1.01  
% 2.53/1.01  cnf(c_13,plain,
% 2.53/1.01      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2268,plain,
% 2.53/1.01      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 2.53/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2271,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_0,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.53/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2274,plain,
% 2.53/1.01      ( X0 = X1
% 2.53/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.53/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_5072,plain,
% 2.53/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_2271,c_2274]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_6371,plain,
% 2.53/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 2.53/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_2268,c_5072]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_14,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | v1_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_61,plain,
% 2.53/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.53/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_63,plain,
% 2.53/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 2.53/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_61]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_8,plain,
% 2.53/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.53/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2409,plain,
% 2.53/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2410,plain,
% 2.53/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.53/1.01      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2412,plain,
% 2.53/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 2.53/1.01      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_2410]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2662,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2665,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_2662]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2667,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_2665]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_6978,plain,
% 2.53/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_6371,c_63,c_2412,c_2667]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_25,negated_conjecture,
% 2.53/1.01      ( r1_tarski(sK1,sK3) ),
% 2.53/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2265,plain,
% 2.53/1.01      ( r1_tarski(sK1,sK3) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_21,plain,
% 2.53/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.53/1.01      | k1_xboole_0 = X2 ),
% 2.53/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_27,negated_conjecture,
% 2.53/1.01      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.53/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_946,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.53/1.01      | sK4 != X0
% 2.53/1.01      | sK2 != X2
% 2.53/1.01      | sK1 != X1
% 2.53/1.01      | k1_xboole_0 = X2 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_947,plain,
% 2.53/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k1_relset_1(sK1,sK2,sK4) = sK1
% 2.53/1.01      | k1_xboole_0 = sK2 ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_946]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_26,negated_conjecture,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.53/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_949,plain,
% 2.53/1.01      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_947,c_26]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2264,plain,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_15,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2266,plain,
% 2.53/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.53/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3389,plain,
% 2.53/1.01      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_2264,c_2266]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3821,plain,
% 2.53/1.01      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_949,c_3389]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_10,plain,
% 2.53/1.01      ( v4_relat_1(X0,X1)
% 2.53/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.53/1.01      | ~ v1_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_12,plain,
% 2.53/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.53/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_409,plain,
% 2.53/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.53/1.01      | ~ v1_relat_1(X0)
% 2.53/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.53/1.01      inference(resolution,[status(thm)],[c_10,c_12]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2262,plain,
% 2.53/1.01      ( k7_relat_1(X0,X1) = X0
% 2.53/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.53/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3825,plain,
% 2.53/1.01      ( k7_relat_1(sK4,X0) = sK4
% 2.53/1.01      | sK2 = k1_xboole_0
% 2.53/1.01      | r1_tarski(sK1,X0) != iProver_top
% 2.53/1.01      | v1_relat_1(sK4) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_3821,c_2262]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_31,plain,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2414,plain,
% 2.53/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | v1_relat_1(sK4) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2415,plain,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.53/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3929,plain,
% 2.53/1.01      ( r1_tarski(sK1,X0) != iProver_top
% 2.53/1.01      | sK2 = k1_xboole_0
% 2.53/1.01      | k7_relat_1(sK4,X0) = sK4 ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_3825,c_31,c_2415]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3930,plain,
% 2.53/1.01      ( k7_relat_1(sK4,X0) = sK4
% 2.53/1.01      | sK2 = k1_xboole_0
% 2.53/1.01      | r1_tarski(sK1,X0) != iProver_top ),
% 2.53/1.01      inference(renaming,[status(thm)],[c_3929]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3939,plain,
% 2.53/1.01      ( k7_relat_1(sK4,sK3) = sK4 | sK2 = k1_xboole_0 ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_2265,c_3930]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_16,plain,
% 2.53/1.01      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.53/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.53/1.01      | k1_xboole_0 = X0 ),
% 2.53/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_28,negated_conjecture,
% 2.53/1.01      ( v1_funct_1(sK4) ),
% 2.53/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_23,plain,
% 2.53/1.01      ( r2_relset_1(X0,X1,X2,X3)
% 2.53/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.53/1.01      | ~ v1_funct_2(X3,X0,X1)
% 2.53/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.01      | ~ v1_funct_1(X2)
% 2.53/1.01      | ~ v1_funct_1(X3)
% 2.53/1.01      | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
% 2.53/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_24,negated_conjecture,
% 2.53/1.01      ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
% 2.53/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_349,plain,
% 2.53/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.53/1.01      | ~ v1_funct_2(X3,X1,X2)
% 2.53/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | ~ v1_funct_1(X0)
% 2.53/1.01      | ~ v1_funct_1(X3)
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 2.53/1.01      | k1_funct_1(X3,sK0(X0,X3)) != k1_funct_1(X0,sK0(X0,X3))
% 2.53/1.01      | sK4 != X3
% 2.53/1.01      | sK2 != X2
% 2.53/1.01      | sK1 != X1 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_24]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_350,plain,
% 2.53/1.01      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 2.53/1.01      | ~ v1_funct_2(sK4,sK1,sK2)
% 2.53/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 2.53/1.01      | ~ v1_funct_1(sK4)
% 2.53/1.01      | k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_349]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_352,plain,
% 2.53/1.01      ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 2.53/1.01      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 2.53/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_350,c_28,c_27,c_26]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_353,plain,
% 2.53/1.01      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 2.53/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 2.53/1.01      | k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 2.53/1.01      inference(renaming,[status(thm)],[c_352]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_386,plain,
% 2.53/1.01      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 2.53/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_353]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_862,plain,
% 2.53/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != k1_xboole_0
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 2.53/1.01      | sK2 != k1_xboole_0
% 2.53/1.01      | sK1 != X0
% 2.53/1.01      | k1_xboole_0 = X0 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_386]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_863,plain,
% 2.53/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != k1_xboole_0
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 2.53/1.01      | sK2 != k1_xboole_0
% 2.53/1.01      | k1_xboole_0 = sK1 ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_862]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_976,plain,
% 2.53/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 2.53/1.01      | sK2 != sK2
% 2.53/1.01      | sK1 != sK1 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_386]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1051,plain,
% 2.53/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 2.53/1.01      inference(equality_resolution_simp,[status(thm)],[c_976]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1066,plain,
% 2.53/1.01      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_863,c_1051]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1067,plain,
% 2.53/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 2.53/1.01      inference(renaming,[status(thm)],[c_1066]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2259,plain,
% 2.53/1.01      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.53/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 2.53/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_22,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | ~ v1_funct_1(X0)
% 2.53/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.53/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_374,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.53/1.01      | sK4 != X0 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_375,plain,
% 2.53/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.53/1.01      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_374]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2263,plain,
% 2.53/1.01      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 2.53/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2431,plain,
% 2.53/1.01      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_2264,c_2263]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2512,plain,
% 2.53/1.01      ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
% 2.53/1.01      | k7_relat_1(sK4,sK3) != sK4
% 2.53/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_2259,c_2431]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3951,plain,
% 2.53/1.01      ( k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
% 2.53/1.01      | k7_relat_1(sK4,sK3) != sK4
% 2.53/1.01      | sK2 = k1_xboole_0
% 2.53/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_3939,c_2512]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3957,plain,
% 2.53/1.01      ( k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
% 2.53/1.01      | sK2 = k1_xboole_0
% 2.53/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.53/1.01      inference(forward_subsumption_resolution,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_3951,c_3939]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4032,plain,
% 2.53/1.01      ( sK2 = k1_xboole_0
% 2.53/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_3939,c_3957]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4038,plain,
% 2.53/1.01      ( sK2 = k1_xboole_0
% 2.53/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_3939,c_4032]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4130,plain,
% 2.53/1.01      ( sK2 = k1_xboole_0 ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_4038,c_31]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_17,plain,
% 2.53/1.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.53/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.53/1.01      | k1_xboole_0 = X1
% 2.53/1.01      | k1_xboole_0 = X0 ),
% 2.53/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_891,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.53/1.01      | sK4 != X0
% 2.53/1.01      | sK2 != k1_xboole_0
% 2.53/1.01      | sK1 != X1
% 2.53/1.01      | k1_xboole_0 = X1
% 2.53/1.01      | k1_xboole_0 = X0 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_892,plain,
% 2.53/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.53/1.01      | sK2 != k1_xboole_0
% 2.53/1.01      | k1_xboole_0 = sK4
% 2.53/1.01      | k1_xboole_0 = sK1 ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_891]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2261,plain,
% 2.53/1.01      ( sK2 != k1_xboole_0
% 2.53/1.01      | k1_xboole_0 = sK4
% 2.53/1.01      | k1_xboole_0 = sK1
% 2.53/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_892]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_5,plain,
% 2.53/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.53/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2346,plain,
% 2.53/1.01      ( sK4 = k1_xboole_0
% 2.53/1.01      | sK2 != k1_xboole_0
% 2.53/1.01      | sK1 = k1_xboole_0
% 2.53/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_2261,c_5]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4137,plain,
% 2.53/1.01      ( sK4 = k1_xboole_0
% 2.53/1.01      | sK1 = k1_xboole_0
% 2.53/1.01      | k1_xboole_0 != k1_xboole_0
% 2.53/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_4130,c_2346]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4161,plain,
% 2.53/1.01      ( sK4 = k1_xboole_0
% 2.53/1.01      | sK1 = k1_xboole_0
% 2.53/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(equality_resolution_simp,[status(thm)],[c_4137]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4142,plain,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_4130,c_2264]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4144,plain,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_4142,c_5]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4165,plain,
% 2.53/1.01      ( sK4 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.53/1.01      inference(forward_subsumption_resolution,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_4161,c_4144]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2590,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2591,plain,
% 2.53/1.01      ( sK4 = X0
% 2.53/1.01      | r1_tarski(X0,sK4) != iProver_top
% 2.53/1.01      | r1_tarski(sK4,X0) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_2590]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2593,plain,
% 2.53/1.01      ( sK4 = k1_xboole_0
% 2.53/1.01      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.53/1.01      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_2591]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_9,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.53/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2741,plain,
% 2.53/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2742,plain,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.53/1.01      | r1_tarski(sK4,X0) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_2741]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2744,plain,
% 2.53/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.53/1.01      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_2742]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2776,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,sK4) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2779,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_2776]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_5148,plain,
% 2.53/1.01      ( sK4 = k1_xboole_0 ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_4165,c_2593,c_2744,c_2779,c_4144]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4138,plain,
% 2.53/1.01      ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
% 2.53/1.01      | k7_relat_1(sK4,sK3) != sK4
% 2.53/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_4130,c_2512]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4157,plain,
% 2.53/1.01      ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
% 2.53/1.01      | k7_relat_1(sK4,sK3) != sK4
% 2.53/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_4138,c_5]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_5151,plain,
% 2.53/1.01      ( k1_funct_1(k7_relat_1(k1_xboole_0,sK3),sK0(k7_relat_1(k1_xboole_0,sK3),k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK0(k7_relat_1(k1_xboole_0,sK3),k1_xboole_0))
% 2.53/1.01      | k7_relat_1(k1_xboole_0,sK3) != k1_xboole_0
% 2.53/1.01      | m1_subset_1(k7_relat_1(k1_xboole_0,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_5148,c_4157]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_6982,plain,
% 2.53/1.01      ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,k1_xboole_0))
% 2.53/1.01      | k1_xboole_0 != k1_xboole_0
% 2.53/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_6978,c_5151]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_6987,plain,
% 2.53/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.53/1.01      inference(equality_resolution_simp,[status(thm)],[c_6982]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_84,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_86,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_84]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_79,plain,
% 2.53/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.53/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_81,plain,
% 2.53/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.53/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_79]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(contradiction,plain,
% 2.53/1.01      ( $false ),
% 2.53/1.01      inference(minisat,[status(thm)],[c_6987,c_86,c_81]) ).
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  ------                               Statistics
% 2.53/1.01  
% 2.53/1.01  ------ General
% 2.53/1.01  
% 2.53/1.01  abstr_ref_over_cycles:                  0
% 2.53/1.01  abstr_ref_under_cycles:                 0
% 2.53/1.01  gc_basic_clause_elim:                   0
% 2.53/1.01  forced_gc_time:                         0
% 2.53/1.01  parsing_time:                           0.014
% 2.53/1.01  unif_index_cands_time:                  0.
% 2.53/1.01  unif_index_add_time:                    0.
% 2.53/1.01  orderings_time:                         0.
% 2.53/1.01  out_proof_time:                         0.01
% 2.53/1.01  total_time:                             0.227
% 2.53/1.01  num_of_symbols:                         51
% 2.53/1.01  num_of_terms:                           3733
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing
% 2.53/1.01  
% 2.53/1.01  num_of_splits:                          0
% 2.53/1.01  num_of_split_atoms:                     0
% 2.53/1.01  num_of_reused_defs:                     0
% 2.53/1.01  num_eq_ax_congr_red:                    20
% 2.53/1.01  num_of_sem_filtered_clauses:            1
% 2.53/1.01  num_of_subtypes:                        0
% 2.53/1.01  monotx_restored_types:                  0
% 2.53/1.01  sat_num_of_epr_types:                   0
% 2.53/1.01  sat_num_of_non_cyclic_types:            0
% 2.53/1.01  sat_guarded_non_collapsed_types:        0
% 2.53/1.01  num_pure_diseq_elim:                    0
% 2.53/1.01  simp_replaced_by:                       0
% 2.53/1.01  res_preprocessed:                       131
% 2.53/1.01  prep_upred:                             0
% 2.53/1.01  prep_unflattend:                        74
% 2.53/1.01  smt_new_axioms:                         0
% 2.53/1.01  pred_elim_cands:                        3
% 2.53/1.01  pred_elim:                              4
% 2.53/1.01  pred_elim_cl:                           5
% 2.53/1.01  pred_elim_cycles:                       11
% 2.53/1.01  merged_defs:                            10
% 2.53/1.01  merged_defs_ncl:                        0
% 2.53/1.01  bin_hyper_res:                          10
% 2.53/1.01  prep_cycles:                            5
% 2.53/1.01  pred_elim_time:                         0.032
% 2.53/1.01  splitting_time:                         0.
% 2.53/1.01  sem_filter_time:                        0.
% 2.53/1.01  monotx_time:                            0.
% 2.53/1.01  subtype_inf_time:                       0.
% 2.53/1.01  
% 2.53/1.01  ------ Problem properties
% 2.53/1.01  
% 2.53/1.01  clauses:                                20
% 2.53/1.01  conjectures:                            2
% 2.53/1.01  epr:                                    5
% 2.53/1.01  horn:                                   17
% 2.53/1.01  ground:                                 6
% 2.53/1.01  unary:                                  6
% 2.53/1.01  binary:                                 7
% 2.53/1.01  lits:                                   42
% 2.53/1.01  lits_eq:                                18
% 2.53/1.01  fd_pure:                                0
% 2.53/1.01  fd_pseudo:                              0
% 2.53/1.01  fd_cond:                                1
% 2.53/1.01  fd_pseudo_cond:                         1
% 2.53/1.01  ac_symbols:                             0
% 2.53/1.01  
% 2.53/1.01  ------ Propositional Solver
% 2.53/1.01  
% 2.53/1.01  prop_solver_calls:                      32
% 2.53/1.01  prop_fast_solver_calls:                 1007
% 2.53/1.01  smt_solver_calls:                       0
% 2.53/1.01  smt_fast_solver_calls:                  0
% 2.53/1.01  prop_num_of_clauses:                    2153
% 2.53/1.01  prop_preprocess_simplified:             7178
% 2.53/1.01  prop_fo_subsumed:                       20
% 2.53/1.01  prop_solver_time:                       0.
% 2.53/1.01  smt_solver_time:                        0.
% 2.53/1.01  smt_fast_solver_time:                   0.
% 2.53/1.01  prop_fast_solver_time:                  0.
% 2.53/1.01  prop_unsat_core_time:                   0.
% 2.53/1.01  
% 2.53/1.01  ------ QBF
% 2.53/1.01  
% 2.53/1.01  qbf_q_res:                              0
% 2.53/1.01  qbf_num_tautologies:                    0
% 2.53/1.01  qbf_prep_cycles:                        0
% 2.53/1.01  
% 2.53/1.01  ------ BMC1
% 2.53/1.01  
% 2.53/1.01  bmc1_current_bound:                     -1
% 2.53/1.01  bmc1_last_solved_bound:                 -1
% 2.53/1.01  bmc1_unsat_core_size:                   -1
% 2.53/1.01  bmc1_unsat_core_parents_size:           -1
% 2.53/1.01  bmc1_merge_next_fun:                    0
% 2.53/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.01  
% 2.53/1.01  ------ Instantiation
% 2.53/1.01  
% 2.53/1.01  inst_num_of_clauses:                    656
% 2.53/1.01  inst_num_in_passive:                    281
% 2.53/1.01  inst_num_in_active:                     270
% 2.53/1.01  inst_num_in_unprocessed:                106
% 2.53/1.01  inst_num_of_loops:                      320
% 2.53/1.01  inst_num_of_learning_restarts:          0
% 2.53/1.01  inst_num_moves_active_passive:          48
% 2.53/1.01  inst_lit_activity:                      0
% 2.53/1.01  inst_lit_activity_moves:                0
% 2.53/1.01  inst_num_tautologies:                   0
% 2.53/1.01  inst_num_prop_implied:                  0
% 2.53/1.01  inst_num_existing_simplified:           0
% 2.53/1.01  inst_num_eq_res_simplified:             0
% 2.53/1.01  inst_num_child_elim:                    0
% 2.53/1.01  inst_num_of_dismatching_blockings:      96
% 2.53/1.01  inst_num_of_non_proper_insts:           662
% 2.53/1.01  inst_num_of_duplicates:                 0
% 2.53/1.01  inst_inst_num_from_inst_to_res:         0
% 2.53/1.01  inst_dismatching_checking_time:         0.
% 2.53/1.01  
% 2.53/1.01  ------ Resolution
% 2.53/1.01  
% 2.53/1.01  res_num_of_clauses:                     0
% 2.53/1.01  res_num_in_passive:                     0
% 2.53/1.01  res_num_in_active:                      0
% 2.53/1.01  res_num_of_loops:                       136
% 2.53/1.01  res_forward_subset_subsumed:            49
% 2.53/1.01  res_backward_subset_subsumed:           2
% 2.53/1.01  res_forward_subsumed:                   1
% 2.53/1.01  res_backward_subsumed:                  0
% 2.53/1.01  res_forward_subsumption_resolution:     1
% 2.53/1.01  res_backward_subsumption_resolution:    0
% 2.53/1.01  res_clause_to_clause_subsumption:       241
% 2.53/1.01  res_orphan_elimination:                 0
% 2.53/1.01  res_tautology_del:                      130
% 2.53/1.01  res_num_eq_res_simplified:              1
% 2.53/1.01  res_num_sel_changes:                    0
% 2.53/1.01  res_moves_from_active_to_pass:          0
% 2.53/1.01  
% 2.53/1.01  ------ Superposition
% 2.53/1.01  
% 2.53/1.01  sup_time_total:                         0.
% 2.53/1.01  sup_time_generating:                    0.
% 2.53/1.01  sup_time_sim_full:                      0.
% 2.53/1.01  sup_time_sim_immed:                     0.
% 2.53/1.01  
% 2.53/1.01  sup_num_of_clauses:                     43
% 2.53/1.01  sup_num_in_active:                      31
% 2.53/1.01  sup_num_in_passive:                     12
% 2.53/1.01  sup_num_of_loops:                       62
% 2.53/1.01  sup_fw_superposition:                   54
% 2.53/1.01  sup_bw_superposition:                   20
% 2.53/1.01  sup_immediate_simplified:               15
% 2.53/1.01  sup_given_eliminated:                   0
% 2.53/1.01  comparisons_done:                       0
% 2.53/1.01  comparisons_avoided:                    9
% 2.53/1.01  
% 2.53/1.01  ------ Simplifications
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  sim_fw_subset_subsumed:                 3
% 2.53/1.01  sim_bw_subset_subsumed:                 9
% 2.53/1.01  sim_fw_subsumed:                        5
% 2.53/1.01  sim_bw_subsumed:                        2
% 2.53/1.01  sim_fw_subsumption_res:                 3
% 2.53/1.01  sim_bw_subsumption_res:                 1
% 2.53/1.01  sim_tautology_del:                      2
% 2.53/1.01  sim_eq_tautology_del:                   6
% 2.53/1.01  sim_eq_res_simp:                        2
% 2.53/1.01  sim_fw_demodulated:                     7
% 2.53/1.01  sim_bw_demodulated:                     27
% 2.53/1.01  sim_light_normalised:                   2
% 2.53/1.01  sim_joinable_taut:                      0
% 2.53/1.01  sim_joinable_simp:                      0
% 2.53/1.01  sim_ac_normalised:                      0
% 2.53/1.01  sim_smt_subsumption:                    0
% 2.53/1.01  
%------------------------------------------------------------------------------
