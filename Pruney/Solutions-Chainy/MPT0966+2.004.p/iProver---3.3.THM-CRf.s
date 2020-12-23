%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:31 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  203 (4819 expanded)
%              Number of clauses        :  138 (1777 expanded)
%              Number of leaves         :   18 ( 912 expanded)
%              Depth                    :   32
%              Number of atoms          :  637 (23746 expanded)
%              Number of equality atoms :  329 (6529 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f39])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f38,plain,(
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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1659,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1663,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2591,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1659,c_1663])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_988,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_989,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_988])).

cnf(c_991,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_989,c_25])).

cnf(c_2889,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2591,c_991])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_329,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_10])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_1658,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_2537,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_1658])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1662,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2587,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1659,c_1662])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1660,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2744,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2587,c_1660])).

cnf(c_3075,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1663])).

cnf(c_3551,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2744,c_3075])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1845,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1846,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1845])).

cnf(c_3879,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3551,c_30,c_1846])).

cnf(c_3880,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3879])).

cnf(c_3888,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2537,c_3880])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_148,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_27])).

cnf(c_149,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_149])).

cnf(c_976,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_1653,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_3928,plain,
    ( k1_relat_1(sK4) != sK1
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3888,c_1653])).

cnf(c_3935,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_3928])).

cnf(c_3994,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_3935])).

cnf(c_1852,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK4),sK1) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_1853,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1852])).

cnf(c_6885,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3994,c_30,c_1846,c_1853,c_2744])).

cnf(c_6886,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6885])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6895,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6886,c_23])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1670,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1669,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2672,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1670,c_1669])).

cnf(c_3200,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2672,c_1669])).

cnf(c_4947,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_3200])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1666,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_298,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_299,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),k2_relset_1(X0,X1,sK4))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_1033,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),k2_relset_1(X0,X1,sK4))
    | sK2 != X1
    | sK1 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_299])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1033])).

cnf(c_1038,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1034,c_25])).

cnf(c_1651,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1038])).

cnf(c_2743,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2587,c_1651])).

cnf(c_3296,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_1669])).

cnf(c_3321,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3296,c_1669])).

cnf(c_3458,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2744,c_3321])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1665,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3522,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r1_tarski(X1,k1_funct_1(sK4,X0)) != iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3458,c_1665])).

cnf(c_4452,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1666,c_3522])).

cnf(c_5318,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4947,c_4452])).

cnf(c_79,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_78,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_80,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_84,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1269,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1926,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_1927,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_1929,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_1268,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1861,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1934,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1861])).

cnf(c_1267,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1935,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_2939,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_2940,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2939])).

cnf(c_5137,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1670,c_4452])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1671,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5315,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4947,c_1671])).

cnf(c_3201,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X1,sK0(X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2672,c_1665])).

cnf(c_3674,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1666,c_3201])).

cnf(c_5732,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5315,c_3674])).

cnf(c_6588,plain,
    ( r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5318,c_23,c_79,c_80,c_84,c_1929,c_1934,c_1935,c_2940,c_5137,c_5315,c_5732])).

cnf(c_6589,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6588])).

cnf(c_6601,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6589,c_3880])).

cnf(c_7021,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | sK1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6895,c_6601])).

cnf(c_1928,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_3881,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0)
    | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3880])).

cnf(c_5816,plain,
    ( r1_tarski(k1_relat_1(sK4),X0)
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5732])).

cnf(c_7097,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7021])).

cnf(c_7523,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7021,c_79,c_84,c_1928,c_3881,c_5816,c_7097])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_925,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_149])).

cnf(c_926,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_1655,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_7527,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7523,c_1655])).

cnf(c_927,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_7025,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6895,c_5137])).

cnf(c_7714,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7025,c_23,c_79,c_80,c_84,c_1934,c_1935,c_2940])).

cnf(c_7715,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7714])).

cnf(c_1668,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2656,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1666,c_1668])).

cnf(c_7730,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7715,c_2656])).

cnf(c_7856,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_7730,c_3888])).

cnf(c_7867,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_7730,c_2591])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_941,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_1654,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_7873,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7730,c_1654])).

cnf(c_7883,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7873])).

cnf(c_7875,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7730,c_1659])).

cnf(c_7886,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7883,c_7875])).

cnf(c_7896,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7867,c_7886])).

cnf(c_7956,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7856,c_7896])).

cnf(c_8316,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7527,c_927,c_7730,c_7956])).

cnf(c_8320,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8316,c_7730])).

cnf(c_8323,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_8320])).

cnf(c_5357,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5315])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8323,c_7730,c_5357,c_2744,c_1929,c_1846,c_84,c_80,c_79,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:42:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.27/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/0.99  
% 3.27/0.99  ------  iProver source info
% 3.27/0.99  
% 3.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/0.99  git: non_committed_changes: false
% 3.27/0.99  git: last_make_outside_of_git: false
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     num_symb
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       true
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  ------ Parsing...
% 3.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/0.99  ------ Proving...
% 3.27/0.99  ------ Problem Properties 
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  clauses                                 24
% 3.27/0.99  conjectures                             3
% 3.27/0.99  EPR                                     6
% 3.27/0.99  Horn                                    19
% 3.27/0.99  unary                                   4
% 3.27/0.99  binary                                  10
% 3.27/0.99  lits                                    61
% 3.27/0.99  lits eq                                 23
% 3.27/0.99  fd_pure                                 0
% 3.27/0.99  fd_pseudo                               0
% 3.27/0.99  fd_cond                                 1
% 3.27/0.99  fd_pseudo_cond                          1
% 3.27/0.99  AC symbols                              0
% 3.27/0.99  
% 3.27/0.99  ------ Schedule dynamic 5 is on 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  Current options:
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     none
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       false
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ Proving...
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS status Theorem for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  fof(f10,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f23,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.27/0.99    inference(ennf_transformation,[],[f10])).
% 3.27/0.99  
% 3.27/0.99  fof(f24,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.27/0.99    inference(flattening,[],[f23])).
% 3.27/0.99  
% 3.27/0.99  fof(f55,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f24])).
% 3.27/0.99  
% 3.27/0.99  fof(f13,conjecture,(
% 3.27/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f14,negated_conjecture,(
% 3.27/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.27/0.99    inference(negated_conjecture,[],[f13])).
% 3.27/0.99  
% 3.27/0.99  fof(f29,plain,(
% 3.27/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.27/0.99    inference(ennf_transformation,[],[f14])).
% 3.27/0.99  
% 3.27/0.99  fof(f30,plain,(
% 3.27/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.27/0.99    inference(flattening,[],[f29])).
% 3.27/0.99  
% 3.27/0.99  fof(f39,plain,(
% 3.27/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f40,plain,(
% 3.27/0.99    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f39])).
% 3.27/0.99  
% 3.27/0.99  fof(f65,plain,(
% 3.27/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f8,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f21,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f8])).
% 3.27/0.99  
% 3.27/0.99  fof(f53,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f21])).
% 3.27/0.99  
% 3.27/0.99  fof(f11,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f25,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f11])).
% 3.27/0.99  
% 3.27/0.99  fof(f26,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(flattening,[],[f25])).
% 3.27/0.99  
% 3.27/0.99  fof(f38,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(nnf_transformation,[],[f26])).
% 3.27/0.99  
% 3.27/0.99  fof(f56,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f38])).
% 3.27/0.99  
% 3.27/0.99  fof(f64,plain,(
% 3.27/0.99    v1_funct_2(sK4,sK1,sK2)),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f7,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f15,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.27/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.27/0.99  
% 3.27/0.99  fof(f20,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f15])).
% 3.27/0.99  
% 3.27/0.99  fof(f52,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f20])).
% 3.27/0.99  
% 3.27/0.99  fof(f4,axiom,(
% 3.27/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f17,plain,(
% 3.27/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f4])).
% 3.27/0.99  
% 3.27/0.99  fof(f37,plain,(
% 3.27/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(nnf_transformation,[],[f17])).
% 3.27/0.99  
% 3.27/0.99  fof(f48,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f37])).
% 3.27/0.99  
% 3.27/0.99  fof(f6,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f19,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f6])).
% 3.27/0.99  
% 3.27/0.99  fof(f51,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f19])).
% 3.27/0.99  
% 3.27/0.99  fof(f9,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f22,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f9])).
% 3.27/0.99  
% 3.27/0.99  fof(f54,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f22])).
% 3.27/0.99  
% 3.27/0.99  fof(f66,plain,(
% 3.27/0.99    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f58,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f38])).
% 3.27/0.99  
% 3.27/0.99  fof(f68,plain,(
% 3.27/0.99    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f63,plain,(
% 3.27/0.99    v1_funct_1(sK4)),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f67,plain,(
% 3.27/0.99    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f1,axiom,(
% 3.27/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f16,plain,(
% 3.27/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f1])).
% 3.27/0.99  
% 3.27/0.99  fof(f31,plain,(
% 3.27/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/0.99    inference(nnf_transformation,[],[f16])).
% 3.27/0.99  
% 3.27/0.99  fof(f32,plain,(
% 3.27/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/0.99    inference(rectify,[],[f31])).
% 3.27/0.99  
% 3.27/0.99  fof(f33,plain,(
% 3.27/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f34,plain,(
% 3.27/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.27/0.99  
% 3.27/0.99  fof(f42,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f34])).
% 3.27/0.99  
% 3.27/0.99  fof(f41,plain,(
% 3.27/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f34])).
% 3.27/0.99  
% 3.27/0.99  fof(f3,axiom,(
% 3.27/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f47,plain,(
% 3.27/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f3])).
% 3.27/0.99  
% 3.27/0.99  fof(f12,axiom,(
% 3.27/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f27,plain,(
% 3.27/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.27/0.99    inference(ennf_transformation,[],[f12])).
% 3.27/0.99  
% 3.27/0.99  fof(f28,plain,(
% 3.27/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.27/0.99    inference(flattening,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f62,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f28])).
% 3.27/0.99  
% 3.27/0.99  fof(f5,axiom,(
% 3.27/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f18,plain,(
% 3.27/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f5])).
% 3.27/0.99  
% 3.27/0.99  fof(f50,plain,(
% 3.27/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f2,axiom,(
% 3.27/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f35,plain,(
% 3.27/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.27/0.99    inference(nnf_transformation,[],[f2])).
% 3.27/0.99  
% 3.27/0.99  fof(f36,plain,(
% 3.27/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.27/0.99    inference(flattening,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f46,plain,(
% 3.27/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f36])).
% 3.27/0.99  
% 3.27/0.99  fof(f43,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f34])).
% 3.27/0.99  
% 3.27/0.99  fof(f59,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f38])).
% 3.27/0.99  
% 3.27/0.99  fof(f74,plain,(
% 3.27/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.27/0.99    inference(equality_resolution,[],[f59])).
% 3.27/0.99  
% 3.27/0.99  fof(f57,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f38])).
% 3.27/0.99  
% 3.27/0.99  fof(f75,plain,(
% 3.27/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.27/0.99    inference(equality_resolution,[],[f57])).
% 3.27/0.99  
% 3.27/0.99  cnf(c_14,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.27/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.27/0.99      | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1661,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.27/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_25,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.27/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1659,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_12,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1663,plain,
% 3.27/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.27/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2591,plain,
% 3.27/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1659,c_1663]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_20,plain,
% 3.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_26,negated_conjecture,
% 3.27/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.27/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_988,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.27/0.99      | sK2 != X2
% 3.27/0.99      | sK1 != X1
% 3.27/0.99      | sK4 != X0
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_989,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.27/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.27/0.99      | k1_xboole_0 = sK2 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_988]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_991,plain,
% 3.27/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_989,c_25]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2889,plain,
% 3.27/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2591,c_991]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_11,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | v4_relat_1(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8,plain,
% 3.27/0.99      ( ~ v4_relat_1(X0,X1)
% 3.27/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.27/0.99      | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_325,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.27/0.99      | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_10,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_329,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_325,c_10]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_330,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_329]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1658,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2537,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1659,c_1658]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_13,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1662,plain,
% 3.27/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.27/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2587,plain,
% 3.27/0.99      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1659,c_1662]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_24,negated_conjecture,
% 3.27/0.99      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 3.27/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1660,plain,
% 3.27/0.99      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2744,plain,
% 3.27/0.99      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_2587,c_1660]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3075,plain,
% 3.27/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.27/0.99      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.27/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1661,c_1663]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3551,plain,
% 3.27/0.99      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.27/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2744,c_3075]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_30,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1845,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.27/0.99      | v1_relat_1(sK4) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1846,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.27/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1845]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3879,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.27/0.99      | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_3551,c_30,c_1846]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3880,plain,
% 3.27/0.99      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_3879]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3888,plain,
% 3.27/0.99      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2537,c_3880]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_18,plain,
% 3.27/0.99      ( v1_funct_2(X0,X1,X2)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_22,negated_conjecture,
% 3.27/0.99      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.27/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.27/0.99      | ~ v1_funct_1(sK4) ),
% 3.27/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_27,negated_conjecture,
% 3.27/0.99      ( v1_funct_1(sK4) ),
% 3.27/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_148,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.27/0.99      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_22,c_27]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_149,negated_conjecture,
% 3.27/0.99      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.27/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_148]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_975,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.27/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.27/0.99      | sK3 != X2
% 3.27/0.99      | sK1 != X1
% 3.27/0.99      | sK4 != X0
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_149]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_976,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.27/0.99      | k1_relset_1(sK1,sK3,sK4) != sK1
% 3.27/0.99      | k1_xboole_0 = sK3 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_975]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1653,plain,
% 3.27/0.99      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.27/0.99      | k1_xboole_0 = sK3
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_976]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3928,plain,
% 3.27/0.99      ( k1_relat_1(sK4) != sK1
% 3.27/0.99      | sK3 = k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_3888,c_1653]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3935,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | sK3 = k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2889,c_3928]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3994,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | sK3 = k1_xboole_0
% 3.27/0.99      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),sK1) != iProver_top
% 3.27/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1661,c_3935]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1852,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),sK1) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_330]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1853,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),sK1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1852]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6885,plain,
% 3.27/0.99      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_3994,c_30,c_1846,c_1853,c_2744]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6886,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_6885]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_23,negated_conjecture,
% 3.27/0.99      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.27/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6895,plain,
% 3.27/0.99      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_6886,c_23]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1670,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.27/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1669,plain,
% 3.27/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.27/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.27/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2672,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1670,c_1669]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3200,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X3) != iProver_top
% 3.27/0.99      | r1_tarski(X3,X2) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2672,c_1669]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4947,plain,
% 3.27/0.99      ( r2_hidden(sK0(k1_relat_1(sK4),X0),X1) = iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.27/0.99      | r1_tarski(sK1,X1) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2537,c_3200]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6,plain,
% 3.27/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1666,plain,
% 3.27/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_21,plain,
% 3.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | ~ r2_hidden(X3,X1)
% 3.27/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_298,plain,
% 3.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | ~ r2_hidden(X3,X1)
% 3.27/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.27/0.99      | sK4 != X0
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_299,plain,
% 3.27/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 3.27/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.27/0.99      | ~ r2_hidden(X2,X0)
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X2),k2_relset_1(X0,X1,sK4))
% 3.27/0.99      | k1_xboole_0 = X1 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_298]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1033,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.27/0.99      | ~ r2_hidden(X2,X0)
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X2),k2_relset_1(X0,X1,sK4))
% 3.27/0.99      | sK2 != X1
% 3.27/0.99      | sK1 != X0
% 3.27/0.99      | sK4 != sK4
% 3.27/0.99      | k1_xboole_0 = X1 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_299]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1034,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.27/0.99      | ~ r2_hidden(X0,sK1)
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))
% 3.27/0.99      | k1_xboole_0 = sK2 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_1033]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1038,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,sK1)
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))
% 3.27/0.99      | k1_xboole_0 = sK2 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_1034,c_25]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1651,plain,
% 3.27/0.99      ( k1_xboole_0 = sK2
% 3.27/0.99      | r2_hidden(X0,sK1) != iProver_top
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1038]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2743,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r2_hidden(X0,sK1) != iProver_top
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_2587,c_1651]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3296,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r2_hidden(X0,sK1) != iProver_top
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
% 3.27/0.99      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2743,c_1669]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3321,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r2_hidden(X0,sK1) != iProver_top
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
% 3.27/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.27/0.99      | r1_tarski(k2_relat_1(sK4),X2) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_3296,c_1669]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3458,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r2_hidden(X0,sK1) != iProver_top
% 3.27/0.99      | r2_hidden(k1_funct_1(sK4,X0),X1) = iProver_top
% 3.27/0.99      | r1_tarski(sK3,X1) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2744,c_3321]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_9,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1665,plain,
% 3.27/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.27/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3522,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r2_hidden(X0,sK1) != iProver_top
% 3.27/0.99      | r1_tarski(X1,k1_funct_1(sK4,X0)) != iProver_top
% 3.27/0.99      | r1_tarski(sK3,X1) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_3458,c_1665]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4452,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r2_hidden(X0,sK1) != iProver_top
% 3.27/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1666,c_3522]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5318,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.27/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.27/0.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_4947,c_4452]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_79,plain,
% 3.27/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_78,plain,
% 3.27/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_80,plain,
% 3.27/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_78]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3,plain,
% 3.27/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_84,plain,
% 3.27/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.27/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1269,plain,
% 3.27/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.27/0.99      theory(equality) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1926,plain,
% 3.27/0.99      ( ~ r1_tarski(X0,X1)
% 3.27/0.99      | r1_tarski(sK1,k1_xboole_0)
% 3.27/0.99      | sK1 != X0
% 3.27/0.99      | k1_xboole_0 != X1 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1269]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1927,plain,
% 3.27/0.99      ( sK1 != X0
% 3.27/0.99      | k1_xboole_0 != X1
% 3.27/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.27/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1929,plain,
% 3.27/0.99      ( sK1 != k1_xboole_0
% 3.27/0.99      | k1_xboole_0 != k1_xboole_0
% 3.27/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.27/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1927]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1268,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1861,plain,
% 3.27/0.99      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1268]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1934,plain,
% 3.27/0.99      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1861]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1267,plain,( X0 = X0 ),theory(equality) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1935,plain,
% 3.27/0.99      ( sK1 = sK1 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1267]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2939,plain,
% 3.27/0.99      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1268]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2940,plain,
% 3.27/0.99      ( sK2 != k1_xboole_0
% 3.27/0.99      | k1_xboole_0 = sK2
% 3.27/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_2939]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5137,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.27/0.99      | r1_tarski(sK1,X0) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1670,c_4452]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_0,plain,
% 3.27/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1671,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5315,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.27/0.99      | r1_tarski(sK1,X0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_4947,c_1671]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3201,plain,
% 3.27/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X2) = iProver_top
% 3.27/0.99      | r1_tarski(X1,sK0(X0,X2)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2672,c_1665]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3674,plain,
% 3.27/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.27/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1666,c_3201]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5732,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.27/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_5315,c_3674]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6588,plain,
% 3.27/0.99      ( r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_5318,c_23,c_79,c_80,c_84,c_1929,c_1934,c_1935,c_2940,
% 3.27/0.99                 c_5137,c_5315,c_5732]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6589,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.27/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_6588]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6601,plain,
% 3.27/0.99      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.27/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_6589,c_3880]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7021,plain,
% 3.27/0.99      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.27/0.99      | sK1 = k1_xboole_0
% 3.27/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_6895,c_6601]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1928,plain,
% 3.27/0.99      ( r1_tarski(sK1,k1_xboole_0)
% 3.27/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.27/0.99      | sK1 != k1_xboole_0
% 3.27/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3881,plain,
% 3.27/0.99      ( ~ r1_tarski(k1_relat_1(sK4),X0)
% 3.27/0.99      | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
% 3.27/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3880]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5816,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK4),X0) | ~ r1_tarski(sK1,k1_xboole_0) ),
% 3.27/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5732]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7097,plain,
% 3.27/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.27/0.99      | k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.27/0.99      | sK1 = k1_xboole_0 ),
% 3.27/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7021]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7523,plain,
% 3.27/0.99      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_7021,c_79,c_84,c_1928,c_3881,c_5816,c_7097]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_17,plain,
% 3.27/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.27/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_925,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.27/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.27/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.27/0.99      | sK3 != X1
% 3.27/0.99      | sK1 != k1_xboole_0
% 3.27/0.99      | sK4 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_149]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_926,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.27/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.27/0.99      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.27/0.99      | sK1 != k1_xboole_0 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_925]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1655,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.27/0.99      | sK1 != k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7527,plain,
% 3.27/0.99      ( k1_relat_1(sK4) != k1_xboole_0
% 3.27/0.99      | sK1 != k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_7523,c_1655]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_927,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.27/0.99      | sK1 != k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7025,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0
% 3.27/0.99      | sK1 = k1_xboole_0
% 3.27/0.99      | r1_tarski(sK1,X0) = iProver_top
% 3.27/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_6895,c_5137]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7714,plain,
% 3.27/0.99      ( r1_tarski(sK1,X0) = iProver_top | sK1 = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_7025,c_23,c_79,c_80,c_84,c_1934,c_1935,c_2940]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7715,plain,
% 3.27/0.99      ( sK1 = k1_xboole_0 | r1_tarski(sK1,X0) = iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_7714]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1668,plain,
% 3.27/0.99      ( X0 = X1
% 3.27/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.27/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2656,plain,
% 3.27/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1666,c_1668]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7730,plain,
% 3.27/0.99      ( sK1 = k1_xboole_0 ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_7715,c_2656]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7856,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_relat_1(sK4) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_7730,c_3888]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7867,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_7730,c_2591]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_19,plain,
% 3.27/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.27/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_941,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.27/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.27/0.99      | sK2 != X1
% 3.27/0.99      | sK1 != k1_xboole_0
% 3.27/0.99      | sK4 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_942,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.27/0.99      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.27/0.99      | sK1 != k1_xboole_0 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_941]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1654,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.27/0.99      | sK1 != k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7873,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.27/0.99      | k1_xboole_0 != k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_7730,c_1654]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7883,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_7873]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7875,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_7730,c_1659]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7886,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0 ),
% 3.27/0.99      inference(forward_subsumption_resolution,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_7883,c_7875]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7896,plain,
% 3.27/0.99      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_7867,c_7886]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7956,plain,
% 3.27/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0 ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_7856,c_7896]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8316,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_7527,c_927,c_7730,c_7956]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8320,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_8316,c_7730]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8323,plain,
% 3.27/0.99      ( r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.27/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1661,c_8320]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5357,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK4),k1_xboole_0) = iProver_top
% 3.27/0.99      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_5315]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(contradiction,plain,
% 3.27/0.99      ( $false ),
% 3.27/0.99      inference(minisat,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_8323,c_7730,c_5357,c_2744,c_1929,c_1846,c_84,c_80,
% 3.27/0.99                 c_79,c_30]) ).
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  ------                               Statistics
% 3.27/0.99  
% 3.27/0.99  ------ General
% 3.27/0.99  
% 3.27/0.99  abstr_ref_over_cycles:                  0
% 3.27/0.99  abstr_ref_under_cycles:                 0
% 3.27/0.99  gc_basic_clause_elim:                   0
% 3.27/0.99  forced_gc_time:                         0
% 3.27/0.99  parsing_time:                           0.022
% 3.27/0.99  unif_index_cands_time:                  0.
% 3.27/0.99  unif_index_add_time:                    0.
% 3.27/0.99  orderings_time:                         0.
% 3.27/0.99  out_proof_time:                         0.009
% 3.27/0.99  total_time:                             0.255
% 3.27/0.99  num_of_symbols:                         51
% 3.27/0.99  num_of_terms:                           5046
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing
% 3.27/0.99  
% 3.27/0.99  num_of_splits:                          0
% 3.27/0.99  num_of_split_atoms:                     0
% 3.27/0.99  num_of_reused_defs:                     0
% 3.27/0.99  num_eq_ax_congr_red:                    23
% 3.27/0.99  num_of_sem_filtered_clauses:            1
% 3.27/0.99  num_of_subtypes:                        0
% 3.27/0.99  monotx_restored_types:                  0
% 3.27/0.99  sat_num_of_epr_types:                   0
% 3.27/0.99  sat_num_of_non_cyclic_types:            0
% 3.27/0.99  sat_guarded_non_collapsed_types:        0
% 3.27/0.99  num_pure_diseq_elim:                    0
% 3.27/0.99  simp_replaced_by:                       0
% 3.27/0.99  res_preprocessed:                       120
% 3.27/0.99  prep_upred:                             0
% 3.27/0.99  prep_unflattend:                        59
% 3.27/0.99  smt_new_axioms:                         0
% 3.27/0.99  pred_elim_cands:                        4
% 3.27/0.99  pred_elim:                              3
% 3.27/0.99  pred_elim_cl:                           3
% 3.27/0.99  pred_elim_cycles:                       7
% 3.27/0.99  merged_defs:                            0
% 3.27/0.99  merged_defs_ncl:                        0
% 3.27/0.99  bin_hyper_res:                          0
% 3.27/0.99  prep_cycles:                            4
% 3.27/0.99  pred_elim_time:                         0.025
% 3.27/0.99  splitting_time:                         0.
% 3.27/0.99  sem_filter_time:                        0.
% 3.27/0.99  monotx_time:                            0.
% 3.27/0.99  subtype_inf_time:                       0.
% 3.27/0.99  
% 3.27/0.99  ------ Problem properties
% 3.27/0.99  
% 3.27/0.99  clauses:                                24
% 3.27/0.99  conjectures:                            3
% 3.27/0.99  epr:                                    6
% 3.27/0.99  horn:                                   19
% 3.27/0.99  ground:                                 10
% 3.27/0.99  unary:                                  4
% 3.27/0.99  binary:                                 10
% 3.27/0.99  lits:                                   61
% 3.27/0.99  lits_eq:                                23
% 3.27/0.99  fd_pure:                                0
% 3.27/0.99  fd_pseudo:                              0
% 3.27/0.99  fd_cond:                                1
% 3.27/0.99  fd_pseudo_cond:                         1
% 3.27/0.99  ac_symbols:                             0
% 3.27/0.99  
% 3.27/0.99  ------ Propositional Solver
% 3.27/0.99  
% 3.27/0.99  prop_solver_calls:                      31
% 3.27/0.99  prop_fast_solver_calls:                 1162
% 3.27/0.99  smt_solver_calls:                       0
% 3.27/0.99  smt_fast_solver_calls:                  0
% 3.27/0.99  prop_num_of_clauses:                    2542
% 3.27/0.99  prop_preprocess_simplified:             6289
% 3.27/0.99  prop_fo_subsumed:                       31
% 3.27/0.99  prop_solver_time:                       0.
% 3.27/0.99  smt_solver_time:                        0.
% 3.27/0.99  smt_fast_solver_time:                   0.
% 3.27/0.99  prop_fast_solver_time:                  0.
% 3.27/0.99  prop_unsat_core_time:                   0.
% 3.27/0.99  
% 3.27/0.99  ------ QBF
% 3.27/0.99  
% 3.27/0.99  qbf_q_res:                              0
% 3.27/0.99  qbf_num_tautologies:                    0
% 3.27/0.99  qbf_prep_cycles:                        0
% 3.27/0.99  
% 3.27/0.99  ------ BMC1
% 3.27/0.99  
% 3.27/0.99  bmc1_current_bound:                     -1
% 3.27/0.99  bmc1_last_solved_bound:                 -1
% 3.27/0.99  bmc1_unsat_core_size:                   -1
% 3.27/0.99  bmc1_unsat_core_parents_size:           -1
% 3.27/0.99  bmc1_merge_next_fun:                    0
% 3.27/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation
% 3.27/0.99  
% 3.27/0.99  inst_num_of_clauses:                    722
% 3.27/0.99  inst_num_in_passive:                    124
% 3.27/0.99  inst_num_in_active:                     458
% 3.27/0.99  inst_num_in_unprocessed:                140
% 3.27/0.99  inst_num_of_loops:                      580
% 3.27/0.99  inst_num_of_learning_restarts:          0
% 3.27/0.99  inst_num_moves_active_passive:          117
% 3.27/0.99  inst_lit_activity:                      0
% 3.27/0.99  inst_lit_activity_moves:                0
% 3.27/0.99  inst_num_tautologies:                   0
% 3.27/0.99  inst_num_prop_implied:                  0
% 3.27/0.99  inst_num_existing_simplified:           0
% 3.27/0.99  inst_num_eq_res_simplified:             0
% 3.27/0.99  inst_num_child_elim:                    0
% 3.27/0.99  inst_num_of_dismatching_blockings:      266
% 3.27/0.99  inst_num_of_non_proper_insts:           1035
% 3.27/0.99  inst_num_of_duplicates:                 0
% 3.27/0.99  inst_inst_num_from_inst_to_res:         0
% 3.27/0.99  inst_dismatching_checking_time:         0.
% 3.27/0.99  
% 3.27/0.99  ------ Resolution
% 3.27/0.99  
% 3.27/0.99  res_num_of_clauses:                     0
% 3.27/0.99  res_num_in_passive:                     0
% 3.27/0.99  res_num_in_active:                      0
% 3.27/0.99  res_num_of_loops:                       124
% 3.27/0.99  res_forward_subset_subsumed:            87
% 3.27/0.99  res_backward_subset_subsumed:           0
% 3.27/0.99  res_forward_subsumed:                   0
% 3.27/0.99  res_backward_subsumed:                  1
% 3.27/0.99  res_forward_subsumption_resolution:     0
% 3.27/0.99  res_backward_subsumption_resolution:    0
% 3.27/0.99  res_clause_to_clause_subsumption:       1023
% 3.27/0.99  res_orphan_elimination:                 0
% 3.27/0.99  res_tautology_del:                      77
% 3.27/0.99  res_num_eq_res_simplified:              1
% 3.27/0.99  res_num_sel_changes:                    0
% 3.27/0.99  res_moves_from_active_to_pass:          0
% 3.27/0.99  
% 3.27/0.99  ------ Superposition
% 3.27/0.99  
% 3.27/0.99  sup_time_total:                         0.
% 3.27/0.99  sup_time_generating:                    0.
% 3.27/0.99  sup_time_sim_full:                      0.
% 3.27/0.99  sup_time_sim_immed:                     0.
% 3.27/0.99  
% 3.27/0.99  sup_num_of_clauses:                     121
% 3.27/0.99  sup_num_in_active:                      53
% 3.27/0.99  sup_num_in_passive:                     68
% 3.27/0.99  sup_num_of_loops:                       114
% 3.27/0.99  sup_fw_superposition:                   120
% 3.27/0.99  sup_bw_superposition:                   163
% 3.27/0.99  sup_immediate_simplified:               96
% 3.27/0.99  sup_given_eliminated:                   1
% 3.27/0.99  comparisons_done:                       0
% 3.27/0.99  comparisons_avoided:                    39
% 3.27/0.99  
% 3.27/0.99  ------ Simplifications
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  sim_fw_subset_subsumed:                 49
% 3.27/0.99  sim_bw_subset_subsumed:                 27
% 3.27/0.99  sim_fw_subsumed:                        22
% 3.27/0.99  sim_bw_subsumed:                        2
% 3.27/0.99  sim_fw_subsumption_res:                 3
% 3.27/0.99  sim_bw_subsumption_res:                 0
% 3.27/0.99  sim_tautology_del:                      9
% 3.27/0.99  sim_eq_tautology_del:                   20
% 3.27/0.99  sim_eq_res_simp:                        3
% 3.27/0.99  sim_fw_demodulated:                     3
% 3.27/0.99  sim_bw_demodulated:                     53
% 3.27/0.99  sim_light_normalised:                   20
% 3.27/0.99  sim_joinable_taut:                      0
% 3.27/0.99  sim_joinable_simp:                      0
% 3.27/0.99  sim_ac_normalised:                      0
% 3.27/0.99  sim_smt_subsumption:                    0
% 3.27/0.99  
%------------------------------------------------------------------------------
