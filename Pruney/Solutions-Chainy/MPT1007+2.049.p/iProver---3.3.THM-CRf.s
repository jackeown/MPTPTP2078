%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:51 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 548 expanded)
%              Number of clauses        :   80 ( 152 expanded)
%              Number of leaves         :   28 ( 126 expanded)
%              Depth                    :   24
%              Number of atoms          :  484 (1559 expanded)
%              Number of equality atoms :  191 ( 525 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f59])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f62,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
      & k1_xboole_0 != sK6
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
      & v1_funct_2(sK7,k1_tarski(sK5),sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    & k1_xboole_0 != sK6
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
    & v1_funct_2(sK7,k1_tarski(sK5),sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f62])).

fof(f100,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f104,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f103])).

fof(f109,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(definition_unfolding,[],[f100,f104])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
            & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f46])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f69,f104])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f21,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    v1_funct_2(sK7,k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f110,plain,(
    v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
    inference(definition_unfolding,[],[f99,f104])).

fof(f101,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f54])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f55,f57,f56])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f105,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f68,f104])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f48])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_24,plain,
    ( r2_hidden(sK4(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1429,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1427,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2022,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_1433])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1436,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2067,plain,
    ( k10_relat_1(sK7,k2_relat_1(sK7)) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2022,c_1436])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1438,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1444,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3132,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_1444])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1446,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3584,plain,
    ( sK5 = X0
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3132,c_1446])).

cnf(c_4115,plain,
    ( sK5 = X0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_3584])).

cnf(c_38,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1675,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1676,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1675])).

cnf(c_5974,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | sK5 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4115,c_38,c_1676])).

cnf(c_5975,plain,
    ( sK5 = X0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5974])).

cnf(c_5988,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_5975])).

cnf(c_6140,plain,
    ( sK4(k1_relat_1(sK7)) = sK5
    | k1_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1429,c_5988])).

cnf(c_6960,plain,
    ( k1_relat_1(sK7) = k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6140,c_1429])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_425,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_426,plain,
    ( ~ v5_relat_1(sK7,X0)
    | ~ r2_hidden(X1,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X1),X0)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X3),X4)
    | ~ v1_relat_1(sK7)
    | X4 != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_426])).

cnf(c_449,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X2),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_461,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X2),X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_449,c_19])).

cnf(c_1425,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1744,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_1425])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1428,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1751,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1428])).

cnf(c_6963,plain,
    ( k1_relat_1(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6960,c_1751])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1434,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6978,plain,
    ( sK7 = k1_xboole_0
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6963,c_1434])).

cnf(c_1819,plain,
    ( ~ v1_relat_1(sK7)
    | k1_relat_1(sK7) != k1_xboole_0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_968,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1830,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_969,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2455,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_4308,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2455])).

cnf(c_4309,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_4308])).

cnf(c_7274,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6978,c_33,c_1675,c_1751,c_1819,c_1830,c_4309,c_6960])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X2
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_643,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
    | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_645,plain,
    ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_33,c_32])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK2(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1432,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3986,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_1432])).

cnf(c_4612,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3986,c_38])).

cnf(c_7288,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7274,c_4612])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_400,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_401,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1426,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_7461,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7288,c_1426])).

cnf(c_7467,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1429,c_7461])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1449,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7967,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7467,c_1449])).

cnf(c_5,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1445,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1442,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2419,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1442])).

cnf(c_4363,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_1426])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7967,c_4363])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:03:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.34/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.98  
% 3.34/0.98  ------  iProver source info
% 3.34/0.98  
% 3.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.98  git: non_committed_changes: false
% 3.34/0.98  git: last_make_outside_of_git: false
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     num_symb
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       true
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  ------ Parsing...
% 3.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.98  ------ Proving...
% 3.34/0.98  ------ Problem Properties 
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  clauses                                 29
% 3.34/0.98  conjectures                             3
% 3.34/0.98  EPR                                     3
% 3.34/0.98  Horn                                    25
% 3.34/0.98  unary                                   8
% 3.34/0.98  binary                                  6
% 3.34/0.98  lits                                    69
% 3.34/0.98  lits eq                                 17
% 3.34/0.98  fd_pure                                 0
% 3.34/0.98  fd_pseudo                               0
% 3.34/0.98  fd_cond                                 3
% 3.34/0.98  fd_pseudo_cond                          1
% 3.34/0.98  AC symbols                              0
% 3.34/0.98  
% 3.34/0.98  ------ Schedule dynamic 5 is on 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  Current options:
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     none
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       false
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ Proving...
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS status Theorem for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  fof(f20,axiom,(
% 3.34/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f24,plain,(
% 3.34/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.34/0.99    inference(pure_predicate_removal,[],[f20])).
% 3.34/0.99  
% 3.34/0.99  fof(f41,plain,(
% 3.34/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.34/0.99    inference(ennf_transformation,[],[f24])).
% 3.34/0.99  
% 3.34/0.99  fof(f59,plain,(
% 3.34/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 3.34/0.99    introduced(choice_axiom,[])).
% 3.34/0.99  
% 3.34/0.99  fof(f60,plain,(
% 3.34/0.99    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 3.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f59])).
% 3.34/0.99  
% 3.34/0.99  fof(f91,plain,(
% 3.34/0.99    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 3.34/0.99    inference(cnf_transformation,[],[f60])).
% 3.34/0.99  
% 3.34/0.99  fof(f22,conjecture,(
% 3.34/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f23,negated_conjecture,(
% 3.34/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.34/0.99    inference(negated_conjecture,[],[f22])).
% 3.34/0.99  
% 3.34/0.99  fof(f44,plain,(
% 3.34/0.99    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.34/0.99    inference(ennf_transformation,[],[f23])).
% 3.34/0.99  
% 3.34/0.99  fof(f45,plain,(
% 3.34/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.34/0.99    inference(flattening,[],[f44])).
% 3.34/0.99  
% 3.34/0.99  fof(f62,plain,(
% 3.34/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7))),
% 3.34/0.99    introduced(choice_axiom,[])).
% 3.34/0.99  
% 3.34/0.99  fof(f63,plain,(
% 3.34/0.99    ~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7)),
% 3.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f62])).
% 3.34/0.99  
% 3.34/0.99  fof(f100,plain,(
% 3.34/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))),
% 3.34/0.99    inference(cnf_transformation,[],[f63])).
% 3.34/0.99  
% 3.34/0.99  fof(f2,axiom,(
% 3.34/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f65,plain,(
% 3.34/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f2])).
% 3.34/0.99  
% 3.34/0.99  fof(f3,axiom,(
% 3.34/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f66,plain,(
% 3.34/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f3])).
% 3.34/0.99  
% 3.34/0.99  fof(f4,axiom,(
% 3.34/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f67,plain,(
% 3.34/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f4])).
% 3.34/0.99  
% 3.34/0.99  fof(f103,plain,(
% 3.34/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.34/0.99    inference(definition_unfolding,[],[f66,f67])).
% 3.34/0.99  
% 3.34/0.99  fof(f104,plain,(
% 3.34/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.34/0.99    inference(definition_unfolding,[],[f65,f103])).
% 3.34/0.99  
% 3.34/0.99  fof(f109,plain,(
% 3.34/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))),
% 3.34/0.99    inference(definition_unfolding,[],[f100,f104])).
% 3.34/0.99  
% 3.34/0.99  fof(f17,axiom,(
% 3.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f38,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.99    inference(ennf_transformation,[],[f17])).
% 3.34/0.99  
% 3.34/0.99  fof(f86,plain,(
% 3.34/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.99    inference(cnf_transformation,[],[f38])).
% 3.34/0.99  
% 3.34/0.99  fof(f13,axiom,(
% 3.34/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f32,plain,(
% 3.34/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.34/0.99    inference(ennf_transformation,[],[f13])).
% 3.34/0.99  
% 3.34/0.99  fof(f81,plain,(
% 3.34/0.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f32])).
% 3.34/0.99  
% 3.34/0.99  fof(f12,axiom,(
% 3.34/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f31,plain,(
% 3.34/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.34/0.99    inference(ennf_transformation,[],[f12])).
% 3.34/0.99  
% 3.34/0.99  fof(f50,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.34/0.99    inference(nnf_transformation,[],[f31])).
% 3.34/0.99  
% 3.34/0.99  fof(f51,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.34/0.99    inference(rectify,[],[f50])).
% 3.34/0.99  
% 3.34/0.99  fof(f52,plain,(
% 3.34/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 3.34/0.99    introduced(choice_axiom,[])).
% 3.34/0.99  
% 3.34/0.99  fof(f53,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).
% 3.34/0.99  
% 3.34/0.99  fof(f78,plain,(
% 3.34/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f53])).
% 3.34/0.99  
% 3.34/0.99  fof(f8,axiom,(
% 3.34/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f26,plain,(
% 3.34/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/0.99    inference(ennf_transformation,[],[f8])).
% 3.34/0.99  
% 3.34/0.99  fof(f73,plain,(
% 3.34/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/0.99    inference(cnf_transformation,[],[f26])).
% 3.34/0.99  
% 3.34/0.99  fof(f6,axiom,(
% 3.34/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f46,plain,(
% 3.34/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 3.34/0.99    inference(nnf_transformation,[],[f6])).
% 3.34/0.99  
% 3.34/0.99  fof(f47,plain,(
% 3.34/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 3.34/0.99    inference(flattening,[],[f46])).
% 3.34/0.99  
% 3.34/0.99  fof(f69,plain,(
% 3.34/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 3.34/0.99    inference(cnf_transformation,[],[f47])).
% 3.34/0.99  
% 3.34/0.99  fof(f108,plain,(
% 3.34/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))) )),
% 3.34/0.99    inference(definition_unfolding,[],[f69,f104])).
% 3.34/0.99  
% 3.34/0.99  fof(f18,axiom,(
% 3.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f25,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.34/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.34/0.99  
% 3.34/0.99  fof(f39,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.99    inference(ennf_transformation,[],[f25])).
% 3.34/0.99  
% 3.34/0.99  fof(f87,plain,(
% 3.34/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.99    inference(cnf_transformation,[],[f39])).
% 3.34/0.99  
% 3.34/0.99  fof(f15,axiom,(
% 3.34/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f35,plain,(
% 3.34/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.34/0.99    inference(ennf_transformation,[],[f15])).
% 3.34/0.99  
% 3.34/0.99  fof(f36,plain,(
% 3.34/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.99    inference(flattening,[],[f35])).
% 3.34/0.99  
% 3.34/0.99  fof(f84,plain,(
% 3.34/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f36])).
% 3.34/0.99  
% 3.34/0.99  fof(f98,plain,(
% 3.34/0.99    v1_funct_1(sK7)),
% 3.34/0.99    inference(cnf_transformation,[],[f63])).
% 3.34/0.99  
% 3.34/0.99  fof(f102,plain,(
% 3.34/0.99    ~r2_hidden(k1_funct_1(sK7,sK5),sK6)),
% 3.34/0.99    inference(cnf_transformation,[],[f63])).
% 3.34/0.99  
% 3.34/0.99  fof(f14,axiom,(
% 3.34/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f33,plain,(
% 3.34/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.34/0.99    inference(ennf_transformation,[],[f14])).
% 3.34/0.99  
% 3.34/0.99  fof(f34,plain,(
% 3.34/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.34/0.99    inference(flattening,[],[f33])).
% 3.34/0.99  
% 3.34/0.99  fof(f82,plain,(
% 3.34/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f34])).
% 3.34/0.99  
% 3.34/0.99  fof(f21,axiom,(
% 3.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f42,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.99    inference(ennf_transformation,[],[f21])).
% 3.34/0.99  
% 3.34/0.99  fof(f43,plain,(
% 3.34/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.99    inference(flattening,[],[f42])).
% 3.34/0.99  
% 3.34/0.99  fof(f61,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.99    inference(nnf_transformation,[],[f43])).
% 3.34/0.99  
% 3.34/0.99  fof(f92,plain,(
% 3.34/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.99    inference(cnf_transformation,[],[f61])).
% 3.34/0.99  
% 3.34/0.99  fof(f99,plain,(
% 3.34/0.99    v1_funct_2(sK7,k1_tarski(sK5),sK6)),
% 3.34/0.99    inference(cnf_transformation,[],[f63])).
% 3.34/0.99  
% 3.34/0.99  fof(f110,plain,(
% 3.34/0.99    v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6)),
% 3.34/0.99    inference(definition_unfolding,[],[f99,f104])).
% 3.34/0.99  
% 3.34/0.99  fof(f101,plain,(
% 3.34/0.99    k1_xboole_0 != sK6),
% 3.34/0.99    inference(cnf_transformation,[],[f63])).
% 3.34/0.99  
% 3.34/0.99  fof(f19,axiom,(
% 3.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f40,plain,(
% 3.34/0.99    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.34/0.99    inference(ennf_transformation,[],[f19])).
% 3.34/0.99  
% 3.34/0.99  fof(f54,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.34/0.99    inference(nnf_transformation,[],[f40])).
% 3.34/0.99  
% 3.34/0.99  fof(f55,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.34/0.99    inference(rectify,[],[f54])).
% 3.34/0.99  
% 3.34/0.99  fof(f57,plain,(
% 3.34/0.99    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 3.34/0.99    introduced(choice_axiom,[])).
% 3.34/0.99  
% 3.34/0.99  fof(f56,plain,(
% 3.34/0.99    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 3.34/0.99    introduced(choice_axiom,[])).
% 3.34/0.99  
% 3.34/0.99  fof(f58,plain,(
% 3.34/0.99    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f55,f57,f56])).
% 3.34/0.99  
% 3.34/0.99  fof(f90,plain,(
% 3.34/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.34/0.99    inference(cnf_transformation,[],[f58])).
% 3.34/0.99  
% 3.34/0.99  fof(f1,axiom,(
% 3.34/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f64,plain,(
% 3.34/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f1])).
% 3.34/0.99  
% 3.34/0.99  fof(f16,axiom,(
% 3.34/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f37,plain,(
% 3.34/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.34/0.99    inference(ennf_transformation,[],[f16])).
% 3.34/0.99  
% 3.34/0.99  fof(f85,plain,(
% 3.34/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f37])).
% 3.34/0.99  
% 3.34/0.99  fof(f5,axiom,(
% 3.34/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f68,plain,(
% 3.34/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.34/0.99    inference(cnf_transformation,[],[f5])).
% 3.34/0.99  
% 3.34/0.99  fof(f105,plain,(
% 3.34/0.99    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 3.34/0.99    inference(definition_unfolding,[],[f68,f104])).
% 3.34/0.99  
% 3.34/0.99  fof(f7,axiom,(
% 3.34/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f48,plain,(
% 3.34/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 3.34/0.99    introduced(choice_axiom,[])).
% 3.34/0.99  
% 3.34/0.99  fof(f49,plain,(
% 3.34/0.99    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 3.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f48])).
% 3.34/0.99  
% 3.34/0.99  fof(f72,plain,(
% 3.34/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f49])).
% 3.34/0.99  
% 3.34/0.99  fof(f10,axiom,(
% 3.34/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.99  
% 3.34/0.99  fof(f27,plain,(
% 3.34/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.34/0.99    inference(ennf_transformation,[],[f10])).
% 3.34/0.99  
% 3.34/0.99  fof(f28,plain,(
% 3.34/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.34/0.99    inference(flattening,[],[f27])).
% 3.34/0.99  
% 3.34/0.99  fof(f75,plain,(
% 3.34/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.34/0.99    inference(cnf_transformation,[],[f28])).
% 3.34/0.99  
% 3.34/0.99  cnf(c_24,plain,
% 3.34/0.99      ( r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0 ),
% 3.34/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1429,plain,
% 3.34/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_33,negated_conjecture,
% 3.34/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
% 3.34/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1427,plain,
% 3.34/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_19,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.99      | v1_relat_1(X0) ),
% 3.34/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1433,plain,
% 3.34/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2022,plain,
% 3.34/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1427,c_1433]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_14,plain,
% 3.34/0.99      ( ~ v1_relat_1(X0)
% 3.34/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.34/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1436,plain,
% 3.34/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.34/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2067,plain,
% 3.34/0.99      ( k10_relat_1(sK7,k2_relat_1(sK7)) = k1_relat_1(sK7) ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_2022,c_1436]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_12,plain,
% 3.34/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.34/0.99      | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
% 3.34/0.99      | ~ v1_relat_1(X1) ),
% 3.34/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1438,plain,
% 3.34/0.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.34/0.99      | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1) = iProver_top
% 3.34/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_6,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/0.99      | ~ r2_hidden(X2,X0)
% 3.34/0.99      | r2_hidden(X2,X1) ),
% 3.34/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1444,plain,
% 3.34/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.34/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.34/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3132,plain,
% 3.34/0.99      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top
% 3.34/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1427,c_1444]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4,plain,
% 3.34/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
% 3.34/0.99      | X2 = X0 ),
% 3.34/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1446,plain,
% 3.34/0.99      ( X0 = X1
% 3.34/0.99      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X3)) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3584,plain,
% 3.34/0.99      ( sK5 = X0 | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_3132,c_1446]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4115,plain,
% 3.34/0.99      ( sK5 = X0
% 3.34/0.99      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 3.34/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1438,c_3584]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_38,plain,
% 3.34/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1675,plain,
% 3.34/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
% 3.34/0.99      | v1_relat_1(sK7) ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1676,plain,
% 3.34/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
% 3.34/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_1675]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_5974,plain,
% 3.34/0.99      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top | sK5 = X0 ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_4115,c_38,c_1676]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_5975,plain,
% 3.34/0.99      ( sK5 = X0 | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
% 3.34/0.99      inference(renaming,[status(thm)],[c_5974]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_5988,plain,
% 3.34/0.99      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_2067,c_5975]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_6140,plain,
% 3.34/0.99      ( sK4(k1_relat_1(sK7)) = sK5 | k1_relat_1(sK7) = k1_xboole_0 ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1429,c_5988]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_6960,plain,
% 3.34/0.99      ( k1_relat_1(sK7) = k1_xboole_0
% 3.34/0.99      | r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_6140,c_1429]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_20,plain,
% 3.34/0.99      ( v5_relat_1(X0,X1)
% 3.34/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.34/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_17,plain,
% 3.34/0.99      ( ~ v5_relat_1(X0,X1)
% 3.34/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.34/0.99      | r2_hidden(k1_funct_1(X0,X2),X1)
% 3.34/0.99      | ~ v1_funct_1(X0)
% 3.34/0.99      | ~ v1_relat_1(X0) ),
% 3.34/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_35,negated_conjecture,
% 3.34/0.99      ( v1_funct_1(sK7) ),
% 3.34/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_425,plain,
% 3.34/0.99      ( ~ v5_relat_1(X0,X1)
% 3.34/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.34/0.99      | r2_hidden(k1_funct_1(X0,X2),X1)
% 3.34/0.99      | ~ v1_relat_1(X0)
% 3.34/0.99      | sK7 != X0 ),
% 3.34/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_426,plain,
% 3.34/0.99      ( ~ v5_relat_1(sK7,X0)
% 3.34/0.99      | ~ r2_hidden(X1,k1_relat_1(sK7))
% 3.34/0.99      | r2_hidden(k1_funct_1(sK7,X1),X0)
% 3.34/0.99      | ~ v1_relat_1(sK7) ),
% 3.34/0.99      inference(unflattening,[status(thm)],[c_425]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_448,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.99      | ~ r2_hidden(X3,k1_relat_1(sK7))
% 3.34/0.99      | r2_hidden(k1_funct_1(sK7,X3),X4)
% 3.34/0.99      | ~ v1_relat_1(sK7)
% 3.34/0.99      | X4 != X2
% 3.34/0.99      | sK7 != X0 ),
% 3.34/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_426]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_449,plain,
% 3.34/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.99      | ~ r2_hidden(X2,k1_relat_1(sK7))
% 3.34/0.99      | r2_hidden(k1_funct_1(sK7,X2),X1)
% 3.34/0.99      | ~ v1_relat_1(sK7) ),
% 3.34/0.99      inference(unflattening,[status(thm)],[c_448]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_461,plain,
% 3.34/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.99      | ~ r2_hidden(X2,k1_relat_1(sK7))
% 3.34/0.99      | r2_hidden(k1_funct_1(sK7,X2),X1) ),
% 3.34/0.99      inference(forward_subsumption_resolution,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_449,c_19]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1425,plain,
% 3.34/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.99      | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
% 3.34/0.99      | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1744,plain,
% 3.34/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.34/0.99      | r2_hidden(k1_funct_1(sK7,X0),sK6) = iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1427,c_1425]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_31,negated_conjecture,
% 3.34/0.99      ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
% 3.34/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1428,plain,
% 3.34/0.99      ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1751,plain,
% 3.34/0.99      ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1744,c_1428]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_6963,plain,
% 3.34/0.99      ( k1_relat_1(sK7) = k1_xboole_0 ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_6960,c_1751]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_16,plain,
% 3.34/0.99      ( ~ v1_relat_1(X0)
% 3.34/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.34/0.99      | k1_xboole_0 = X0 ),
% 3.34/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1434,plain,
% 3.34/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.34/0.99      | k1_xboole_0 = X0
% 3.34/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_6978,plain,
% 3.34/0.99      ( sK7 = k1_xboole_0 | v1_relat_1(sK7) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_6963,c_1434]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1819,plain,
% 3.34/0.99      ( ~ v1_relat_1(sK7)
% 3.34/0.99      | k1_relat_1(sK7) != k1_xboole_0
% 3.34/0.99      | k1_xboole_0 = sK7 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_968,plain,( X0 = X0 ),theory(equality) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1830,plain,
% 3.34/0.99      ( sK7 = sK7 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_968]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_969,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2455,plain,
% 3.34/0.99      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_969]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4308,plain,
% 3.34/0.99      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_2455]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4309,plain,
% 3.34/0.99      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 3.34/0.99      inference(instantiation,[status(thm)],[c_4308]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7274,plain,
% 3.34/0.99      ( sK7 = k1_xboole_0 ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_6978,c_33,c_1675,c_1751,c_1819,c_1830,c_4309,c_6960]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_30,plain,
% 3.34/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.99      | k1_xboole_0 = X2 ),
% 3.34/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_34,negated_conjecture,
% 3.34/0.99      ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
% 3.34/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_642,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.99      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 3.34/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.99      | sK6 != X2
% 3.34/0.99      | sK7 != X0
% 3.34/0.99      | k1_xboole_0 = X2 ),
% 3.34/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_643,plain,
% 3.34/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
% 3.34/0.99      | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
% 3.34/0.99      | k1_xboole_0 = sK6 ),
% 3.34/0.99      inference(unflattening,[status(thm)],[c_642]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_32,negated_conjecture,
% 3.34/0.99      ( k1_xboole_0 != sK6 ),
% 3.34/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_645,plain,
% 3.34/0.99      ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_643,c_33,c_32]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_21,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.99      | ~ r2_hidden(X3,X1)
% 3.34/0.99      | r2_hidden(k4_tarski(X3,sK2(X0,X3)),X0)
% 3.34/0.99      | k1_relset_1(X1,X2,X0) != X1 ),
% 3.34/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1432,plain,
% 3.34/0.99      ( k1_relset_1(X0,X1,X2) != X0
% 3.34/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.99      | r2_hidden(X3,X0) != iProver_top
% 3.34/0.99      | r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_3986,plain,
% 3.34/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) != iProver_top
% 3.34/0.99      | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.34/0.99      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_645,c_1432]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4612,plain,
% 3.34/0.99      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.34/0.99      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
% 3.34/0.99      inference(global_propositional_subsumption,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_3986,c_38]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7288,plain,
% 3.34/0.99      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.34/0.99      | r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.34/0.99      inference(demodulation,[status(thm)],[c_7274,c_4612]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_0,plain,
% 3.34/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.34/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_18,plain,
% 3.34/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.34/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_400,plain,
% 3.34/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.34/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_401,plain,
% 3.34/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.34/0.99      inference(unflattening,[status(thm)],[c_400]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1426,plain,
% 3.34/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7461,plain,
% 3.34/0.99      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
% 3.34/0.99      inference(forward_subsumption_resolution,
% 3.34/0.99                [status(thm)],
% 3.34/0.99                [c_7288,c_1426]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7467,plain,
% 3.34/0.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0 ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1429,c_7461]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1,plain,
% 3.34/0.99      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 3.34/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1449,plain,
% 3.34/0.99      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_7967,plain,
% 3.34/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_7467,c_1449]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_5,plain,
% 3.34/0.99      ( m1_subset_1(sK0(X0),X0) ),
% 3.34/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1445,plain,
% 3.34/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_8,plain,
% 3.34/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.34/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_1442,plain,
% 3.34/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.34/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.34/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.34/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_2419,plain,
% 3.34/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.34/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_1445,c_1442]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(c_4363,plain,
% 3.34/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.34/0.99      inference(superposition,[status(thm)],[c_2419,c_1426]) ).
% 3.34/0.99  
% 3.34/0.99  cnf(contradiction,plain,
% 3.34/0.99      ( $false ),
% 3.34/0.99      inference(minisat,[status(thm)],[c_7967,c_4363]) ).
% 3.34/0.99  
% 3.34/0.99  
% 3.34/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.99  
% 3.34/0.99  ------                               Statistics
% 3.34/0.99  
% 3.34/0.99  ------ General
% 3.34/0.99  
% 3.34/0.99  abstr_ref_over_cycles:                  0
% 3.34/0.99  abstr_ref_under_cycles:                 0
% 3.34/0.99  gc_basic_clause_elim:                   0
% 3.34/0.99  forced_gc_time:                         0
% 3.34/0.99  parsing_time:                           0.009
% 3.34/0.99  unif_index_cands_time:                  0.
% 3.34/0.99  unif_index_add_time:                    0.
% 3.34/0.99  orderings_time:                         0.
% 3.34/0.99  out_proof_time:                         0.009
% 3.34/0.99  total_time:                             0.26
% 3.34/0.99  num_of_symbols:                         57
% 3.34/0.99  num_of_terms:                           9269
% 3.34/0.99  
% 3.34/0.99  ------ Preprocessing
% 3.34/0.99  
% 3.34/0.99  num_of_splits:                          0
% 3.34/0.99  num_of_split_atoms:                     0
% 3.34/0.99  num_of_reused_defs:                     0
% 3.34/0.99  num_eq_ax_congr_red:                    42
% 3.34/0.99  num_of_sem_filtered_clauses:            1
% 3.34/0.99  num_of_subtypes:                        0
% 3.34/0.99  monotx_restored_types:                  0
% 3.34/0.99  sat_num_of_epr_types:                   0
% 3.34/0.99  sat_num_of_non_cyclic_types:            0
% 3.34/0.99  sat_guarded_non_collapsed_types:        0
% 3.34/0.99  num_pure_diseq_elim:                    0
% 3.34/0.99  simp_replaced_by:                       0
% 3.34/0.99  res_preprocessed:                       150
% 3.34/0.99  prep_upred:                             0
% 3.34/0.99  prep_unflattend:                        42
% 3.34/0.99  smt_new_axioms:                         0
% 3.34/0.99  pred_elim_cands:                        4
% 3.34/0.99  pred_elim:                              4
% 3.34/0.99  pred_elim_cl:                           7
% 3.34/0.99  pred_elim_cycles:                       9
% 3.34/0.99  merged_defs:                            0
% 3.34/0.99  merged_defs_ncl:                        0
% 3.34/0.99  bin_hyper_res:                          0
% 3.34/0.99  prep_cycles:                            4
% 3.34/0.99  pred_elim_time:                         0.008
% 3.34/0.99  splitting_time:                         0.
% 3.34/0.99  sem_filter_time:                        0.
% 3.34/0.99  monotx_time:                            0.
% 3.34/0.99  subtype_inf_time:                       0.
% 3.34/0.99  
% 3.34/0.99  ------ Problem properties
% 3.34/0.99  
% 3.34/0.99  clauses:                                29
% 3.34/0.99  conjectures:                            3
% 3.34/0.99  epr:                                    3
% 3.34/0.99  horn:                                   25
% 3.34/0.99  ground:                                 6
% 3.34/0.99  unary:                                  8
% 3.34/0.99  binary:                                 6
% 3.34/0.99  lits:                                   69
% 3.34/0.99  lits_eq:                                17
% 3.34/0.99  fd_pure:                                0
% 3.34/0.99  fd_pseudo:                              0
% 3.34/0.99  fd_cond:                                3
% 3.34/0.99  fd_pseudo_cond:                         1
% 3.34/0.99  ac_symbols:                             0
% 3.34/0.99  
% 3.34/0.99  ------ Propositional Solver
% 3.34/0.99  
% 3.34/0.99  prop_solver_calls:                      28
% 3.34/0.99  prop_fast_solver_calls:                 1037
% 3.34/0.99  smt_solver_calls:                       0
% 3.34/0.99  smt_fast_solver_calls:                  0
% 3.34/0.99  prop_num_of_clauses:                    2951
% 3.34/0.99  prop_preprocess_simplified:             8722
% 3.34/0.99  prop_fo_subsumed:                       15
% 3.34/0.99  prop_solver_time:                       0.
% 3.34/0.99  smt_solver_time:                        0.
% 3.34/0.99  smt_fast_solver_time:                   0.
% 3.34/0.99  prop_fast_solver_time:                  0.
% 3.34/0.99  prop_unsat_core_time:                   0.
% 3.34/0.99  
% 3.34/0.99  ------ QBF
% 3.34/0.99  
% 3.34/0.99  qbf_q_res:                              0
% 3.34/0.99  qbf_num_tautologies:                    0
% 3.34/0.99  qbf_prep_cycles:                        0
% 3.34/0.99  
% 3.34/0.99  ------ BMC1
% 3.34/0.99  
% 3.34/0.99  bmc1_current_bound:                     -1
% 3.34/0.99  bmc1_last_solved_bound:                 -1
% 3.34/0.99  bmc1_unsat_core_size:                   -1
% 3.34/0.99  bmc1_unsat_core_parents_size:           -1
% 3.34/0.99  bmc1_merge_next_fun:                    0
% 3.34/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.99  
% 3.34/0.99  ------ Instantiation
% 3.34/0.99  
% 3.34/0.99  inst_num_of_clauses:                    780
% 3.34/0.99  inst_num_in_passive:                    393
% 3.34/0.99  inst_num_in_active:                     337
% 3.34/0.99  inst_num_in_unprocessed:                50
% 3.34/0.99  inst_num_of_loops:                      410
% 3.34/0.99  inst_num_of_learning_restarts:          0
% 3.34/0.99  inst_num_moves_active_passive:          71
% 3.34/0.99  inst_lit_activity:                      0
% 3.34/0.99  inst_lit_activity_moves:                0
% 3.34/0.99  inst_num_tautologies:                   0
% 3.34/0.99  inst_num_prop_implied:                  0
% 3.34/0.99  inst_num_existing_simplified:           0
% 3.34/0.99  inst_num_eq_res_simplified:             0
% 3.34/0.99  inst_num_child_elim:                    0
% 3.34/0.99  inst_num_of_dismatching_blockings:      222
% 3.34/0.99  inst_num_of_non_proper_insts:           590
% 3.34/0.99  inst_num_of_duplicates:                 0
% 3.34/0.99  inst_inst_num_from_inst_to_res:         0
% 3.34/0.99  inst_dismatching_checking_time:         0.
% 3.34/0.99  
% 3.34/0.99  ------ Resolution
% 3.34/0.99  
% 3.34/0.99  res_num_of_clauses:                     0
% 3.34/0.99  res_num_in_passive:                     0
% 3.34/0.99  res_num_in_active:                      0
% 3.34/0.99  res_num_of_loops:                       154
% 3.34/0.99  res_forward_subset_subsumed:            51
% 3.34/0.99  res_backward_subset_subsumed:           0
% 3.34/0.99  res_forward_subsumed:                   0
% 3.34/0.99  res_backward_subsumed:                  0
% 3.34/0.99  res_forward_subsumption_resolution:     1
% 3.34/0.99  res_backward_subsumption_resolution:    0
% 3.34/0.99  res_clause_to_clause_subsumption:       334
% 3.34/0.99  res_orphan_elimination:                 0
% 3.34/0.99  res_tautology_del:                      83
% 3.34/0.99  res_num_eq_res_simplified:              0
% 3.34/0.99  res_num_sel_changes:                    0
% 3.34/0.99  res_moves_from_active_to_pass:          0
% 3.34/0.99  
% 3.34/0.99  ------ Superposition
% 3.34/0.99  
% 3.34/0.99  sup_time_total:                         0.
% 3.34/0.99  sup_time_generating:                    0.
% 3.34/0.99  sup_time_sim_full:                      0.
% 3.34/0.99  sup_time_sim_immed:                     0.
% 3.34/0.99  
% 3.34/0.99  sup_num_of_clauses:                     135
% 3.34/0.99  sup_num_in_active:                      43
% 3.34/0.99  sup_num_in_passive:                     92
% 3.34/0.99  sup_num_of_loops:                       81
% 3.34/0.99  sup_fw_superposition:                   71
% 3.34/0.99  sup_bw_superposition:                   86
% 3.34/0.99  sup_immediate_simplified:               24
% 3.34/0.99  sup_given_eliminated:                   2
% 3.34/0.99  comparisons_done:                       0
% 3.34/0.99  comparisons_avoided:                    3
% 3.34/0.99  
% 3.34/0.99  ------ Simplifications
% 3.34/0.99  
% 3.34/0.99  
% 3.34/0.99  sim_fw_subset_subsumed:                 14
% 3.34/0.99  sim_bw_subset_subsumed:                 15
% 3.34/0.99  sim_fw_subsumed:                        8
% 3.34/0.99  sim_bw_subsumed:                        0
% 3.34/0.99  sim_fw_subsumption_res:                 3
% 3.34/0.99  sim_bw_subsumption_res:                 0
% 3.34/0.99  sim_tautology_del:                      1
% 3.34/0.99  sim_eq_tautology_del:                   3
% 3.34/0.99  sim_eq_res_simp:                        0
% 3.34/0.99  sim_fw_demodulated:                     0
% 3.34/0.99  sim_bw_demodulated:                     41
% 3.34/0.99  sim_light_normalised:                   4
% 3.34/0.99  sim_joinable_taut:                      0
% 3.34/0.99  sim_joinable_simp:                      0
% 3.34/0.99  sim_ac_normalised:                      0
% 3.34/0.99  sim_smt_subsumption:                    0
% 3.34/0.99  
%------------------------------------------------------------------------------
