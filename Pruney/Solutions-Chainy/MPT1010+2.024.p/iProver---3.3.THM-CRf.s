%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:06 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 176 expanded)
%              Number of clauses        :   45 (  48 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   19
%              Number of atoms          :  372 ( 707 expanded)
%              Number of equality atoms :  185 ( 324 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK5,sK4) != sK3
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_funct_1(sK5,sK4) != sK3
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f40])).

fof(f73,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f82,plain,(
    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f71,f75])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f84,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f83])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f74,plain,(
    k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2695,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_enumset1(sK3,sK3,sK3) != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_446,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
    | k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_448,plain,
    ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_28])).

cnf(c_2694,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2696,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3437,plain,
    ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2694,c_2696])).

cnf(c_3439,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k1_xboole_0
    | k1_relat_1(sK5) = sK2 ),
    inference(superposition,[status(thm)],[c_448,c_3437])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_330,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_855,plain,
    ( X0 != X1
    | k1_enumset1(X2,X3,X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_331])).

cnf(c_856,plain,
    ( k1_enumset1(X0,X1,X2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_3688,plain,
    ( k1_relat_1(sK5) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3439,c_856])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_353,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_354,plain,
    ( ~ v5_relat_1(sK5,X0)
    | m1_subset_1(k1_funct_1(sK5,X1),X0)
    | ~ r2_hidden(X1,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(sK5,X3),X4)
    | ~ r2_hidden(X3,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | X4 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_354])).

cnf(c_377,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_389,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_377,c_17])).

cnf(c_2692,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_2911,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2694,c_2692])).

cnf(c_3690,plain,
    ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3688,c_2911])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2697,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4067,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | v1_xboole_0(k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3690,c_2697])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2698,plain,
    ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4885,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4067,c_2698])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2703,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4889,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4885,c_2703])).

cnf(c_4898,plain,
    ( k1_funct_1(sK5,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_2695,c_4889])).

cnf(c_26,negated_conjecture,
    ( k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4898,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:22:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.85/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.98  
% 2.85/0.98  ------  iProver source info
% 2.85/0.98  
% 2.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.98  git: non_committed_changes: false
% 2.85/0.98  git: last_make_outside_of_git: false
% 2.85/0.98  
% 2.85/0.98  ------ 
% 2.85/0.98  
% 2.85/0.98  ------ Input Options
% 2.85/0.98  
% 2.85/0.98  --out_options                           all
% 2.85/0.98  --tptp_safe_out                         true
% 2.85/0.98  --problem_path                          ""
% 2.85/0.98  --include_path                          ""
% 2.85/0.98  --clausifier                            res/vclausify_rel
% 2.85/0.98  --clausifier_options                    --mode clausify
% 2.85/0.98  --stdin                                 false
% 2.85/0.98  --stats_out                             all
% 2.85/0.98  
% 2.85/0.98  ------ General Options
% 2.85/0.98  
% 2.85/0.98  --fof                                   false
% 2.85/0.98  --time_out_real                         305.
% 2.85/0.98  --time_out_virtual                      -1.
% 2.85/0.98  --symbol_type_check                     false
% 2.85/0.98  --clausify_out                          false
% 2.85/0.98  --sig_cnt_out                           false
% 2.85/0.98  --trig_cnt_out                          false
% 2.85/0.98  --trig_cnt_out_tolerance                1.
% 2.85/0.98  --trig_cnt_out_sk_spl                   false
% 2.85/0.98  --abstr_cl_out                          false
% 2.85/0.98  
% 2.85/0.98  ------ Global Options
% 2.85/0.98  
% 2.85/0.98  --schedule                              default
% 2.85/0.98  --add_important_lit                     false
% 2.85/0.98  --prop_solver_per_cl                    1000
% 2.85/0.98  --min_unsat_core                        false
% 2.85/0.98  --soft_assumptions                      false
% 2.85/0.98  --soft_lemma_size                       3
% 2.85/0.98  --prop_impl_unit_size                   0
% 2.85/0.98  --prop_impl_unit                        []
% 2.85/0.98  --share_sel_clauses                     true
% 2.85/0.98  --reset_solvers                         false
% 2.85/0.98  --bc_imp_inh                            [conj_cone]
% 2.85/0.98  --conj_cone_tolerance                   3.
% 2.85/0.98  --extra_neg_conj                        none
% 2.85/0.98  --large_theory_mode                     true
% 2.85/0.98  --prolific_symb_bound                   200
% 2.85/0.98  --lt_threshold                          2000
% 2.85/0.98  --clause_weak_htbl                      true
% 2.85/0.98  --gc_record_bc_elim                     false
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing Options
% 2.85/0.98  
% 2.85/0.98  --preprocessing_flag                    true
% 2.85/0.98  --time_out_prep_mult                    0.1
% 2.85/0.98  --splitting_mode                        input
% 2.85/0.98  --splitting_grd                         true
% 2.85/0.98  --splitting_cvd                         false
% 2.85/0.98  --splitting_cvd_svl                     false
% 2.85/0.98  --splitting_nvd                         32
% 2.85/0.98  --sub_typing                            true
% 2.85/0.98  --prep_gs_sim                           true
% 2.85/0.98  --prep_unflatten                        true
% 2.85/0.98  --prep_res_sim                          true
% 2.85/0.98  --prep_upred                            true
% 2.85/0.98  --prep_sem_filter                       exhaustive
% 2.85/0.98  --prep_sem_filter_out                   false
% 2.85/0.98  --pred_elim                             true
% 2.85/0.98  --res_sim_input                         true
% 2.85/0.98  --eq_ax_congr_red                       true
% 2.85/0.98  --pure_diseq_elim                       true
% 2.85/0.98  --brand_transform                       false
% 2.85/0.98  --non_eq_to_eq                          false
% 2.85/0.98  --prep_def_merge                        true
% 2.85/0.98  --prep_def_merge_prop_impl              false
% 2.85/0.98  --prep_def_merge_mbd                    true
% 2.85/0.98  --prep_def_merge_tr_red                 false
% 2.85/0.98  --prep_def_merge_tr_cl                  false
% 2.85/0.98  --smt_preprocessing                     true
% 2.85/0.98  --smt_ac_axioms                         fast
% 2.85/0.98  --preprocessed_out                      false
% 2.85/0.98  --preprocessed_stats                    false
% 2.85/0.98  
% 2.85/0.98  ------ Abstraction refinement Options
% 2.85/0.98  
% 2.85/0.98  --abstr_ref                             []
% 2.85/0.98  --abstr_ref_prep                        false
% 2.85/0.98  --abstr_ref_until_sat                   false
% 2.85/0.98  --abstr_ref_sig_restrict                funpre
% 2.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.98  --abstr_ref_under                       []
% 2.85/0.98  
% 2.85/0.98  ------ SAT Options
% 2.85/0.98  
% 2.85/0.98  --sat_mode                              false
% 2.85/0.98  --sat_fm_restart_options                ""
% 2.85/0.98  --sat_gr_def                            false
% 2.85/0.98  --sat_epr_types                         true
% 2.85/0.98  --sat_non_cyclic_types                  false
% 2.85/0.98  --sat_finite_models                     false
% 2.85/0.98  --sat_fm_lemmas                         false
% 2.85/0.98  --sat_fm_prep                           false
% 2.85/0.98  --sat_fm_uc_incr                        true
% 2.85/0.98  --sat_out_model                         small
% 2.85/0.98  --sat_out_clauses                       false
% 2.85/0.98  
% 2.85/0.98  ------ QBF Options
% 2.85/0.98  
% 2.85/0.98  --qbf_mode                              false
% 2.85/0.98  --qbf_elim_univ                         false
% 2.85/0.98  --qbf_dom_inst                          none
% 2.85/0.98  --qbf_dom_pre_inst                      false
% 2.85/0.98  --qbf_sk_in                             false
% 2.85/0.98  --qbf_pred_elim                         true
% 2.85/0.98  --qbf_split                             512
% 2.85/0.98  
% 2.85/0.98  ------ BMC1 Options
% 2.85/0.98  
% 2.85/0.98  --bmc1_incremental                      false
% 2.85/0.98  --bmc1_axioms                           reachable_all
% 2.85/0.98  --bmc1_min_bound                        0
% 2.85/0.98  --bmc1_max_bound                        -1
% 2.85/0.98  --bmc1_max_bound_default                -1
% 2.85/0.98  --bmc1_symbol_reachability              true
% 2.85/0.98  --bmc1_property_lemmas                  false
% 2.85/0.98  --bmc1_k_induction                      false
% 2.85/0.98  --bmc1_non_equiv_states                 false
% 2.85/0.98  --bmc1_deadlock                         false
% 2.85/0.98  --bmc1_ucm                              false
% 2.85/0.98  --bmc1_add_unsat_core                   none
% 2.85/0.98  --bmc1_unsat_core_children              false
% 2.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.98  --bmc1_out_stat                         full
% 2.85/0.98  --bmc1_ground_init                      false
% 2.85/0.98  --bmc1_pre_inst_next_state              false
% 2.85/0.98  --bmc1_pre_inst_state                   false
% 2.85/0.98  --bmc1_pre_inst_reach_state             false
% 2.85/0.98  --bmc1_out_unsat_core                   false
% 2.85/0.98  --bmc1_aig_witness_out                  false
% 2.85/0.98  --bmc1_verbose                          false
% 2.85/0.98  --bmc1_dump_clauses_tptp                false
% 2.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.98  --bmc1_dump_file                        -
% 2.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.98  --bmc1_ucm_extend_mode                  1
% 2.85/0.98  --bmc1_ucm_init_mode                    2
% 2.85/0.98  --bmc1_ucm_cone_mode                    none
% 2.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.98  --bmc1_ucm_relax_model                  4
% 2.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.98  --bmc1_ucm_layered_model                none
% 2.85/0.99  --bmc1_ucm_max_lemma_size               10
% 2.85/0.99  
% 2.85/0.99  ------ AIG Options
% 2.85/0.99  
% 2.85/0.99  --aig_mode                              false
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation Options
% 2.85/0.99  
% 2.85/0.99  --instantiation_flag                    true
% 2.85/0.99  --inst_sos_flag                         false
% 2.85/0.99  --inst_sos_phase                        true
% 2.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel_side                     num_symb
% 2.85/0.99  --inst_solver_per_active                1400
% 2.85/0.99  --inst_solver_calls_frac                1.
% 2.85/0.99  --inst_passive_queue_type               priority_queues
% 2.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.99  --inst_passive_queues_freq              [25;2]
% 2.85/0.99  --inst_dismatching                      true
% 2.85/0.99  --inst_eager_unprocessed_to_passive     true
% 2.85/0.99  --inst_prop_sim_given                   true
% 2.85/0.99  --inst_prop_sim_new                     false
% 2.85/0.99  --inst_subs_new                         false
% 2.85/0.99  --inst_eq_res_simp                      false
% 2.85/0.99  --inst_subs_given                       false
% 2.85/0.99  --inst_orphan_elimination               true
% 2.85/0.99  --inst_learning_loop_flag               true
% 2.85/0.99  --inst_learning_start                   3000
% 2.85/0.99  --inst_learning_factor                  2
% 2.85/0.99  --inst_start_prop_sim_after_learn       3
% 2.85/0.99  --inst_sel_renew                        solver
% 2.85/0.99  --inst_lit_activity_flag                true
% 2.85/0.99  --inst_restr_to_given                   false
% 2.85/0.99  --inst_activity_threshold               500
% 2.85/0.99  --inst_out_proof                        true
% 2.85/0.99  
% 2.85/0.99  ------ Resolution Options
% 2.85/0.99  
% 2.85/0.99  --resolution_flag                       true
% 2.85/0.99  --res_lit_sel                           adaptive
% 2.85/0.99  --res_lit_sel_side                      none
% 2.85/0.99  --res_ordering                          kbo
% 2.85/0.99  --res_to_prop_solver                    active
% 2.85/0.99  --res_prop_simpl_new                    false
% 2.85/0.99  --res_prop_simpl_given                  true
% 2.85/0.99  --res_passive_queue_type                priority_queues
% 2.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.99  --res_passive_queues_freq               [15;5]
% 2.85/0.99  --res_forward_subs                      full
% 2.85/0.99  --res_backward_subs                     full
% 2.85/0.99  --res_forward_subs_resolution           true
% 2.85/0.99  --res_backward_subs_resolution          true
% 2.85/0.99  --res_orphan_elimination                true
% 2.85/0.99  --res_time_limit                        2.
% 2.85/0.99  --res_out_proof                         true
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Options
% 2.85/0.99  
% 2.85/0.99  --superposition_flag                    true
% 2.85/0.99  --sup_passive_queue_type                priority_queues
% 2.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.99  --demod_completeness_check              fast
% 2.85/0.99  --demod_use_ground                      true
% 2.85/0.99  --sup_to_prop_solver                    passive
% 2.85/0.99  --sup_prop_simpl_new                    true
% 2.85/0.99  --sup_prop_simpl_given                  true
% 2.85/0.99  --sup_fun_splitting                     false
% 2.85/0.99  --sup_smt_interval                      50000
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Simplification Setup
% 2.85/0.99  
% 2.85/0.99  --sup_indices_passive                   []
% 2.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_full_bw                           [BwDemod]
% 2.85/0.99  --sup_immed_triv                        [TrivRules]
% 2.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_immed_bw_main                     []
% 2.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  
% 2.85/0.99  ------ Combination Options
% 2.85/0.99  
% 2.85/0.99  --comb_res_mult                         3
% 2.85/0.99  --comb_sup_mult                         2
% 2.85/0.99  --comb_inst_mult                        10
% 2.85/0.99  
% 2.85/0.99  ------ Debug Options
% 2.85/0.99  
% 2.85/0.99  --dbg_backtrace                         false
% 2.85/0.99  --dbg_dump_prop_clauses                 false
% 2.85/0.99  --dbg_dump_prop_clauses_file            -
% 2.85/0.99  --dbg_out_stat                          false
% 2.85/0.99  ------ Parsing...
% 2.85/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.99  ------ Proving...
% 2.85/0.99  ------ Problem Properties 
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  clauses                                 23
% 2.85/0.99  conjectures                             3
% 2.85/0.99  EPR                                     4
% 2.85/0.99  Horn                                    18
% 2.85/0.99  unary                                   11
% 2.85/0.99  binary                                  3
% 2.85/0.99  lits                                    47
% 2.85/0.99  lits eq                                 24
% 2.85/0.99  fd_pure                                 0
% 2.85/0.99  fd_pseudo                               0
% 2.85/0.99  fd_cond                                 0
% 2.85/0.99  fd_pseudo_cond                          6
% 2.85/0.99  AC symbols                              0
% 2.85/0.99  
% 2.85/0.99  ------ Schedule dynamic 5 is on 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ 
% 2.85/0.99  Current options:
% 2.85/0.99  ------ 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options
% 2.85/0.99  
% 2.85/0.99  --out_options                           all
% 2.85/0.99  --tptp_safe_out                         true
% 2.85/0.99  --problem_path                          ""
% 2.85/0.99  --include_path                          ""
% 2.85/0.99  --clausifier                            res/vclausify_rel
% 2.85/0.99  --clausifier_options                    --mode clausify
% 2.85/0.99  --stdin                                 false
% 2.85/0.99  --stats_out                             all
% 2.85/0.99  
% 2.85/0.99  ------ General Options
% 2.85/0.99  
% 2.85/0.99  --fof                                   false
% 2.85/0.99  --time_out_real                         305.
% 2.85/0.99  --time_out_virtual                      -1.
% 2.85/0.99  --symbol_type_check                     false
% 2.85/0.99  --clausify_out                          false
% 2.85/0.99  --sig_cnt_out                           false
% 2.85/0.99  --trig_cnt_out                          false
% 2.85/0.99  --trig_cnt_out_tolerance                1.
% 2.85/0.99  --trig_cnt_out_sk_spl                   false
% 2.85/0.99  --abstr_cl_out                          false
% 2.85/0.99  
% 2.85/0.99  ------ Global Options
% 2.85/0.99  
% 2.85/0.99  --schedule                              default
% 2.85/0.99  --add_important_lit                     false
% 2.85/0.99  --prop_solver_per_cl                    1000
% 2.85/0.99  --min_unsat_core                        false
% 2.85/0.99  --soft_assumptions                      false
% 2.85/0.99  --soft_lemma_size                       3
% 2.85/0.99  --prop_impl_unit_size                   0
% 2.85/0.99  --prop_impl_unit                        []
% 2.85/0.99  --share_sel_clauses                     true
% 2.85/0.99  --reset_solvers                         false
% 2.85/0.99  --bc_imp_inh                            [conj_cone]
% 2.85/0.99  --conj_cone_tolerance                   3.
% 2.85/0.99  --extra_neg_conj                        none
% 2.85/0.99  --large_theory_mode                     true
% 2.85/0.99  --prolific_symb_bound                   200
% 2.85/0.99  --lt_threshold                          2000
% 2.85/0.99  --clause_weak_htbl                      true
% 2.85/0.99  --gc_record_bc_elim                     false
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing Options
% 2.85/0.99  
% 2.85/0.99  --preprocessing_flag                    true
% 2.85/0.99  --time_out_prep_mult                    0.1
% 2.85/0.99  --splitting_mode                        input
% 2.85/0.99  --splitting_grd                         true
% 2.85/0.99  --splitting_cvd                         false
% 2.85/0.99  --splitting_cvd_svl                     false
% 2.85/0.99  --splitting_nvd                         32
% 2.85/0.99  --sub_typing                            true
% 2.85/0.99  --prep_gs_sim                           true
% 2.85/0.99  --prep_unflatten                        true
% 2.85/0.99  --prep_res_sim                          true
% 2.85/0.99  --prep_upred                            true
% 2.85/0.99  --prep_sem_filter                       exhaustive
% 2.85/0.99  --prep_sem_filter_out                   false
% 2.85/0.99  --pred_elim                             true
% 2.85/0.99  --res_sim_input                         true
% 2.85/0.99  --eq_ax_congr_red                       true
% 2.85/0.99  --pure_diseq_elim                       true
% 2.85/0.99  --brand_transform                       false
% 2.85/0.99  --non_eq_to_eq                          false
% 2.85/0.99  --prep_def_merge                        true
% 2.85/0.99  --prep_def_merge_prop_impl              false
% 2.85/0.99  --prep_def_merge_mbd                    true
% 2.85/0.99  --prep_def_merge_tr_red                 false
% 2.85/0.99  --prep_def_merge_tr_cl                  false
% 2.85/0.99  --smt_preprocessing                     true
% 2.85/0.99  --smt_ac_axioms                         fast
% 2.85/0.99  --preprocessed_out                      false
% 2.85/0.99  --preprocessed_stats                    false
% 2.85/0.99  
% 2.85/0.99  ------ Abstraction refinement Options
% 2.85/0.99  
% 2.85/0.99  --abstr_ref                             []
% 2.85/0.99  --abstr_ref_prep                        false
% 2.85/0.99  --abstr_ref_until_sat                   false
% 2.85/0.99  --abstr_ref_sig_restrict                funpre
% 2.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.99  --abstr_ref_under                       []
% 2.85/0.99  
% 2.85/0.99  ------ SAT Options
% 2.85/0.99  
% 2.85/0.99  --sat_mode                              false
% 2.85/0.99  --sat_fm_restart_options                ""
% 2.85/0.99  --sat_gr_def                            false
% 2.85/0.99  --sat_epr_types                         true
% 2.85/0.99  --sat_non_cyclic_types                  false
% 2.85/0.99  --sat_finite_models                     false
% 2.85/0.99  --sat_fm_lemmas                         false
% 2.85/0.99  --sat_fm_prep                           false
% 2.85/0.99  --sat_fm_uc_incr                        true
% 2.85/0.99  --sat_out_model                         small
% 2.85/0.99  --sat_out_clauses                       false
% 2.85/0.99  
% 2.85/0.99  ------ QBF Options
% 2.85/0.99  
% 2.85/0.99  --qbf_mode                              false
% 2.85/0.99  --qbf_elim_univ                         false
% 2.85/0.99  --qbf_dom_inst                          none
% 2.85/0.99  --qbf_dom_pre_inst                      false
% 2.85/0.99  --qbf_sk_in                             false
% 2.85/0.99  --qbf_pred_elim                         true
% 2.85/0.99  --qbf_split                             512
% 2.85/0.99  
% 2.85/0.99  ------ BMC1 Options
% 2.85/0.99  
% 2.85/0.99  --bmc1_incremental                      false
% 2.85/0.99  --bmc1_axioms                           reachable_all
% 2.85/0.99  --bmc1_min_bound                        0
% 2.85/0.99  --bmc1_max_bound                        -1
% 2.85/0.99  --bmc1_max_bound_default                -1
% 2.85/0.99  --bmc1_symbol_reachability              true
% 2.85/0.99  --bmc1_property_lemmas                  false
% 2.85/0.99  --bmc1_k_induction                      false
% 2.85/0.99  --bmc1_non_equiv_states                 false
% 2.85/0.99  --bmc1_deadlock                         false
% 2.85/0.99  --bmc1_ucm                              false
% 2.85/0.99  --bmc1_add_unsat_core                   none
% 2.85/0.99  --bmc1_unsat_core_children              false
% 2.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.99  --bmc1_out_stat                         full
% 2.85/0.99  --bmc1_ground_init                      false
% 2.85/0.99  --bmc1_pre_inst_next_state              false
% 2.85/0.99  --bmc1_pre_inst_state                   false
% 2.85/0.99  --bmc1_pre_inst_reach_state             false
% 2.85/0.99  --bmc1_out_unsat_core                   false
% 2.85/0.99  --bmc1_aig_witness_out                  false
% 2.85/0.99  --bmc1_verbose                          false
% 2.85/0.99  --bmc1_dump_clauses_tptp                false
% 2.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.99  --bmc1_dump_file                        -
% 2.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.99  --bmc1_ucm_extend_mode                  1
% 2.85/0.99  --bmc1_ucm_init_mode                    2
% 2.85/0.99  --bmc1_ucm_cone_mode                    none
% 2.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.99  --bmc1_ucm_relax_model                  4
% 2.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.99  --bmc1_ucm_layered_model                none
% 2.85/0.99  --bmc1_ucm_max_lemma_size               10
% 2.85/0.99  
% 2.85/0.99  ------ AIG Options
% 2.85/0.99  
% 2.85/0.99  --aig_mode                              false
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation Options
% 2.85/0.99  
% 2.85/0.99  --instantiation_flag                    true
% 2.85/0.99  --inst_sos_flag                         false
% 2.85/0.99  --inst_sos_phase                        true
% 2.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel_side                     none
% 2.85/0.99  --inst_solver_per_active                1400
% 2.85/0.99  --inst_solver_calls_frac                1.
% 2.85/0.99  --inst_passive_queue_type               priority_queues
% 2.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.99  --inst_passive_queues_freq              [25;2]
% 2.85/0.99  --inst_dismatching                      true
% 2.85/0.99  --inst_eager_unprocessed_to_passive     true
% 2.85/0.99  --inst_prop_sim_given                   true
% 2.85/0.99  --inst_prop_sim_new                     false
% 2.85/0.99  --inst_subs_new                         false
% 2.85/0.99  --inst_eq_res_simp                      false
% 2.85/0.99  --inst_subs_given                       false
% 2.85/0.99  --inst_orphan_elimination               true
% 2.85/0.99  --inst_learning_loop_flag               true
% 2.85/0.99  --inst_learning_start                   3000
% 2.85/0.99  --inst_learning_factor                  2
% 2.85/0.99  --inst_start_prop_sim_after_learn       3
% 2.85/0.99  --inst_sel_renew                        solver
% 2.85/0.99  --inst_lit_activity_flag                true
% 2.85/0.99  --inst_restr_to_given                   false
% 2.85/0.99  --inst_activity_threshold               500
% 2.85/0.99  --inst_out_proof                        true
% 2.85/0.99  
% 2.85/0.99  ------ Resolution Options
% 2.85/0.99  
% 2.85/0.99  --resolution_flag                       false
% 2.85/0.99  --res_lit_sel                           adaptive
% 2.85/0.99  --res_lit_sel_side                      none
% 2.85/0.99  --res_ordering                          kbo
% 2.85/0.99  --res_to_prop_solver                    active
% 2.85/0.99  --res_prop_simpl_new                    false
% 2.85/0.99  --res_prop_simpl_given                  true
% 2.85/0.99  --res_passive_queue_type                priority_queues
% 2.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.99  --res_passive_queues_freq               [15;5]
% 2.85/0.99  --res_forward_subs                      full
% 2.85/0.99  --res_backward_subs                     full
% 2.85/0.99  --res_forward_subs_resolution           true
% 2.85/0.99  --res_backward_subs_resolution          true
% 2.85/0.99  --res_orphan_elimination                true
% 2.85/0.99  --res_time_limit                        2.
% 2.85/0.99  --res_out_proof                         true
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Options
% 2.85/0.99  
% 2.85/0.99  --superposition_flag                    true
% 2.85/0.99  --sup_passive_queue_type                priority_queues
% 2.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.99  --demod_completeness_check              fast
% 2.85/0.99  --demod_use_ground                      true
% 2.85/0.99  --sup_to_prop_solver                    passive
% 2.85/0.99  --sup_prop_simpl_new                    true
% 2.85/0.99  --sup_prop_simpl_given                  true
% 2.85/0.99  --sup_fun_splitting                     false
% 2.85/0.99  --sup_smt_interval                      50000
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Simplification Setup
% 2.85/0.99  
% 2.85/0.99  --sup_indices_passive                   []
% 2.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_full_bw                           [BwDemod]
% 2.85/0.99  --sup_immed_triv                        [TrivRules]
% 2.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_immed_bw_main                     []
% 2.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  
% 2.85/0.99  ------ Combination Options
% 2.85/0.99  
% 2.85/0.99  --comb_res_mult                         3
% 2.85/0.99  --comb_sup_mult                         2
% 2.85/0.99  --comb_inst_mult                        10
% 2.85/0.99  
% 2.85/0.99  ------ Debug Options
% 2.85/0.99  
% 2.85/0.99  --dbg_backtrace                         false
% 2.85/0.99  --dbg_dump_prop_clauses                 false
% 2.85/0.99  --dbg_dump_prop_clauses_file            -
% 2.85/0.99  --dbg_out_stat                          false
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ Proving...
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  % SZS status Theorem for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  fof(f14,conjecture,(
% 2.85/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f15,negated_conjecture,(
% 2.85/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.85/0.99    inference(negated_conjecture,[],[f14])).
% 2.85/0.99  
% 2.85/0.99  fof(f28,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.85/0.99    inference(ennf_transformation,[],[f15])).
% 2.85/0.99  
% 2.85/0.99  fof(f29,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.85/0.99    inference(flattening,[],[f28])).
% 2.85/0.99  
% 2.85/0.99  fof(f40,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f41,plain,(
% 2.85/0.99    k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f40])).
% 2.85/0.99  
% 2.85/0.99  fof(f73,plain,(
% 2.85/0.99    r2_hidden(sK4,sK2)),
% 2.85/0.99    inference(cnf_transformation,[],[f41])).
% 2.85/0.99  
% 2.85/0.99  fof(f13,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f26,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f13])).
% 2.85/0.99  
% 2.85/0.99  fof(f27,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(flattening,[],[f26])).
% 2.85/0.99  
% 2.85/0.99  fof(f39,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(nnf_transformation,[],[f27])).
% 2.85/0.99  
% 2.85/0.99  fof(f64,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f39])).
% 2.85/0.99  
% 2.85/0.99  fof(f71,plain,(
% 2.85/0.99    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 2.85/0.99    inference(cnf_transformation,[],[f41])).
% 2.85/0.99  
% 2.85/0.99  fof(f4,axiom,(
% 2.85/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f55,plain,(
% 2.85/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f4])).
% 2.85/0.99  
% 2.85/0.99  fof(f5,axiom,(
% 2.85/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f56,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f5])).
% 2.85/0.99  
% 2.85/0.99  fof(f75,plain,(
% 2.85/0.99    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 2.85/0.99    inference(definition_unfolding,[],[f55,f56])).
% 2.85/0.99  
% 2.85/0.99  fof(f82,plain,(
% 2.85/0.99    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3))),
% 2.85/0.99    inference(definition_unfolding,[],[f71,f75])).
% 2.85/0.99  
% 2.85/0.99  fof(f72,plain,(
% 2.85/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 2.85/0.99    inference(cnf_transformation,[],[f41])).
% 2.85/0.99  
% 2.85/0.99  fof(f81,plain,(
% 2.85/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))),
% 2.85/0.99    inference(definition_unfolding,[],[f72,f75])).
% 2.85/0.99  
% 2.85/0.99  fof(f12,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f25,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f12])).
% 2.85/0.99  
% 2.85/0.99  fof(f63,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f25])).
% 2.85/0.99  
% 2.85/0.99  fof(f2,axiom,(
% 2.85/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f17,plain,(
% 2.85/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.85/0.99    inference(ennf_transformation,[],[f2])).
% 2.85/0.99  
% 2.85/0.99  fof(f30,plain,(
% 2.85/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.85/0.99    inference(nnf_transformation,[],[f17])).
% 2.85/0.99  
% 2.85/0.99  fof(f31,plain,(
% 2.85/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.85/0.99    inference(flattening,[],[f30])).
% 2.85/0.99  
% 2.85/0.99  fof(f32,plain,(
% 2.85/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.85/0.99    inference(rectify,[],[f31])).
% 2.85/0.99  
% 2.85/0.99  fof(f33,plain,(
% 2.85/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f34,plain,(
% 2.85/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f46,plain,(
% 2.85/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.85/0.99    inference(cnf_transformation,[],[f34])).
% 2.85/0.99  
% 2.85/0.99  fof(f83,plain,(
% 2.85/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 2.85/0.99    inference(equality_resolution,[],[f46])).
% 2.85/0.99  
% 2.85/0.99  fof(f84,plain,(
% 2.85/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 2.85/0.99    inference(equality_resolution,[],[f83])).
% 2.85/0.99  
% 2.85/0.99  fof(f1,axiom,(
% 2.85/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f42,plain,(
% 2.85/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f1])).
% 2.85/0.99  
% 2.85/0.99  fof(f9,axiom,(
% 2.85/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f22,plain,(
% 2.85/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.85/0.99    inference(ennf_transformation,[],[f9])).
% 2.85/0.99  
% 2.85/0.99  fof(f60,plain,(
% 2.85/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f22])).
% 2.85/0.99  
% 2.85/0.99  fof(f11,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f16,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.85/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.85/0.99  
% 2.85/0.99  fof(f24,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f16])).
% 2.85/0.99  
% 2.85/0.99  fof(f62,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f24])).
% 2.85/0.99  
% 2.85/0.99  fof(f8,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f20,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.85/0.99    inference(ennf_transformation,[],[f8])).
% 2.85/0.99  
% 2.85/0.99  fof(f21,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.85/0.99    inference(flattening,[],[f20])).
% 2.85/0.99  
% 2.85/0.99  fof(f59,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f21])).
% 2.85/0.99  
% 2.85/0.99  fof(f70,plain,(
% 2.85/0.99    v1_funct_1(sK5)),
% 2.85/0.99    inference(cnf_transformation,[],[f41])).
% 2.85/0.99  
% 2.85/0.99  fof(f10,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f23,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f10])).
% 2.85/0.99  
% 2.85/0.99  fof(f61,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f23])).
% 2.85/0.99  
% 2.85/0.99  fof(f7,axiom,(
% 2.85/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f18,plain,(
% 2.85/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.85/0.99    inference(ennf_transformation,[],[f7])).
% 2.85/0.99  
% 2.85/0.99  fof(f19,plain,(
% 2.85/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.85/0.99    inference(flattening,[],[f18])).
% 2.85/0.99  
% 2.85/0.99  fof(f58,plain,(
% 2.85/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f19])).
% 2.85/0.99  
% 2.85/0.99  fof(f6,axiom,(
% 2.85/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f57,plain,(
% 2.85/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f6])).
% 2.85/0.99  
% 2.85/0.99  fof(f80,plain,(
% 2.85/0.99    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 2.85/0.99    inference(definition_unfolding,[],[f57,f75])).
% 2.85/0.99  
% 2.85/0.99  fof(f43,plain,(
% 2.85/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.85/0.99    inference(cnf_transformation,[],[f34])).
% 2.85/0.99  
% 2.85/0.99  fof(f89,plain,(
% 2.85/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 2.85/0.99    inference(equality_resolution,[],[f43])).
% 2.85/0.99  
% 2.85/0.99  fof(f74,plain,(
% 2.85/0.99    k1_funct_1(sK5,sK4) != sK3),
% 2.85/0.99    inference(cnf_transformation,[],[f41])).
% 2.85/0.99  
% 2.85/0.99  cnf(c_27,negated_conjecture,
% 2.85/0.99      ( r2_hidden(sK4,sK2) ),
% 2.85/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2695,plain,
% 2.85/0.99      ( r2_hidden(sK4,sK2) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_25,plain,
% 2.85/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.99      | k1_xboole_0 = X2 ),
% 2.85/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_29,negated_conjecture,
% 2.85/0.99      ( v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_445,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.99      | k1_enumset1(sK3,sK3,sK3) != X2
% 2.85/0.99      | sK2 != X1
% 2.85/0.99      | sK5 != X0
% 2.85/0.99      | k1_xboole_0 = X2 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_446,plain,
% 2.85/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
% 2.85/0.99      | k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
% 2.85/0.99      | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_28,negated_conjecture,
% 2.85/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
% 2.85/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_448,plain,
% 2.85/0.99      ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
% 2.85/0.99      | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_446,c_28]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2694,plain,
% 2.85/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_19,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2696,plain,
% 2.85/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.85/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3437,plain,
% 2.85/0.99      ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_2694,c_2696]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3439,plain,
% 2.85/0.99      ( k1_enumset1(sK3,sK3,sK3) = k1_xboole_0 | k1_relat_1(sK5) = sK2 ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_448,c_3437]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_5,plain,
% 2.85/0.99      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_0,plain,
% 2.85/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_16,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_330,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_331,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_330]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_855,plain,
% 2.85/0.99      ( X0 != X1 | k1_enumset1(X2,X3,X1) != k1_xboole_0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_331]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_856,plain,
% 2.85/0.99      ( k1_enumset1(X0,X1,X2) != k1_xboole_0 ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_855]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3688,plain,
% 2.85/0.99      ( k1_relat_1(sK5) = sK2 ),
% 2.85/0.99      inference(forward_subsumption_resolution,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_3439,c_856]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_18,plain,
% 2.85/0.99      ( v5_relat_1(X0,X1)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.85/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_15,plain,
% 2.85/0.99      ( ~ v5_relat_1(X0,X1)
% 2.85/0.99      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.85/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.85/0.99      | ~ v1_relat_1(X0)
% 2.85/0.99      | ~ v1_funct_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_30,negated_conjecture,
% 2.85/0.99      ( v1_funct_1(sK5) ),
% 2.85/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_353,plain,
% 2.85/0.99      ( ~ v5_relat_1(X0,X1)
% 2.85/0.99      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.85/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.85/0.99      | ~ v1_relat_1(X0)
% 2.85/0.99      | sK5 != X0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_354,plain,
% 2.85/0.99      ( ~ v5_relat_1(sK5,X0)
% 2.85/0.99      | m1_subset_1(k1_funct_1(sK5,X1),X0)
% 2.85/0.99      | ~ r2_hidden(X1,k1_relat_1(sK5))
% 2.85/0.99      | ~ v1_relat_1(sK5) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_376,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | m1_subset_1(k1_funct_1(sK5,X3),X4)
% 2.85/0.99      | ~ r2_hidden(X3,k1_relat_1(sK5))
% 2.85/0.99      | ~ v1_relat_1(sK5)
% 2.85/0.99      | X4 != X2
% 2.85/0.99      | sK5 != X0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_354]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_377,plain,
% 2.85/0.99      ( m1_subset_1(k1_funct_1(sK5,X0),X1)
% 2.85/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.85/0.99      | ~ r2_hidden(X0,k1_relat_1(sK5))
% 2.85/0.99      | ~ v1_relat_1(sK5) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_376]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_17,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | v1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_389,plain,
% 2.85/0.99      ( m1_subset_1(k1_funct_1(sK5,X0),X1)
% 2.85/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.85/0.99      | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
% 2.85/0.99      inference(forward_subsumption_resolution,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_377,c_17]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2692,plain,
% 2.85/0.99      ( m1_subset_1(k1_funct_1(sK5,X0),X1) = iProver_top
% 2.85/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.85/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2911,plain,
% 2.85/0.99      ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 2.85/0.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_2694,c_2692]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3690,plain,
% 2.85/0.99      ( m1_subset_1(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 2.85/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 2.85/0.99      inference(demodulation,[status(thm)],[c_3688,c_2911]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_14,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.85/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2697,plain,
% 2.85/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.85/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.85/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4067,plain,
% 2.85/0.99      ( r2_hidden(X0,sK2) != iProver_top
% 2.85/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 2.85/0.99      | v1_xboole_0(k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_3690,c_2697]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_13,plain,
% 2.85/0.99      ( ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2698,plain,
% 2.85/0.99      ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4885,plain,
% 2.85/0.99      ( r2_hidden(X0,sK2) != iProver_top
% 2.85/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 2.85/0.99      inference(forward_subsumption_resolution,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_4067,c_2698]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_8,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 2.85/0.99      | X0 = X1
% 2.85/0.99      | X0 = X2
% 2.85/0.99      | X0 = X3 ),
% 2.85/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2703,plain,
% 2.85/0.99      ( X0 = X1
% 2.85/0.99      | X0 = X2
% 2.85/0.99      | X0 = X3
% 2.85/0.99      | r2_hidden(X0,k1_enumset1(X1,X2,X3)) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4889,plain,
% 2.85/0.99      ( k1_funct_1(sK5,X0) = sK3 | r2_hidden(X0,sK2) != iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_4885,c_2703]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4898,plain,
% 2.85/0.99      ( k1_funct_1(sK5,sK4) = sK3 ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_2695,c_4889]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_26,negated_conjecture,
% 2.85/0.99      ( k1_funct_1(sK5,sK4) != sK3 ),
% 2.85/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(contradiction,plain,
% 2.85/0.99      ( $false ),
% 2.85/0.99      inference(minisat,[status(thm)],[c_4898,c_26]) ).
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  ------                               Statistics
% 2.85/0.99  
% 2.85/0.99  ------ General
% 2.85/0.99  
% 2.85/0.99  abstr_ref_over_cycles:                  0
% 2.85/0.99  abstr_ref_under_cycles:                 0
% 2.85/0.99  gc_basic_clause_elim:                   0
% 2.85/0.99  forced_gc_time:                         0
% 2.85/0.99  parsing_time:                           0.009
% 2.85/0.99  unif_index_cands_time:                  0.
% 2.85/0.99  unif_index_add_time:                    0.
% 2.85/0.99  orderings_time:                         0.
% 2.85/0.99  out_proof_time:                         0.008
% 2.85/0.99  total_time:                             0.159
% 2.85/0.99  num_of_symbols:                         52
% 2.85/0.99  num_of_terms:                           4756
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing
% 2.85/0.99  
% 2.85/0.99  num_of_splits:                          0
% 2.85/0.99  num_of_split_atoms:                     0
% 2.85/0.99  num_of_reused_defs:                     0
% 2.85/0.99  num_eq_ax_congr_red:                    25
% 2.85/0.99  num_of_sem_filtered_clauses:            1
% 2.85/0.99  num_of_subtypes:                        0
% 2.85/0.99  monotx_restored_types:                  0
% 2.85/0.99  sat_num_of_epr_types:                   0
% 2.85/0.99  sat_num_of_non_cyclic_types:            0
% 2.85/0.99  sat_guarded_non_collapsed_types:        0
% 2.85/0.99  num_pure_diseq_elim:                    0
% 2.85/0.99  simp_replaced_by:                       0
% 2.85/0.99  res_preprocessed:                       123
% 2.85/0.99  prep_upred:                             0
% 2.85/0.99  prep_unflattend:                        186
% 2.85/0.99  smt_new_axioms:                         0
% 2.85/0.99  pred_elim_cands:                        3
% 2.85/0.99  pred_elim:                              5
% 2.85/0.99  pred_elim_cl:                           8
% 2.85/0.99  pred_elim_cycles:                       10
% 2.85/0.99  merged_defs:                            0
% 2.85/0.99  merged_defs_ncl:                        0
% 2.85/0.99  bin_hyper_res:                          0
% 2.85/0.99  prep_cycles:                            4
% 2.85/0.99  pred_elim_time:                         0.031
% 2.85/0.99  splitting_time:                         0.
% 2.85/0.99  sem_filter_time:                        0.
% 2.85/0.99  monotx_time:                            0.
% 2.85/0.99  subtype_inf_time:                       0.
% 2.85/0.99  
% 2.85/0.99  ------ Problem properties
% 2.85/0.99  
% 2.85/0.99  clauses:                                23
% 2.85/0.99  conjectures:                            3
% 2.85/0.99  epr:                                    4
% 2.85/0.99  horn:                                   18
% 2.85/0.99  ground:                                 5
% 2.85/0.99  unary:                                  11
% 2.85/0.99  binary:                                 3
% 2.85/0.99  lits:                                   47
% 2.85/0.99  lits_eq:                                24
% 2.85/0.99  fd_pure:                                0
% 2.85/0.99  fd_pseudo:                              0
% 2.85/0.99  fd_cond:                                0
% 2.85/0.99  fd_pseudo_cond:                         6
% 2.85/0.99  ac_symbols:                             0
% 2.85/0.99  
% 2.85/0.99  ------ Propositional Solver
% 2.85/0.99  
% 2.85/0.99  prop_solver_calls:                      26
% 2.85/0.99  prop_fast_solver_calls:                 1041
% 2.85/0.99  smt_solver_calls:                       0
% 2.85/0.99  smt_fast_solver_calls:                  0
% 2.85/0.99  prop_num_of_clauses:                    1286
% 2.85/0.99  prop_preprocess_simplified:             5438
% 2.85/0.99  prop_fo_subsumed:                       4
% 2.85/0.99  prop_solver_time:                       0.
% 2.85/0.99  smt_solver_time:                        0.
% 2.85/0.99  smt_fast_solver_time:                   0.
% 2.85/0.99  prop_fast_solver_time:                  0.
% 2.85/0.99  prop_unsat_core_time:                   0.
% 2.85/0.99  
% 2.85/0.99  ------ QBF
% 2.85/0.99  
% 2.85/0.99  qbf_q_res:                              0
% 2.85/0.99  qbf_num_tautologies:                    0
% 2.85/0.99  qbf_prep_cycles:                        0
% 2.85/0.99  
% 2.85/0.99  ------ BMC1
% 2.85/0.99  
% 2.85/0.99  bmc1_current_bound:                     -1
% 2.85/0.99  bmc1_last_solved_bound:                 -1
% 2.85/0.99  bmc1_unsat_core_size:                   -1
% 2.85/0.99  bmc1_unsat_core_parents_size:           -1
% 2.85/0.99  bmc1_merge_next_fun:                    0
% 2.85/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation
% 2.85/0.99  
% 2.85/0.99  inst_num_of_clauses:                    364
% 2.85/0.99  inst_num_in_passive:                    176
% 2.85/0.99  inst_num_in_active:                     133
% 2.85/0.99  inst_num_in_unprocessed:                55
% 2.85/0.99  inst_num_of_loops:                      140
% 2.85/0.99  inst_num_of_learning_restarts:          0
% 2.85/0.99  inst_num_moves_active_passive:          5
% 2.85/0.99  inst_lit_activity:                      0
% 2.85/0.99  inst_lit_activity_moves:                0
% 2.85/0.99  inst_num_tautologies:                   0
% 2.85/0.99  inst_num_prop_implied:                  0
% 2.85/0.99  inst_num_existing_simplified:           0
% 2.85/0.99  inst_num_eq_res_simplified:             0
% 2.85/0.99  inst_num_child_elim:                    0
% 2.85/0.99  inst_num_of_dismatching_blockings:      109
% 2.85/0.99  inst_num_of_non_proper_insts:           268
% 2.85/0.99  inst_num_of_duplicates:                 0
% 2.85/0.99  inst_inst_num_from_inst_to_res:         0
% 2.85/0.99  inst_dismatching_checking_time:         0.
% 2.85/0.99  
% 2.85/0.99  ------ Resolution
% 2.85/0.99  
% 2.85/0.99  res_num_of_clauses:                     0
% 2.85/0.99  res_num_in_passive:                     0
% 2.85/0.99  res_num_in_active:                      0
% 2.85/0.99  res_num_of_loops:                       127
% 2.85/0.99  res_forward_subset_subsumed:            85
% 2.85/0.99  res_backward_subset_subsumed:           0
% 2.85/0.99  res_forward_subsumed:                   14
% 2.85/0.99  res_backward_subsumed:                  2
% 2.85/0.99  res_forward_subsumption_resolution:     3
% 2.85/0.99  res_backward_subsumption_resolution:    1
% 2.85/0.99  res_clause_to_clause_subsumption:       458
% 2.85/0.99  res_orphan_elimination:                 0
% 2.85/0.99  res_tautology_del:                      27
% 2.85/0.99  res_num_eq_res_simplified:              0
% 2.85/0.99  res_num_sel_changes:                    0
% 2.85/0.99  res_moves_from_active_to_pass:          0
% 2.85/0.99  
% 2.85/0.99  ------ Superposition
% 2.85/0.99  
% 2.85/0.99  sup_time_total:                         0.
% 2.85/0.99  sup_time_generating:                    0.
% 2.85/0.99  sup_time_sim_full:                      0.
% 2.85/0.99  sup_time_sim_immed:                     0.
% 2.85/0.99  
% 2.85/0.99  sup_num_of_clauses:                     33
% 2.85/0.99  sup_num_in_active:                      24
% 2.85/0.99  sup_num_in_passive:                     9
% 2.85/0.99  sup_num_of_loops:                       27
% 2.85/0.99  sup_fw_superposition:                   15
% 2.85/0.99  sup_bw_superposition:                   5
% 2.85/0.99  sup_immediate_simplified:               0
% 2.85/0.99  sup_given_eliminated:                   0
% 2.85/0.99  comparisons_done:                       0
% 2.85/0.99  comparisons_avoided:                    2
% 2.85/0.99  
% 2.85/0.99  ------ Simplifications
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  sim_fw_subset_subsumed:                 0
% 2.85/0.99  sim_bw_subset_subsumed:                 1
% 2.85/0.99  sim_fw_subsumed:                        0
% 2.85/0.99  sim_bw_subsumed:                        1
% 2.85/0.99  sim_fw_subsumption_res:                 2
% 2.85/0.99  sim_bw_subsumption_res:                 0
% 2.85/0.99  sim_tautology_del:                      0
% 2.85/0.99  sim_eq_tautology_del:                   2
% 2.85/0.99  sim_eq_res_simp:                        0
% 2.85/0.99  sim_fw_demodulated:                     0
% 2.85/0.99  sim_bw_demodulated:                     3
% 2.85/0.99  sim_light_normalised:                   0
% 2.85/0.99  sim_joinable_taut:                      0
% 2.85/0.99  sim_joinable_simp:                      0
% 2.85/0.99  sim_ac_normalised:                      0
% 2.85/0.99  sim_smt_subsumption:                    0
% 2.85/0.99  
%------------------------------------------------------------------------------
