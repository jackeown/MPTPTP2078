%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:12 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 230 expanded)
%              Number of clauses        :   55 (  62 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  430 ( 911 expanded)
%              Number of equality atoms :  238 ( 423 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK4,sK3) != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_funct_1(sK4,sK3) != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f35])).

fof(f69,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f82,plain,(
    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f67,f72])).

fof(f12,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f87,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f88,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f87])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f89,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f70,plain,(
    k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1231,plain,
    ( r2_hidden(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_469,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_470,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_691,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != X0
    | k1_relset_1(X1,X0,sK4) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK1 != X1
    | sK4 != sK4
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_470])).

cnf(c_692,plain,
    ( k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_763,plain,
    ( k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = sK1
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_692])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_505,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_506,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_1407,plain,
    ( k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_506])).

cnf(c_1657,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | k1_relat_1(sK4) = sK1 ),
    inference(demodulation,[status(thm)],[c_763,c_1407])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1236,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1693,plain,
    ( k1_relat_1(sK4) = sK1
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_1236])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_325,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1230,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_4825,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1693,c_1230])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_1229,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_337,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_919,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1398,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_514,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_515,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1400,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_1401,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_1571,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1229,c_337,c_1398,c_1401])).

cnf(c_1572,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1571])).

cnf(c_4833,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4825,c_1572])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_455,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_1226,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_2013,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1226])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1233,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2676,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_1233])).

cnf(c_6503,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4833,c_2676])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1235,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8485,plain,
    ( k1_funct_1(sK4,X0) = sK2
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6503,c_1235])).

cnf(c_9425,plain,
    ( k1_funct_1(sK4,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_1231,c_8485])).

cnf(c_26,negated_conjecture,
    ( k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9425,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.73/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.01  
% 3.73/1.01  ------  iProver source info
% 3.73/1.01  
% 3.73/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.01  git: non_committed_changes: false
% 3.73/1.01  git: last_make_outside_of_git: false
% 3.73/1.01  
% 3.73/1.01  ------ 
% 3.73/1.01  
% 3.73/1.01  ------ Input Options
% 3.73/1.01  
% 3.73/1.01  --out_options                           all
% 3.73/1.01  --tptp_safe_out                         true
% 3.73/1.01  --problem_path                          ""
% 3.73/1.01  --include_path                          ""
% 3.73/1.01  --clausifier                            res/vclausify_rel
% 3.73/1.01  --clausifier_options                    --mode clausify
% 3.73/1.01  --stdin                                 false
% 3.73/1.01  --stats_out                             all
% 3.73/1.01  
% 3.73/1.01  ------ General Options
% 3.73/1.01  
% 3.73/1.01  --fof                                   false
% 3.73/1.01  --time_out_real                         305.
% 3.73/1.01  --time_out_virtual                      -1.
% 3.73/1.01  --symbol_type_check                     false
% 3.73/1.01  --clausify_out                          false
% 3.73/1.01  --sig_cnt_out                           false
% 3.73/1.01  --trig_cnt_out                          false
% 3.73/1.01  --trig_cnt_out_tolerance                1.
% 3.73/1.01  --trig_cnt_out_sk_spl                   false
% 3.73/1.01  --abstr_cl_out                          false
% 3.73/1.01  
% 3.73/1.01  ------ Global Options
% 3.73/1.01  
% 3.73/1.01  --schedule                              default
% 3.73/1.01  --add_important_lit                     false
% 3.73/1.01  --prop_solver_per_cl                    1000
% 3.73/1.01  --min_unsat_core                        false
% 3.73/1.01  --soft_assumptions                      false
% 3.73/1.01  --soft_lemma_size                       3
% 3.73/1.01  --prop_impl_unit_size                   0
% 3.73/1.01  --prop_impl_unit                        []
% 3.73/1.01  --share_sel_clauses                     true
% 3.73/1.01  --reset_solvers                         false
% 3.73/1.01  --bc_imp_inh                            [conj_cone]
% 3.73/1.01  --conj_cone_tolerance                   3.
% 3.73/1.01  --extra_neg_conj                        none
% 3.73/1.01  --large_theory_mode                     true
% 3.73/1.01  --prolific_symb_bound                   200
% 3.73/1.01  --lt_threshold                          2000
% 3.73/1.01  --clause_weak_htbl                      true
% 3.73/1.01  --gc_record_bc_elim                     false
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing Options
% 3.73/1.01  
% 3.73/1.01  --preprocessing_flag                    true
% 3.73/1.01  --time_out_prep_mult                    0.1
% 3.73/1.01  --splitting_mode                        input
% 3.73/1.01  --splitting_grd                         true
% 3.73/1.01  --splitting_cvd                         false
% 3.73/1.01  --splitting_cvd_svl                     false
% 3.73/1.01  --splitting_nvd                         32
% 3.73/1.01  --sub_typing                            true
% 3.73/1.01  --prep_gs_sim                           true
% 3.73/1.01  --prep_unflatten                        true
% 3.73/1.01  --prep_res_sim                          true
% 3.73/1.01  --prep_upred                            true
% 3.73/1.01  --prep_sem_filter                       exhaustive
% 3.73/1.01  --prep_sem_filter_out                   false
% 3.73/1.01  --pred_elim                             true
% 3.73/1.01  --res_sim_input                         true
% 3.73/1.01  --eq_ax_congr_red                       true
% 3.73/1.01  --pure_diseq_elim                       true
% 3.73/1.01  --brand_transform                       false
% 3.73/1.01  --non_eq_to_eq                          false
% 3.73/1.01  --prep_def_merge                        true
% 3.73/1.01  --prep_def_merge_prop_impl              false
% 3.73/1.01  --prep_def_merge_mbd                    true
% 3.73/1.01  --prep_def_merge_tr_red                 false
% 3.73/1.01  --prep_def_merge_tr_cl                  false
% 3.73/1.01  --smt_preprocessing                     true
% 3.73/1.01  --smt_ac_axioms                         fast
% 3.73/1.01  --preprocessed_out                      false
% 3.73/1.01  --preprocessed_stats                    false
% 3.73/1.01  
% 3.73/1.01  ------ Abstraction refinement Options
% 3.73/1.01  
% 3.73/1.01  --abstr_ref                             []
% 3.73/1.01  --abstr_ref_prep                        false
% 3.73/1.01  --abstr_ref_until_sat                   false
% 3.73/1.01  --abstr_ref_sig_restrict                funpre
% 3.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.01  --abstr_ref_under                       []
% 3.73/1.01  
% 3.73/1.01  ------ SAT Options
% 3.73/1.01  
% 3.73/1.01  --sat_mode                              false
% 3.73/1.01  --sat_fm_restart_options                ""
% 3.73/1.01  --sat_gr_def                            false
% 3.73/1.01  --sat_epr_types                         true
% 3.73/1.01  --sat_non_cyclic_types                  false
% 3.73/1.01  --sat_finite_models                     false
% 3.73/1.01  --sat_fm_lemmas                         false
% 3.73/1.01  --sat_fm_prep                           false
% 3.73/1.01  --sat_fm_uc_incr                        true
% 3.73/1.01  --sat_out_model                         small
% 3.73/1.01  --sat_out_clauses                       false
% 3.73/1.01  
% 3.73/1.01  ------ QBF Options
% 3.73/1.01  
% 3.73/1.01  --qbf_mode                              false
% 3.73/1.01  --qbf_elim_univ                         false
% 3.73/1.01  --qbf_dom_inst                          none
% 3.73/1.01  --qbf_dom_pre_inst                      false
% 3.73/1.01  --qbf_sk_in                             false
% 3.73/1.01  --qbf_pred_elim                         true
% 3.73/1.01  --qbf_split                             512
% 3.73/1.01  
% 3.73/1.01  ------ BMC1 Options
% 3.73/1.01  
% 3.73/1.01  --bmc1_incremental                      false
% 3.73/1.01  --bmc1_axioms                           reachable_all
% 3.73/1.01  --bmc1_min_bound                        0
% 3.73/1.01  --bmc1_max_bound                        -1
% 3.73/1.01  --bmc1_max_bound_default                -1
% 3.73/1.01  --bmc1_symbol_reachability              true
% 3.73/1.01  --bmc1_property_lemmas                  false
% 3.73/1.01  --bmc1_k_induction                      false
% 3.73/1.01  --bmc1_non_equiv_states                 false
% 3.73/1.01  --bmc1_deadlock                         false
% 3.73/1.01  --bmc1_ucm                              false
% 3.73/1.01  --bmc1_add_unsat_core                   none
% 3.73/1.01  --bmc1_unsat_core_children              false
% 3.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.01  --bmc1_out_stat                         full
% 3.73/1.01  --bmc1_ground_init                      false
% 3.73/1.01  --bmc1_pre_inst_next_state              false
% 3.73/1.01  --bmc1_pre_inst_state                   false
% 3.73/1.01  --bmc1_pre_inst_reach_state             false
% 3.73/1.01  --bmc1_out_unsat_core                   false
% 3.73/1.01  --bmc1_aig_witness_out                  false
% 3.73/1.01  --bmc1_verbose                          false
% 3.73/1.01  --bmc1_dump_clauses_tptp                false
% 3.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.01  --bmc1_dump_file                        -
% 3.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.01  --bmc1_ucm_extend_mode                  1
% 3.73/1.01  --bmc1_ucm_init_mode                    2
% 3.73/1.01  --bmc1_ucm_cone_mode                    none
% 3.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.01  --bmc1_ucm_relax_model                  4
% 3.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.01  --bmc1_ucm_layered_model                none
% 3.73/1.01  --bmc1_ucm_max_lemma_size               10
% 3.73/1.01  
% 3.73/1.01  ------ AIG Options
% 3.73/1.01  
% 3.73/1.01  --aig_mode                              false
% 3.73/1.01  
% 3.73/1.01  ------ Instantiation Options
% 3.73/1.01  
% 3.73/1.01  --instantiation_flag                    true
% 3.73/1.01  --inst_sos_flag                         false
% 3.73/1.01  --inst_sos_phase                        true
% 3.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel_side                     num_symb
% 3.73/1.01  --inst_solver_per_active                1400
% 3.73/1.01  --inst_solver_calls_frac                1.
% 3.73/1.01  --inst_passive_queue_type               priority_queues
% 3.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.01  --inst_passive_queues_freq              [25;2]
% 3.73/1.01  --inst_dismatching                      true
% 3.73/1.01  --inst_eager_unprocessed_to_passive     true
% 3.73/1.01  --inst_prop_sim_given                   true
% 3.73/1.01  --inst_prop_sim_new                     false
% 3.73/1.01  --inst_subs_new                         false
% 3.73/1.01  --inst_eq_res_simp                      false
% 3.73/1.01  --inst_subs_given                       false
% 3.73/1.01  --inst_orphan_elimination               true
% 3.73/1.01  --inst_learning_loop_flag               true
% 3.73/1.01  --inst_learning_start                   3000
% 3.73/1.01  --inst_learning_factor                  2
% 3.73/1.01  --inst_start_prop_sim_after_learn       3
% 3.73/1.01  --inst_sel_renew                        solver
% 3.73/1.01  --inst_lit_activity_flag                true
% 3.73/1.01  --inst_restr_to_given                   false
% 3.73/1.01  --inst_activity_threshold               500
% 3.73/1.01  --inst_out_proof                        true
% 3.73/1.01  
% 3.73/1.01  ------ Resolution Options
% 3.73/1.01  
% 3.73/1.01  --resolution_flag                       true
% 3.73/1.01  --res_lit_sel                           adaptive
% 3.73/1.01  --res_lit_sel_side                      none
% 3.73/1.01  --res_ordering                          kbo
% 3.73/1.01  --res_to_prop_solver                    active
% 3.73/1.01  --res_prop_simpl_new                    false
% 3.73/1.01  --res_prop_simpl_given                  true
% 3.73/1.01  --res_passive_queue_type                priority_queues
% 3.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.01  --res_passive_queues_freq               [15;5]
% 3.73/1.01  --res_forward_subs                      full
% 3.73/1.01  --res_backward_subs                     full
% 3.73/1.01  --res_forward_subs_resolution           true
% 3.73/1.01  --res_backward_subs_resolution          true
% 3.73/1.01  --res_orphan_elimination                true
% 3.73/1.01  --res_time_limit                        2.
% 3.73/1.01  --res_out_proof                         true
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Options
% 3.73/1.01  
% 3.73/1.01  --superposition_flag                    true
% 3.73/1.01  --sup_passive_queue_type                priority_queues
% 3.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.01  --demod_completeness_check              fast
% 3.73/1.01  --demod_use_ground                      true
% 3.73/1.01  --sup_to_prop_solver                    passive
% 3.73/1.01  --sup_prop_simpl_new                    true
% 3.73/1.01  --sup_prop_simpl_given                  true
% 3.73/1.01  --sup_fun_splitting                     false
% 3.73/1.01  --sup_smt_interval                      50000
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Simplification Setup
% 3.73/1.01  
% 3.73/1.01  --sup_indices_passive                   []
% 3.73/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.01  --sup_full_bw                           [BwDemod]
% 3.73/1.01  --sup_immed_triv                        [TrivRules]
% 3.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.01  --sup_immed_bw_main                     []
% 3.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.01  
% 3.73/1.01  ------ Combination Options
% 3.73/1.01  
% 3.73/1.01  --comb_res_mult                         3
% 3.73/1.01  --comb_sup_mult                         2
% 3.73/1.01  --comb_inst_mult                        10
% 3.73/1.01  
% 3.73/1.01  ------ Debug Options
% 3.73/1.01  
% 3.73/1.01  --dbg_backtrace                         false
% 3.73/1.01  --dbg_dump_prop_clauses                 false
% 3.73/1.01  --dbg_dump_prop_clauses_file            -
% 3.73/1.01  --dbg_out_stat                          false
% 3.73/1.01  ------ Parsing...
% 3.73/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  ------ Proving...
% 3.73/1.01  ------ Problem Properties 
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  clauses                                 23
% 3.73/1.01  conjectures                             2
% 3.73/1.01  EPR                                     2
% 3.73/1.01  Horn                                    18
% 3.73/1.01  unary                                   6
% 3.73/1.01  binary                                  5
% 3.73/1.01  lits                                    57
% 3.73/1.01  lits eq                                 29
% 3.73/1.01  fd_pure                                 0
% 3.73/1.01  fd_pseudo                               0
% 3.73/1.01  fd_cond                                 0
% 3.73/1.01  fd_pseudo_cond                          5
% 3.73/1.01  AC symbols                              0
% 3.73/1.01  
% 3.73/1.01  ------ Schedule dynamic 5 is on 
% 3.73/1.01  
% 3.73/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ 
% 3.73/1.01  Current options:
% 3.73/1.01  ------ 
% 3.73/1.01  
% 3.73/1.01  ------ Input Options
% 3.73/1.01  
% 3.73/1.01  --out_options                           all
% 3.73/1.01  --tptp_safe_out                         true
% 3.73/1.01  --problem_path                          ""
% 3.73/1.01  --include_path                          ""
% 3.73/1.01  --clausifier                            res/vclausify_rel
% 3.73/1.01  --clausifier_options                    --mode clausify
% 3.73/1.01  --stdin                                 false
% 3.73/1.01  --stats_out                             all
% 3.73/1.01  
% 3.73/1.01  ------ General Options
% 3.73/1.01  
% 3.73/1.01  --fof                                   false
% 3.73/1.01  --time_out_real                         305.
% 3.73/1.01  --time_out_virtual                      -1.
% 3.73/1.01  --symbol_type_check                     false
% 3.73/1.01  --clausify_out                          false
% 3.73/1.01  --sig_cnt_out                           false
% 3.73/1.01  --trig_cnt_out                          false
% 3.73/1.01  --trig_cnt_out_tolerance                1.
% 3.73/1.01  --trig_cnt_out_sk_spl                   false
% 3.73/1.01  --abstr_cl_out                          false
% 3.73/1.01  
% 3.73/1.01  ------ Global Options
% 3.73/1.01  
% 3.73/1.01  --schedule                              default
% 3.73/1.01  --add_important_lit                     false
% 3.73/1.01  --prop_solver_per_cl                    1000
% 3.73/1.01  --min_unsat_core                        false
% 3.73/1.01  --soft_assumptions                      false
% 3.73/1.01  --soft_lemma_size                       3
% 3.73/1.01  --prop_impl_unit_size                   0
% 3.73/1.01  --prop_impl_unit                        []
% 3.73/1.01  --share_sel_clauses                     true
% 3.73/1.01  --reset_solvers                         false
% 3.73/1.01  --bc_imp_inh                            [conj_cone]
% 3.73/1.01  --conj_cone_tolerance                   3.
% 3.73/1.01  --extra_neg_conj                        none
% 3.73/1.01  --large_theory_mode                     true
% 3.73/1.01  --prolific_symb_bound                   200
% 3.73/1.01  --lt_threshold                          2000
% 3.73/1.01  --clause_weak_htbl                      true
% 3.73/1.01  --gc_record_bc_elim                     false
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing Options
% 3.73/1.01  
% 3.73/1.01  --preprocessing_flag                    true
% 3.73/1.01  --time_out_prep_mult                    0.1
% 3.73/1.01  --splitting_mode                        input
% 3.73/1.01  --splitting_grd                         true
% 3.73/1.01  --splitting_cvd                         false
% 3.73/1.01  --splitting_cvd_svl                     false
% 3.73/1.01  --splitting_nvd                         32
% 3.73/1.01  --sub_typing                            true
% 3.73/1.01  --prep_gs_sim                           true
% 3.73/1.01  --prep_unflatten                        true
% 3.73/1.01  --prep_res_sim                          true
% 3.73/1.01  --prep_upred                            true
% 3.73/1.01  --prep_sem_filter                       exhaustive
% 3.73/1.01  --prep_sem_filter_out                   false
% 3.73/1.01  --pred_elim                             true
% 3.73/1.01  --res_sim_input                         true
% 3.73/1.01  --eq_ax_congr_red                       true
% 3.73/1.01  --pure_diseq_elim                       true
% 3.73/1.01  --brand_transform                       false
% 3.73/1.01  --non_eq_to_eq                          false
% 3.73/1.01  --prep_def_merge                        true
% 3.73/1.01  --prep_def_merge_prop_impl              false
% 3.73/1.01  --prep_def_merge_mbd                    true
% 3.73/1.01  --prep_def_merge_tr_red                 false
% 3.73/1.01  --prep_def_merge_tr_cl                  false
% 3.73/1.01  --smt_preprocessing                     true
% 3.73/1.01  --smt_ac_axioms                         fast
% 3.73/1.01  --preprocessed_out                      false
% 3.73/1.01  --preprocessed_stats                    false
% 3.73/1.01  
% 3.73/1.01  ------ Abstraction refinement Options
% 3.73/1.01  
% 3.73/1.01  --abstr_ref                             []
% 3.73/1.01  --abstr_ref_prep                        false
% 3.73/1.01  --abstr_ref_until_sat                   false
% 3.73/1.01  --abstr_ref_sig_restrict                funpre
% 3.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.01  --abstr_ref_under                       []
% 3.73/1.01  
% 3.73/1.01  ------ SAT Options
% 3.73/1.01  
% 3.73/1.01  --sat_mode                              false
% 3.73/1.01  --sat_fm_restart_options                ""
% 3.73/1.01  --sat_gr_def                            false
% 3.73/1.01  --sat_epr_types                         true
% 3.73/1.01  --sat_non_cyclic_types                  false
% 3.73/1.01  --sat_finite_models                     false
% 3.73/1.01  --sat_fm_lemmas                         false
% 3.73/1.01  --sat_fm_prep                           false
% 3.73/1.01  --sat_fm_uc_incr                        true
% 3.73/1.01  --sat_out_model                         small
% 3.73/1.01  --sat_out_clauses                       false
% 3.73/1.01  
% 3.73/1.01  ------ QBF Options
% 3.73/1.01  
% 3.73/1.01  --qbf_mode                              false
% 3.73/1.01  --qbf_elim_univ                         false
% 3.73/1.01  --qbf_dom_inst                          none
% 3.73/1.01  --qbf_dom_pre_inst                      false
% 3.73/1.01  --qbf_sk_in                             false
% 3.73/1.01  --qbf_pred_elim                         true
% 3.73/1.01  --qbf_split                             512
% 3.73/1.01  
% 3.73/1.01  ------ BMC1 Options
% 3.73/1.01  
% 3.73/1.01  --bmc1_incremental                      false
% 3.73/1.01  --bmc1_axioms                           reachable_all
% 3.73/1.01  --bmc1_min_bound                        0
% 3.73/1.01  --bmc1_max_bound                        -1
% 3.73/1.01  --bmc1_max_bound_default                -1
% 3.73/1.01  --bmc1_symbol_reachability              true
% 3.73/1.01  --bmc1_property_lemmas                  false
% 3.73/1.01  --bmc1_k_induction                      false
% 3.73/1.01  --bmc1_non_equiv_states                 false
% 3.73/1.01  --bmc1_deadlock                         false
% 3.73/1.01  --bmc1_ucm                              false
% 3.73/1.01  --bmc1_add_unsat_core                   none
% 3.73/1.01  --bmc1_unsat_core_children              false
% 3.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.01  --bmc1_out_stat                         full
% 3.73/1.01  --bmc1_ground_init                      false
% 3.73/1.01  --bmc1_pre_inst_next_state              false
% 3.73/1.01  --bmc1_pre_inst_state                   false
% 3.73/1.01  --bmc1_pre_inst_reach_state             false
% 3.73/1.01  --bmc1_out_unsat_core                   false
% 3.73/1.01  --bmc1_aig_witness_out                  false
% 3.73/1.01  --bmc1_verbose                          false
% 3.73/1.01  --bmc1_dump_clauses_tptp                false
% 3.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.01  --bmc1_dump_file                        -
% 3.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.01  --bmc1_ucm_extend_mode                  1
% 3.73/1.01  --bmc1_ucm_init_mode                    2
% 3.73/1.01  --bmc1_ucm_cone_mode                    none
% 3.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.01  --bmc1_ucm_relax_model                  4
% 3.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.01  --bmc1_ucm_layered_model                none
% 3.73/1.01  --bmc1_ucm_max_lemma_size               10
% 3.73/1.01  
% 3.73/1.01  ------ AIG Options
% 3.73/1.01  
% 3.73/1.01  --aig_mode                              false
% 3.73/1.01  
% 3.73/1.01  ------ Instantiation Options
% 3.73/1.01  
% 3.73/1.01  --instantiation_flag                    true
% 3.73/1.01  --inst_sos_flag                         false
% 3.73/1.01  --inst_sos_phase                        true
% 3.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel_side                     none
% 3.73/1.01  --inst_solver_per_active                1400
% 3.73/1.01  --inst_solver_calls_frac                1.
% 3.73/1.01  --inst_passive_queue_type               priority_queues
% 3.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.01  --inst_passive_queues_freq              [25;2]
% 3.73/1.01  --inst_dismatching                      true
% 3.73/1.01  --inst_eager_unprocessed_to_passive     true
% 3.73/1.01  --inst_prop_sim_given                   true
% 3.73/1.01  --inst_prop_sim_new                     false
% 3.73/1.01  --inst_subs_new                         false
% 3.73/1.01  --inst_eq_res_simp                      false
% 3.73/1.01  --inst_subs_given                       false
% 3.73/1.01  --inst_orphan_elimination               true
% 3.73/1.01  --inst_learning_loop_flag               true
% 3.73/1.01  --inst_learning_start                   3000
% 3.73/1.01  --inst_learning_factor                  2
% 3.73/1.01  --inst_start_prop_sim_after_learn       3
% 3.73/1.01  --inst_sel_renew                        solver
% 3.73/1.01  --inst_lit_activity_flag                true
% 3.73/1.01  --inst_restr_to_given                   false
% 3.73/1.01  --inst_activity_threshold               500
% 3.73/1.01  --inst_out_proof                        true
% 3.73/1.01  
% 3.73/1.01  ------ Resolution Options
% 3.73/1.01  
% 3.73/1.01  --resolution_flag                       false
% 3.73/1.01  --res_lit_sel                           adaptive
% 3.73/1.01  --res_lit_sel_side                      none
% 3.73/1.01  --res_ordering                          kbo
% 3.73/1.01  --res_to_prop_solver                    active
% 3.73/1.01  --res_prop_simpl_new                    false
% 3.73/1.01  --res_prop_simpl_given                  true
% 3.73/1.01  --res_passive_queue_type                priority_queues
% 3.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.01  --res_passive_queues_freq               [15;5]
% 3.73/1.01  --res_forward_subs                      full
% 3.73/1.01  --res_backward_subs                     full
% 3.73/1.01  --res_forward_subs_resolution           true
% 3.73/1.01  --res_backward_subs_resolution          true
% 3.73/1.01  --res_orphan_elimination                true
% 3.73/1.01  --res_time_limit                        2.
% 3.73/1.01  --res_out_proof                         true
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Options
% 3.73/1.01  
% 3.73/1.01  --superposition_flag                    true
% 3.73/1.01  --sup_passive_queue_type                priority_queues
% 3.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.01  --demod_completeness_check              fast
% 3.73/1.01  --demod_use_ground                      true
% 3.73/1.01  --sup_to_prop_solver                    passive
% 3.73/1.01  --sup_prop_simpl_new                    true
% 3.73/1.01  --sup_prop_simpl_given                  true
% 3.73/1.01  --sup_fun_splitting                     false
% 3.73/1.01  --sup_smt_interval                      50000
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Simplification Setup
% 3.73/1.01  
% 3.73/1.01  --sup_indices_passive                   []
% 3.73/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.01  --sup_full_bw                           [BwDemod]
% 3.73/1.01  --sup_immed_triv                        [TrivRules]
% 3.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.01  --sup_immed_bw_main                     []
% 3.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/1.01  
% 3.73/1.01  ------ Combination Options
% 3.73/1.01  
% 3.73/1.01  --comb_res_mult                         3
% 3.73/1.01  --comb_sup_mult                         2
% 3.73/1.01  --comb_inst_mult                        10
% 3.73/1.01  
% 3.73/1.01  ------ Debug Options
% 3.73/1.01  
% 3.73/1.01  --dbg_backtrace                         false
% 3.73/1.01  --dbg_dump_prop_clauses                 false
% 3.73/1.01  --dbg_dump_prop_clauses_file            -
% 3.73/1.01  --dbg_out_stat                          false
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS status Theorem for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  fof(f13,conjecture,(
% 3.73/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f14,negated_conjecture,(
% 3.73/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.73/1.01    inference(negated_conjecture,[],[f13])).
% 3.73/1.01  
% 3.73/1.01  fof(f24,plain,(
% 3.73/1.01    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.73/1.01    inference(ennf_transformation,[],[f14])).
% 3.73/1.01  
% 3.73/1.01  fof(f25,plain,(
% 3.73/1.01    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.73/1.01    inference(flattening,[],[f24])).
% 3.73/1.01  
% 3.73/1.01  fof(f35,plain,(
% 3.73/1.01    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f36,plain,(
% 3.73/1.01    k1_funct_1(sK4,sK3) != sK2 & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 3.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f35])).
% 3.73/1.01  
% 3.73/1.01  fof(f69,plain,(
% 3.73/1.01    r2_hidden(sK3,sK1)),
% 3.73/1.01    inference(cnf_transformation,[],[f36])).
% 3.73/1.01  
% 3.73/1.01  fof(f67,plain,(
% 3.73/1.01    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 3.73/1.01    inference(cnf_transformation,[],[f36])).
% 3.73/1.01  
% 3.73/1.01  fof(f3,axiom,(
% 3.73/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f46,plain,(
% 3.73/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f3])).
% 3.73/1.01  
% 3.73/1.01  fof(f4,axiom,(
% 3.73/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f47,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f4])).
% 3.73/1.01  
% 3.73/1.01  fof(f5,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f48,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f5])).
% 3.73/1.01  
% 3.73/1.01  fof(f71,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.73/1.01    inference(definition_unfolding,[],[f47,f48])).
% 3.73/1.01  
% 3.73/1.01  fof(f72,plain,(
% 3.73/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.73/1.01    inference(definition_unfolding,[],[f46,f71])).
% 3.73/1.01  
% 3.73/1.01  fof(f82,plain,(
% 3.73/1.01    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 3.73/1.01    inference(definition_unfolding,[],[f67,f72])).
% 3.73/1.01  
% 3.73/1.01  fof(f12,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f22,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.01    inference(ennf_transformation,[],[f12])).
% 3.73/1.01  
% 3.73/1.01  fof(f23,plain,(
% 3.73/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.01    inference(flattening,[],[f22])).
% 3.73/1.01  
% 3.73/1.01  fof(f34,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.01    inference(nnf_transformation,[],[f23])).
% 3.73/1.01  
% 3.73/1.01  fof(f60,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f34])).
% 3.73/1.01  
% 3.73/1.01  fof(f68,plain,(
% 3.73/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 3.73/1.01    inference(cnf_transformation,[],[f36])).
% 3.73/1.01  
% 3.73/1.01  fof(f81,plain,(
% 3.73/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 3.73/1.01    inference(definition_unfolding,[],[f68,f72])).
% 3.73/1.01  
% 3.73/1.01  fof(f11,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f21,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.01    inference(ennf_transformation,[],[f11])).
% 3.73/1.01  
% 3.73/1.01  fof(f59,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f21])).
% 3.73/1.01  
% 3.73/1.01  fof(f2,axiom,(
% 3.73/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f15,plain,(
% 3.73/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.73/1.01    inference(ennf_transformation,[],[f2])).
% 3.73/1.01  
% 3.73/1.01  fof(f26,plain,(
% 3.73/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.01    inference(nnf_transformation,[],[f15])).
% 3.73/1.01  
% 3.73/1.01  fof(f27,plain,(
% 3.73/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.01    inference(flattening,[],[f26])).
% 3.73/1.01  
% 3.73/1.01  fof(f28,plain,(
% 3.73/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.01    inference(rectify,[],[f27])).
% 3.73/1.01  
% 3.73/1.01  fof(f29,plain,(
% 3.73/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f30,plain,(
% 3.73/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.73/1.01  
% 3.73/1.01  fof(f39,plain,(
% 3.73/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.73/1.01    inference(cnf_transformation,[],[f30])).
% 3.73/1.01  
% 3.73/1.01  fof(f79,plain,(
% 3.73/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.73/1.01    inference(definition_unfolding,[],[f39,f48])).
% 3.73/1.01  
% 3.73/1.01  fof(f87,plain,(
% 3.73/1.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.73/1.01    inference(equality_resolution,[],[f79])).
% 3.73/1.01  
% 3.73/1.01  fof(f88,plain,(
% 3.73/1.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.73/1.01    inference(equality_resolution,[],[f87])).
% 3.73/1.01  
% 3.73/1.01  fof(f1,axiom,(
% 3.73/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f37,plain,(
% 3.73/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f1])).
% 3.73/1.01  
% 3.73/1.01  fof(f9,axiom,(
% 3.73/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f19,plain,(
% 3.73/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.73/1.01    inference(ennf_transformation,[],[f9])).
% 3.73/1.01  
% 3.73/1.01  fof(f57,plain,(
% 3.73/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f19])).
% 3.73/1.01  
% 3.73/1.01  fof(f8,axiom,(
% 3.73/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f17,plain,(
% 3.73/1.01    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.73/1.01    inference(ennf_transformation,[],[f8])).
% 3.73/1.01  
% 3.73/1.01  fof(f18,plain,(
% 3.73/1.01    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/1.01    inference(flattening,[],[f17])).
% 3.73/1.01  
% 3.73/1.01  fof(f33,plain,(
% 3.73/1.01    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/1.01    inference(nnf_transformation,[],[f18])).
% 3.73/1.01  
% 3.73/1.01  fof(f53,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f33])).
% 3.73/1.01  
% 3.73/1.01  fof(f92,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/1.01    inference(equality_resolution,[],[f53])).
% 3.73/1.01  
% 3.73/1.01  fof(f66,plain,(
% 3.73/1.01    v1_funct_1(sK4)),
% 3.73/1.01    inference(cnf_transformation,[],[f36])).
% 3.73/1.01  
% 3.73/1.01  fof(f10,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f20,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/1.01    inference(ennf_transformation,[],[f10])).
% 3.73/1.01  
% 3.73/1.01  fof(f58,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f20])).
% 3.73/1.01  
% 3.73/1.01  fof(f7,axiom,(
% 3.73/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f16,plain,(
% 3.73/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/1.01    inference(ennf_transformation,[],[f7])).
% 3.73/1.01  
% 3.73/1.01  fof(f52,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f16])).
% 3.73/1.01  
% 3.73/1.01  fof(f6,axiom,(
% 3.73/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f31,plain,(
% 3.73/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.73/1.01    inference(nnf_transformation,[],[f6])).
% 3.73/1.01  
% 3.73/1.01  fof(f32,plain,(
% 3.73/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.73/1.01    inference(flattening,[],[f31])).
% 3.73/1.01  
% 3.73/1.01  fof(f50,plain,(
% 3.73/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f32])).
% 3.73/1.01  
% 3.73/1.01  fof(f38,plain,(
% 3.73/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.73/1.01    inference(cnf_transformation,[],[f30])).
% 3.73/1.01  
% 3.73/1.01  fof(f80,plain,(
% 3.73/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.73/1.01    inference(definition_unfolding,[],[f38,f48])).
% 3.73/1.01  
% 3.73/1.01  fof(f89,plain,(
% 3.73/1.01    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.73/1.01    inference(equality_resolution,[],[f80])).
% 3.73/1.01  
% 3.73/1.01  fof(f70,plain,(
% 3.73/1.01    k1_funct_1(sK4,sK3) != sK2),
% 3.73/1.01    inference(cnf_transformation,[],[f36])).
% 3.73/1.01  
% 3.73/1.01  cnf(c_27,negated_conjecture,
% 3.73/1.01      ( r2_hidden(sK3,sK1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1231,plain,
% 3.73/1.01      ( r2_hidden(sK3,sK1) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_29,negated_conjecture,
% 3.73/1.01      ( v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_25,plain,
% 3.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.73/1.01      | k1_xboole_0 = X2 ),
% 3.73/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_28,negated_conjecture,
% 3.73/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
% 3.73/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_469,plain,
% 3.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.73/1.01      | sK4 != X0
% 3.73/1.01      | k1_xboole_0 = X2 ),
% 3.73/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_28]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_470,plain,
% 3.73/1.01      ( ~ v1_funct_2(sK4,X0,X1)
% 3.73/1.01      | k1_relset_1(X0,X1,sK4) = X0
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.73/1.01      | k1_xboole_0 = X1 ),
% 3.73/1.01      inference(unflattening,[status(thm)],[c_469]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_691,plain,
% 3.73/1.01      ( k2_enumset1(sK2,sK2,sK2,sK2) != X0
% 3.73/1.01      | k1_relset_1(X1,X0,sK4) = X1
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 3.73/1.01      | sK1 != X1
% 3.73/1.01      | sK4 != sK4
% 3.73/1.01      | k1_xboole_0 = X0 ),
% 3.73/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_470]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_692,plain,
% 3.73/1.01      ( k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = sK1
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.73/1.01      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.73/1.01      inference(unflattening,[status(thm)],[c_691]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_763,plain,
% 3.73/1.01      ( k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = sK1
% 3.73/1.01      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 3.73/1.01      inference(equality_resolution_simp,[status(thm)],[c_692]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_19,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_505,plain,
% 3.73/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.73/1.01      | sK4 != X2 ),
% 3.73/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_506,plain,
% 3.73/1.01      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.73/1.01      inference(unflattening,[status(thm)],[c_505]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1407,plain,
% 3.73/1.01      ( k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) = k1_relat_1(sK4) ),
% 3.73/1.01      inference(equality_resolution,[status(thm)],[c_506]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1657,plain,
% 3.73/1.01      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
% 3.73/1.01      | k1_relat_1(sK4) = sK1 ),
% 3.73/1.01      inference(demodulation,[status(thm)],[c_763,c_1407]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_7,plain,
% 3.73/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1236,plain,
% 3.73/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1693,plain,
% 3.73/1.01      ( k1_relat_1(sK4) = sK1
% 3.73/1.01      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_1657,c_1236]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_0,plain,
% 3.73/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_17,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_324,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.73/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_325,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.73/1.01      inference(unflattening,[status(thm)],[c_324]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1230,plain,
% 3.73/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_4825,plain,
% 3.73/1.01      ( k1_relat_1(sK4) = sK1 ),
% 3.73/1.01      inference(forward_subsumption_resolution,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_1693,c_1230]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_16,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.73/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.73/1.01      | ~ v1_relat_1(X1)
% 3.73/1.01      | ~ v1_funct_1(X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_30,negated_conjecture,
% 3.73/1.01      ( v1_funct_1(sK4) ),
% 3.73/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_335,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.73/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.73/1.01      | ~ v1_relat_1(X1)
% 3.73/1.01      | sK4 != X1 ),
% 3.73/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_336,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.73/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 3.73/1.01      | ~ v1_relat_1(sK4) ),
% 3.73/1.01      inference(unflattening,[status(thm)],[c_335]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1229,plain,
% 3.73/1.01      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.73/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 3.73/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_337,plain,
% 3.73/1.01      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.73/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 3.73/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_919,plain,( X0 = X0 ),theory(equality) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1398,plain,
% 3.73/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_919]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_18,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.01      | v1_relat_1(X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_514,plain,
% 3.73/1.01      ( v1_relat_1(X0)
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.73/1.01      | sK4 != X0 ),
% 3.73/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_515,plain,
% 3.73/1.01      ( v1_relat_1(sK4)
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.73/1.01      inference(unflattening,[status(thm)],[c_514]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1400,plain,
% 3.73/1.01      ( v1_relat_1(sK4)
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_515]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1401,plain,
% 3.73/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
% 3.73/1.01      | v1_relat_1(sK4) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1571,plain,
% 3.73/1.01      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 3.73/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.73/1.01      inference(global_propositional_subsumption,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_1229,c_337,c_1398,c_1401]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1572,plain,
% 3.73/1.01      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.73/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
% 3.73/1.01      inference(renaming,[status(thm)],[c_1571]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_4833,plain,
% 3.73/1.01      ( r2_hidden(X0,sK1) != iProver_top
% 3.73/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
% 3.73/1.01      inference(demodulation,[status(thm)],[c_4825,c_1572]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_12,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/1.01      | ~ r2_hidden(X2,X0)
% 3.73/1.01      | r2_hidden(X2,X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_454,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,X1)
% 3.73/1.01      | r2_hidden(X0,X2)
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(X2)
% 3.73/1.01      | sK4 != X1 ),
% 3.73/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_455,plain,
% 3.73/1.01      ( r2_hidden(X0,X1)
% 3.73/1.01      | ~ r2_hidden(X0,sK4)
% 3.73/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(X1) ),
% 3.73/1.01      inference(unflattening,[status(thm)],[c_454]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1226,plain,
% 3.73/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_zfmisc_1(X0)
% 3.73/1.01      | r2_hidden(X1,X0) = iProver_top
% 3.73/1.01      | r2_hidden(X1,sK4) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2013,plain,
% 3.73/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = iProver_top
% 3.73/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 3.73/1.01      inference(equality_resolution,[status(thm)],[c_1226]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_10,plain,
% 3.73/1.01      ( r2_hidden(X0,X1)
% 3.73/1.01      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1233,plain,
% 3.73/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.73/1.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2676,plain,
% 3.73/1.01      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 3.73/1.01      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_2013,c_1233]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_6503,plain,
% 3.73/1.01      ( r2_hidden(X0,sK1) != iProver_top
% 3.73/1.01      | r2_hidden(k1_funct_1(sK4,X0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_4833,c_2676]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.73/1.01      | X0 = X1
% 3.73/1.01      | X0 = X2
% 3.73/1.01      | X0 = X3 ),
% 3.73/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1235,plain,
% 3.73/1.01      ( X0 = X1
% 3.73/1.01      | X0 = X2
% 3.73/1.01      | X0 = X3
% 3.73/1.01      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8485,plain,
% 3.73/1.01      ( k1_funct_1(sK4,X0) = sK2 | r2_hidden(X0,sK1) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_6503,c_1235]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_9425,plain,
% 3.73/1.01      ( k1_funct_1(sK4,sK3) = sK2 ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_1231,c_8485]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_26,negated_conjecture,
% 3.73/1.01      ( k1_funct_1(sK4,sK3) != sK2 ),
% 3.73/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(contradiction,plain,
% 3.73/1.01      ( $false ),
% 3.73/1.01      inference(minisat,[status(thm)],[c_9425,c_26]) ).
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  ------                               Statistics
% 3.73/1.01  
% 3.73/1.01  ------ General
% 3.73/1.01  
% 3.73/1.01  abstr_ref_over_cycles:                  0
% 3.73/1.01  abstr_ref_under_cycles:                 0
% 3.73/1.01  gc_basic_clause_elim:                   0
% 3.73/1.01  forced_gc_time:                         0
% 3.73/1.01  parsing_time:                           0.012
% 3.73/1.01  unif_index_cands_time:                  0.
% 3.73/1.01  unif_index_add_time:                    0.
% 3.73/1.01  orderings_time:                         0.
% 3.73/1.01  out_proof_time:                         0.013
% 3.73/1.01  total_time:                             0.501
% 3.73/1.01  num_of_symbols:                         50
% 3.73/1.01  num_of_terms:                           15935
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing
% 3.73/1.01  
% 3.73/1.01  num_of_splits:                          0
% 3.73/1.01  num_of_split_atoms:                     0
% 3.73/1.01  num_of_reused_defs:                     0
% 3.73/1.01  num_eq_ax_congr_red:                    20
% 3.73/1.01  num_of_sem_filtered_clauses:            1
% 3.73/1.01  num_of_subtypes:                        0
% 3.73/1.01  monotx_restored_types:                  0
% 3.73/1.01  sat_num_of_epr_types:                   0
% 3.73/1.01  sat_num_of_non_cyclic_types:            0
% 3.73/1.01  sat_guarded_non_collapsed_types:        0
% 3.73/1.01  num_pure_diseq_elim:                    0
% 3.73/1.01  simp_replaced_by:                       0
% 3.73/1.01  res_preprocessed:                       122
% 3.73/1.01  prep_upred:                             0
% 3.73/1.01  prep_unflattend:                        33
% 3.73/1.01  smt_new_axioms:                         0
% 3.73/1.01  pred_elim_cands:                        2
% 3.73/1.01  pred_elim:                              4
% 3.73/1.01  pred_elim_cl:                           7
% 3.73/1.01  pred_elim_cycles:                       8
% 3.73/1.01  merged_defs:                            0
% 3.73/1.01  merged_defs_ncl:                        0
% 3.73/1.01  bin_hyper_res:                          0
% 3.73/1.01  prep_cycles:                            4
% 3.73/1.01  pred_elim_time:                         0.011
% 3.73/1.01  splitting_time:                         0.
% 3.73/1.01  sem_filter_time:                        0.
% 3.73/1.01  monotx_time:                            0.
% 3.73/1.01  subtype_inf_time:                       0.
% 3.73/1.01  
% 3.73/1.01  ------ Problem properties
% 3.73/1.01  
% 3.73/1.01  clauses:                                23
% 3.73/1.01  conjectures:                            2
% 3.73/1.01  epr:                                    2
% 3.73/1.01  horn:                                   18
% 3.73/1.01  ground:                                 5
% 3.73/1.01  unary:                                  6
% 3.73/1.01  binary:                                 5
% 3.73/1.01  lits:                                   57
% 3.73/1.01  lits_eq:                                29
% 3.73/1.01  fd_pure:                                0
% 3.73/1.01  fd_pseudo:                              0
% 3.73/1.01  fd_cond:                                0
% 3.73/1.01  fd_pseudo_cond:                         5
% 3.73/1.01  ac_symbols:                             0
% 3.73/1.01  
% 3.73/1.01  ------ Propositional Solver
% 3.73/1.01  
% 3.73/1.01  prop_solver_calls:                      29
% 3.73/1.01  prop_fast_solver_calls:                 888
% 3.73/1.01  smt_solver_calls:                       0
% 3.73/1.01  smt_fast_solver_calls:                  0
% 3.73/1.01  prop_num_of_clauses:                    4436
% 3.73/1.01  prop_preprocess_simplified:             16199
% 3.73/1.01  prop_fo_subsumed:                       8
% 3.73/1.01  prop_solver_time:                       0.
% 3.73/1.01  smt_solver_time:                        0.
% 3.73/1.01  smt_fast_solver_time:                   0.
% 3.73/1.01  prop_fast_solver_time:                  0.
% 3.73/1.01  prop_unsat_core_time:                   0.001
% 3.73/1.01  
% 3.73/1.01  ------ QBF
% 3.73/1.01  
% 3.73/1.01  qbf_q_res:                              0
% 3.73/1.01  qbf_num_tautologies:                    0
% 3.73/1.01  qbf_prep_cycles:                        0
% 3.73/1.01  
% 3.73/1.01  ------ BMC1
% 3.73/1.01  
% 3.73/1.01  bmc1_current_bound:                     -1
% 3.73/1.01  bmc1_last_solved_bound:                 -1
% 3.73/1.01  bmc1_unsat_core_size:                   -1
% 3.73/1.01  bmc1_unsat_core_parents_size:           -1
% 3.73/1.01  bmc1_merge_next_fun:                    0
% 3.73/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.73/1.01  
% 3.73/1.01  ------ Instantiation
% 3.73/1.01  
% 3.73/1.01  inst_num_of_clauses:                    1688
% 3.73/1.01  inst_num_in_passive:                    957
% 3.73/1.01  inst_num_in_active:                     258
% 3.73/1.01  inst_num_in_unprocessed:                473
% 3.73/1.01  inst_num_of_loops:                      270
% 3.73/1.01  inst_num_of_learning_restarts:          0
% 3.73/1.01  inst_num_moves_active_passive:          11
% 3.73/1.01  inst_lit_activity:                      0
% 3.73/1.01  inst_lit_activity_moves:                0
% 3.73/1.01  inst_num_tautologies:                   0
% 3.73/1.01  inst_num_prop_implied:                  0
% 3.73/1.01  inst_num_existing_simplified:           0
% 3.73/1.01  inst_num_eq_res_simplified:             0
% 3.73/1.01  inst_num_child_elim:                    0
% 3.73/1.01  inst_num_of_dismatching_blockings:      121
% 3.73/1.01  inst_num_of_non_proper_insts:           722
% 3.73/1.01  inst_num_of_duplicates:                 0
% 3.73/1.01  inst_inst_num_from_inst_to_res:         0
% 3.73/1.01  inst_dismatching_checking_time:         0.
% 3.73/1.01  
% 3.73/1.01  ------ Resolution
% 3.73/1.01  
% 3.73/1.01  res_num_of_clauses:                     0
% 3.73/1.01  res_num_in_passive:                     0
% 3.73/1.01  res_num_in_active:                      0
% 3.73/1.01  res_num_of_loops:                       126
% 3.73/1.01  res_forward_subset_subsumed:            142
% 3.73/1.01  res_backward_subset_subsumed:           0
% 3.73/1.01  res_forward_subsumed:                   0
% 3.73/1.01  res_backward_subsumed:                  0
% 3.73/1.01  res_forward_subsumption_resolution:     0
% 3.73/1.01  res_backward_subsumption_resolution:    0
% 3.73/1.01  res_clause_to_clause_subsumption:       315
% 3.73/1.01  res_orphan_elimination:                 0
% 3.73/1.01  res_tautology_del:                      15
% 3.73/1.01  res_num_eq_res_simplified:              1
% 3.73/1.01  res_num_sel_changes:                    0
% 3.73/1.01  res_moves_from_active_to_pass:          0
% 3.73/1.01  
% 3.73/1.01  ------ Superposition
% 3.73/1.01  
% 3.73/1.01  sup_time_total:                         0.
% 3.73/1.01  sup_time_generating:                    0.
% 3.73/1.01  sup_time_sim_full:                      0.
% 3.73/1.01  sup_time_sim_immed:                     0.
% 3.73/1.01  
% 3.73/1.01  sup_num_of_clauses:                     53
% 3.73/1.01  sup_num_in_active:                      39
% 3.73/1.01  sup_num_in_passive:                     14
% 3.73/1.01  sup_num_of_loops:                       52
% 3.73/1.01  sup_fw_superposition:                   42
% 3.73/1.01  sup_bw_superposition:                   68
% 3.73/1.01  sup_immediate_simplified:               37
% 3.73/1.01  sup_given_eliminated:                   1
% 3.73/1.01  comparisons_done:                       0
% 3.73/1.01  comparisons_avoided:                    30
% 3.73/1.01  
% 3.73/1.01  ------ Simplifications
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  sim_fw_subset_subsumed:                 9
% 3.73/1.01  sim_bw_subset_subsumed:                 11
% 3.73/1.01  sim_fw_subsumed:                        29
% 3.73/1.01  sim_bw_subsumed:                        1
% 3.73/1.01  sim_fw_subsumption_res:                 2
% 3.73/1.01  sim_bw_subsumption_res:                 0
% 3.73/1.01  sim_tautology_del:                      5
% 3.73/1.01  sim_eq_tautology_del:                   7
% 3.73/1.01  sim_eq_res_simp:                        0
% 3.73/1.01  sim_fw_demodulated:                     1
% 3.73/1.01  sim_bw_demodulated:                     10
% 3.73/1.01  sim_light_normalised:                   2
% 3.73/1.01  sim_joinable_taut:                      0
% 3.73/1.01  sim_joinable_simp:                      0
% 3.73/1.01  sim_ac_normalised:                      0
% 3.73/1.01  sim_smt_subsumption:                    0
% 3.73/1.01  
%------------------------------------------------------------------------------
