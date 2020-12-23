%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:15 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 262 expanded)
%              Number of clauses        :   51 (  69 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  424 ( 977 expanded)
%              Number of equality atoms :  217 ( 429 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK7,sK6) != sK5
      & r2_hidden(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
      & v1_funct_2(sK7,sK4,k1_tarski(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_funct_1(sK7,sK6) != sK5
    & r2_hidden(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
    & v1_funct_2(sK7,sK4,k1_tarski(sK5))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f39])).

fof(f71,plain,(
    r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f88,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f80,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f68,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    v1_funct_2(sK7,sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f84,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f85,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,(
    k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_741,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_755,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_740,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_748,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1366,plain,
    ( k2_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_740,c_748])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1885,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_750])).

cnf(c_32,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2045,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1885,c_32])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_759,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2345,plain,
    ( r2_hidden(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_759])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_760,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2897,plain,
    ( sK5 = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2345,c_760])).

cnf(c_5312,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_2897])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1030,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1031,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_7075,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5312,c_30,c_32,c_1031])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_742,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3910,plain,
    ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = sK4
    | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_742])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_749,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1566,plain,
    ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_740,c_749])).

cnf(c_3914,plain,
    ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4
    | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3910,c_1566])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3927,plain,
    ( ~ v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5))
    | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3914])).

cnf(c_4248,plain,
    ( k1_relat_1(sK7) = sK4
    | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3914,c_28,c_3927])).

cnf(c_4249,plain,
    ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(renaming,[status(thm)],[c_4248])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_761,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_752,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1211,plain,
    ( r1_tarski(k1_enumset1(X0,X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_752])).

cnf(c_4252,plain,
    ( k1_relat_1(sK7) = sK4
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4249,c_1211])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_766,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6914,plain,
    ( k1_relat_1(sK7) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4252,c_766])).

cnf(c_7081,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7075,c_6914])).

cnf(c_7090,plain,
    ( k1_funct_1(sK7,sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_741,c_7081])).

cnf(c_25,negated_conjecture,
    ( k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7090,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.72/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.98  
% 3.72/0.98  ------  iProver source info
% 3.72/0.98  
% 3.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.98  git: non_committed_changes: false
% 3.72/0.98  git: last_make_outside_of_git: false
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  ------ Parsing...
% 3.72/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  ------ Proving...
% 3.72/0.98  ------ Problem Properties 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  clauses                                 30
% 3.72/0.98  conjectures                             5
% 3.72/0.98  EPR                                     4
% 3.72/0.98  Horn                                    22
% 3.72/0.98  unary                                   8
% 3.72/0.98  binary                                  5
% 3.72/0.98  lits                                    83
% 3.72/0.98  lits eq                                 27
% 3.72/0.98  fd_pure                                 0
% 3.72/0.98  fd_pseudo                               0
% 3.72/0.98  fd_cond                                 3
% 3.72/0.98  fd_pseudo_cond                          6
% 3.72/0.98  AC symbols                              0
% 3.72/0.98  
% 3.72/0.98  ------ Input Options Time Limit: Unbounded
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  Current options:
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS status Theorem for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  fof(f13,conjecture,(
% 3.72/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f14,negated_conjecture,(
% 3.72/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.72/0.98    inference(negated_conjecture,[],[f13])).
% 3.72/0.98  
% 3.72/0.98  fof(f25,plain,(
% 3.72/0.98    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.72/0.98    inference(ennf_transformation,[],[f14])).
% 3.72/0.98  
% 3.72/0.98  fof(f26,plain,(
% 3.72/0.98    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.72/0.98    inference(flattening,[],[f25])).
% 3.72/0.98  
% 3.72/0.98  fof(f39,plain,(
% 3.72/0.98    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f40,plain,(
% 3.72/0.98    k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7)),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f39])).
% 3.72/0.98  
% 3.72/0.98  fof(f71,plain,(
% 3.72/0.98    r2_hidden(sK6,sK4)),
% 3.72/0.98    inference(cnf_transformation,[],[f40])).
% 3.72/0.98  
% 3.72/0.98  fof(f6,axiom,(
% 3.72/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f16,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.98    inference(ennf_transformation,[],[f6])).
% 3.72/0.98  
% 3.72/0.98  fof(f17,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(flattening,[],[f16])).
% 3.72/0.98  
% 3.72/0.98  fof(f32,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(nnf_transformation,[],[f17])).
% 3.72/0.98  
% 3.72/0.98  fof(f33,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(rectify,[],[f32])).
% 3.72/0.98  
% 3.72/0.98  fof(f36,plain,(
% 3.72/0.98    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f35,plain,(
% 3.72/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f34,plain,(
% 3.72/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f37,plain,(
% 3.72/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).
% 3.72/0.98  
% 3.72/0.98  fof(f53,plain,(
% 3.72/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f37])).
% 3.72/0.98  
% 3.72/0.98  fof(f87,plain,(
% 3.72/0.98    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.98    inference(equality_resolution,[],[f53])).
% 3.72/0.98  
% 3.72/0.98  fof(f88,plain,(
% 3.72/0.98    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.98    inference(equality_resolution,[],[f87])).
% 3.72/0.98  
% 3.72/0.98  fof(f70,plain,(
% 3.72/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))),
% 3.72/0.98    inference(cnf_transformation,[],[f40])).
% 3.72/0.98  
% 3.72/0.98  fof(f3,axiom,(
% 3.72/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f48,plain,(
% 3.72/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f3])).
% 3.72/0.98  
% 3.72/0.98  fof(f4,axiom,(
% 3.72/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f49,plain,(
% 3.72/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f4])).
% 3.72/0.98  
% 3.72/0.98  fof(f73,plain,(
% 3.72/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.72/0.98    inference(definition_unfolding,[],[f48,f49])).
% 3.72/0.98  
% 3.72/0.98  fof(f80,plain,(
% 3.72/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))))),
% 3.72/0.98    inference(definition_unfolding,[],[f70,f73])).
% 3.72/0.98  
% 3.72/0.98  fof(f11,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f22,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f11])).
% 3.72/0.98  
% 3.72/0.98  fof(f61,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f22])).
% 3.72/0.98  
% 3.72/0.98  fof(f9,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f20,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f9])).
% 3.72/0.98  
% 3.72/0.98  fof(f59,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f20])).
% 3.72/0.98  
% 3.72/0.98  fof(f5,axiom,(
% 3.72/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f15,plain,(
% 3.72/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/0.98    inference(ennf_transformation,[],[f5])).
% 3.72/0.98  
% 3.72/0.98  fof(f50,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f15])).
% 3.72/0.98  
% 3.72/0.98  fof(f2,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f27,plain,(
% 3.72/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.72/0.98    inference(nnf_transformation,[],[f2])).
% 3.72/0.98  
% 3.72/0.98  fof(f28,plain,(
% 3.72/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.72/0.98    inference(flattening,[],[f27])).
% 3.72/0.98  
% 3.72/0.98  fof(f29,plain,(
% 3.72/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.72/0.98    inference(rectify,[],[f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f30,plain,(
% 3.72/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f31,plain,(
% 3.72/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.72/0.98  
% 3.72/0.98  fof(f42,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f79,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.72/0.98    inference(definition_unfolding,[],[f42,f49])).
% 3.72/0.98  
% 3.72/0.98  fof(f86,plain,(
% 3.72/0.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 3.72/0.98    inference(equality_resolution,[],[f79])).
% 3.72/0.98  
% 3.72/0.98  fof(f68,plain,(
% 3.72/0.98    v1_funct_1(sK7)),
% 3.72/0.98    inference(cnf_transformation,[],[f40])).
% 3.72/0.98  
% 3.72/0.98  fof(f8,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f19,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f8])).
% 3.72/0.98  
% 3.72/0.98  fof(f58,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f19])).
% 3.72/0.98  
% 3.72/0.98  fof(f12,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f23,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f12])).
% 3.72/0.98  
% 3.72/0.98  fof(f24,plain,(
% 3.72/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(flattening,[],[f23])).
% 3.72/0.98  
% 3.72/0.98  fof(f38,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(nnf_transformation,[],[f24])).
% 3.72/0.98  
% 3.72/0.98  fof(f62,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f38])).
% 3.72/0.98  
% 3.72/0.98  fof(f10,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f21,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f10])).
% 3.72/0.98  
% 3.72/0.98  fof(f60,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f21])).
% 3.72/0.98  
% 3.72/0.98  fof(f69,plain,(
% 3.72/0.98    v1_funct_2(sK7,sK4,k1_tarski(sK5))),
% 3.72/0.98    inference(cnf_transformation,[],[f40])).
% 3.72/0.98  
% 3.72/0.98  fof(f81,plain,(
% 3.72/0.98    v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5))),
% 3.72/0.98    inference(definition_unfolding,[],[f69,f73])).
% 3.72/0.98  
% 3.72/0.98  fof(f43,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f78,plain,(
% 3.72/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.72/0.98    inference(definition_unfolding,[],[f43,f49])).
% 3.72/0.98  
% 3.72/0.98  fof(f84,plain,(
% 3.72/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 3.72/0.98    inference(equality_resolution,[],[f78])).
% 3.72/0.98  
% 3.72/0.98  fof(f85,plain,(
% 3.72/0.98    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 3.72/0.98    inference(equality_resolution,[],[f84])).
% 3.72/0.98  
% 3.72/0.98  fof(f7,axiom,(
% 3.72/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f18,plain,(
% 3.72/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.72/0.98    inference(ennf_transformation,[],[f7])).
% 3.72/0.98  
% 3.72/0.98  fof(f57,plain,(
% 3.72/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f18])).
% 3.72/0.98  
% 3.72/0.98  fof(f1,axiom,(
% 3.72/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.72/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f41,plain,(
% 3.72/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f1])).
% 3.72/0.98  
% 3.72/0.98  fof(f72,plain,(
% 3.72/0.98    k1_funct_1(sK7,sK6) != sK5),
% 3.72/0.98    inference(cnf_transformation,[],[f40])).
% 3.72/0.98  
% 3.72/0.98  cnf(c_26,negated_conjecture,
% 3.72/0.98      ( r2_hidden(sK6,sK4) ),
% 3.72/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_741,plain,
% 3.72/0.98      ( r2_hidden(sK6,sK4) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_11,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.72/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.72/0.98      | ~ v1_relat_1(X1)
% 3.72/0.98      | ~ v1_funct_1(X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_755,plain,
% 3.72/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.72/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.72/0.98      | v1_relat_1(X1) != iProver_top
% 3.72/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_27,negated_conjecture,
% 3.72/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) ),
% 3.72/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_740,plain,
% 3.72/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_18,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_748,plain,
% 3.72/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1366,plain,
% 3.72/0.98      ( k2_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k2_relat_1(sK7) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_740,c_748]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_16,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.72/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_750,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.72/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1885,plain,
% 3.72/0.98      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top
% 3.72/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1366,c_750]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_32,plain,
% 3.72/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2045,plain,
% 3.72/0.98      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k1_enumset1(sK5,sK5,sK5))) = iProver_top ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_1885,c_32]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/0.98      | ~ r2_hidden(X2,X0)
% 3.72/0.98      | r2_hidden(X2,X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_759,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.72/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2345,plain,
% 3.72/0.98      ( r2_hidden(X0,k1_enumset1(sK5,sK5,sK5)) = iProver_top
% 3.72/0.98      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2045,c_759]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_760,plain,
% 3.72/0.98      ( X0 = X1
% 3.72/0.98      | X0 = X2
% 3.72/0.98      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2897,plain,
% 3.72/0.98      ( sK5 = X0 | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_2345,c_760]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5312,plain,
% 3.72/0.98      ( k1_funct_1(sK7,X0) = sK5
% 3.72/0.98      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.72/0.98      | v1_relat_1(sK7) != iProver_top
% 3.72/0.98      | v1_funct_1(sK7) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_755,c_2897]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_29,negated_conjecture,
% 3.72/0.98      ( v1_funct_1(sK7) ),
% 3.72/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_30,plain,
% 3.72/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_15,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | v1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1030,plain,
% 3.72/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5))))
% 3.72/0.98      | v1_relat_1(sK7) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1031,plain,
% 3.72/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_enumset1(sK5,sK5,sK5)))) != iProver_top
% 3.72/0.98      | v1_relat_1(sK7) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7075,plain,
% 3.72/0.98      ( k1_funct_1(sK7,X0) = sK5
% 3.72/0.98      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_5312,c_30,c_32,c_1031]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_24,plain,
% 3.72/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.72/0.98      | k1_xboole_0 = X2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_742,plain,
% 3.72/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.72/0.98      | k1_xboole_0 = X1
% 3.72/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3910,plain,
% 3.72/0.98      ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = sK4
% 3.72/0.98      | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
% 3.72/0.98      | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_740,c_742]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_17,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_749,plain,
% 3.72/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1566,plain,
% 3.72/0.98      ( k1_relset_1(sK4,k1_enumset1(sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_740,c_749]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3914,plain,
% 3.72/0.98      ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
% 3.72/0.98      | k1_relat_1(sK7) = sK4
% 3.72/0.98      | v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) != iProver_top ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_3910,c_1566]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_28,negated_conjecture,
% 3.72/0.98      ( v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5)) ),
% 3.72/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3927,plain,
% 3.72/0.98      ( ~ v1_funct_2(sK7,sK4,k1_enumset1(sK5,sK5,sK5))
% 3.72/0.98      | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0
% 3.72/0.98      | k1_relat_1(sK7) = sK4 ),
% 3.72/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3914]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4248,plain,
% 3.72/0.98      ( k1_relat_1(sK7) = sK4 | k1_enumset1(sK5,sK5,sK5) = k1_xboole_0 ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_3914,c_28,c_3927]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4249,plain,
% 3.72/0.98      ( k1_enumset1(sK5,sK5,sK5) = k1_xboole_0 | k1_relat_1(sK7) = sK4 ),
% 3.72/0.98      inference(renaming,[status(thm)],[c_4248]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5,plain,
% 3.72/0.98      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 3.72/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_761,plain,
% 3.72/0.98      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_14,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_752,plain,
% 3.72/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.72/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1211,plain,
% 3.72/0.98      ( r1_tarski(k1_enumset1(X0,X0,X1),X0) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_761,c_752]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4252,plain,
% 3.72/0.98      ( k1_relat_1(sK7) = sK4
% 3.72/0.98      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_4249,c_1211]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_0,plain,
% 3.72/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_766,plain,
% 3.72/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6914,plain,
% 3.72/0.98      ( k1_relat_1(sK7) = sK4 ),
% 3.72/0.98      inference(forward_subsumption_resolution,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_4252,c_766]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7081,plain,
% 3.72/0.98      ( k1_funct_1(sK7,X0) = sK5 | r2_hidden(X0,sK4) != iProver_top ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_7075,c_6914]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7090,plain,
% 3.72/0.98      ( k1_funct_1(sK7,sK6) = sK5 ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_741,c_7081]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_25,negated_conjecture,
% 3.72/0.98      ( k1_funct_1(sK7,sK6) != sK5 ),
% 3.72/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(contradiction,plain,
% 3.72/0.98      ( $false ),
% 3.72/0.98      inference(minisat,[status(thm)],[c_7090,c_25]) ).
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  ------                               Statistics
% 3.72/0.98  
% 3.72/0.98  ------ Selected
% 3.72/0.98  
% 3.72/0.98  total_time:                             0.246
% 3.72/0.98  
%------------------------------------------------------------------------------
