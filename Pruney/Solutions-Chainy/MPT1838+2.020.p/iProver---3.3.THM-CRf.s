%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:34 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 227 expanded)
%              Number of clauses        :   57 (  70 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 ( 969 expanded)
%              Number of equality atoms :  153 ( 250 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK5 != X0
        & r1_tarski(X0,sK5)
        & v1_zfmisc_1(sK5)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r1_tarski(sK4,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( sK4 != sK5
    & r1_tarski(sK4,sK5)
    & v1_zfmisc_1(sK5)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f42,f41])).

fof(f70,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f60])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( X0 = X1
    | k2_tarski(X2,X2) != k2_xboole_0(X0,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1136,plain,
    ( X0 = sK5
    | k2_tarski(X1,X1) != k2_xboole_0(X0,sK5)
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2314,plain,
    ( k2_tarski(X0,X0) != k2_xboole_0(sK4,sK5)
    | sK4 = sK5
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_12428,plain,
    ( k2_tarski(sK3(sK5),sK3(sK5)) != k2_xboole_0(sK4,sK5)
    | sK4 = sK5
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_2314])).

cnf(c_465,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3714,plain,
    ( k2_tarski(X0,X0) != X1
    | k2_tarski(X0,X0) = k2_xboole_0(sK4,sK5)
    | k2_xboole_0(sK4,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_10120,plain,
    ( k2_tarski(sK3(sK5),sK3(sK5)) = k2_xboole_0(sK4,sK5)
    | k2_tarski(sK3(sK5),sK3(sK5)) != sK5
    | k2_xboole_0(sK4,sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_3714])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_757,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_750,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1888,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(X0,X1),X2),X1) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_750])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_746,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_756,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1789,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_756])).

cnf(c_4867,plain,
    ( r1_tarski(k2_xboole_0(sK4,X0),X1) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(sK4,X0),X1),X0) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(sK4,X0),X1),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_1789])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_758,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5225,plain,
    ( r1_tarski(k2_xboole_0(sK4,X0),sK5) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(sK4,X0),sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4867,c_758])).

cnf(c_5696,plain,
    ( r1_tarski(k2_xboole_0(sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5225,c_758])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_752,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1781,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k2_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_752,c_758])).

cnf(c_3385,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_1781])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_749,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3478,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(k2_xboole_0(X0,X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3385,c_749])).

cnf(c_8736,plain,
    ( k2_xboole_0(sK4,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_5696,c_3478])).

cnf(c_464,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1139,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_983,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_797,plain,
    ( sK4 != X0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_910,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_793,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_885,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_21,plain,
    ( m1_subset_1(sK3(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_256,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | sK3(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_257,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = k2_tarski(sK3(X0),sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_24,negated_conjecture,
    ( v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_273,plain,
    ( v1_xboole_0(X0)
    | k2_tarski(sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_24])).

cnf(c_274,plain,
    ( v1_xboole_0(sK5)
    | k2_tarski(sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_276,plain,
    ( k2_tarski(sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_25])).

cnf(c_20,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_281,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_282,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_284,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_25])).

cnf(c_759,plain,
    ( k2_tarski(sK3(sK5),sK3(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_276,c_284])).

cnf(c_11,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_330,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_326,plain,
    ( sK5 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_22,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12428,c_10120,c_8736,c_1139,c_983,c_910,c_885,c_759,c_330,c_326,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:24:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.56/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/1.00  
% 3.56/1.00  ------  iProver source info
% 3.56/1.00  
% 3.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/1.00  git: non_committed_changes: false
% 3.56/1.00  git: last_make_outside_of_git: false
% 3.56/1.00  
% 3.56/1.00  ------ 
% 3.56/1.00  
% 3.56/1.00  ------ Input Options
% 3.56/1.00  
% 3.56/1.00  --out_options                           all
% 3.56/1.00  --tptp_safe_out                         true
% 3.56/1.00  --problem_path                          ""
% 3.56/1.00  --include_path                          ""
% 3.56/1.00  --clausifier                            res/vclausify_rel
% 3.56/1.00  --clausifier_options                    ""
% 3.56/1.00  --stdin                                 false
% 3.56/1.00  --stats_out                             all
% 3.56/1.00  
% 3.56/1.00  ------ General Options
% 3.56/1.00  
% 3.56/1.00  --fof                                   false
% 3.56/1.00  --time_out_real                         305.
% 3.56/1.00  --time_out_virtual                      -1.
% 3.56/1.00  --symbol_type_check                     false
% 3.56/1.00  --clausify_out                          false
% 3.56/1.00  --sig_cnt_out                           false
% 3.56/1.00  --trig_cnt_out                          false
% 3.56/1.00  --trig_cnt_out_tolerance                1.
% 3.56/1.00  --trig_cnt_out_sk_spl                   false
% 3.56/1.00  --abstr_cl_out                          false
% 3.56/1.00  
% 3.56/1.00  ------ Global Options
% 3.56/1.00  
% 3.56/1.00  --schedule                              default
% 3.56/1.00  --add_important_lit                     false
% 3.56/1.00  --prop_solver_per_cl                    1000
% 3.56/1.00  --min_unsat_core                        false
% 3.56/1.00  --soft_assumptions                      false
% 3.56/1.00  --soft_lemma_size                       3
% 3.56/1.00  --prop_impl_unit_size                   0
% 3.56/1.00  --prop_impl_unit                        []
% 3.56/1.00  --share_sel_clauses                     true
% 3.56/1.00  --reset_solvers                         false
% 3.56/1.00  --bc_imp_inh                            [conj_cone]
% 3.56/1.00  --conj_cone_tolerance                   3.
% 3.56/1.00  --extra_neg_conj                        none
% 3.56/1.00  --large_theory_mode                     true
% 3.56/1.00  --prolific_symb_bound                   200
% 3.56/1.00  --lt_threshold                          2000
% 3.56/1.00  --clause_weak_htbl                      true
% 3.56/1.00  --gc_record_bc_elim                     false
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing Options
% 3.56/1.00  
% 3.56/1.00  --preprocessing_flag                    true
% 3.56/1.00  --time_out_prep_mult                    0.1
% 3.56/1.00  --splitting_mode                        input
% 3.56/1.00  --splitting_grd                         true
% 3.56/1.00  --splitting_cvd                         false
% 3.56/1.00  --splitting_cvd_svl                     false
% 3.56/1.00  --splitting_nvd                         32
% 3.56/1.00  --sub_typing                            true
% 3.56/1.00  --prep_gs_sim                           true
% 3.56/1.00  --prep_unflatten                        true
% 3.56/1.00  --prep_res_sim                          true
% 3.56/1.00  --prep_upred                            true
% 3.56/1.00  --prep_sem_filter                       exhaustive
% 3.56/1.00  --prep_sem_filter_out                   false
% 3.56/1.00  --pred_elim                             true
% 3.56/1.00  --res_sim_input                         true
% 3.56/1.00  --eq_ax_congr_red                       true
% 3.56/1.00  --pure_diseq_elim                       true
% 3.56/1.00  --brand_transform                       false
% 3.56/1.00  --non_eq_to_eq                          false
% 3.56/1.00  --prep_def_merge                        true
% 3.56/1.00  --prep_def_merge_prop_impl              false
% 3.56/1.00  --prep_def_merge_mbd                    true
% 3.56/1.00  --prep_def_merge_tr_red                 false
% 3.56/1.00  --prep_def_merge_tr_cl                  false
% 3.56/1.00  --smt_preprocessing                     true
% 3.56/1.00  --smt_ac_axioms                         fast
% 3.56/1.00  --preprocessed_out                      false
% 3.56/1.00  --preprocessed_stats                    false
% 3.56/1.00  
% 3.56/1.00  ------ Abstraction refinement Options
% 3.56/1.00  
% 3.56/1.00  --abstr_ref                             []
% 3.56/1.00  --abstr_ref_prep                        false
% 3.56/1.00  --abstr_ref_until_sat                   false
% 3.56/1.00  --abstr_ref_sig_restrict                funpre
% 3.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.00  --abstr_ref_under                       []
% 3.56/1.00  
% 3.56/1.00  ------ SAT Options
% 3.56/1.00  
% 3.56/1.00  --sat_mode                              false
% 3.56/1.00  --sat_fm_restart_options                ""
% 3.56/1.00  --sat_gr_def                            false
% 3.56/1.00  --sat_epr_types                         true
% 3.56/1.00  --sat_non_cyclic_types                  false
% 3.56/1.00  --sat_finite_models                     false
% 3.56/1.00  --sat_fm_lemmas                         false
% 3.56/1.00  --sat_fm_prep                           false
% 3.56/1.00  --sat_fm_uc_incr                        true
% 3.56/1.00  --sat_out_model                         small
% 3.56/1.00  --sat_out_clauses                       false
% 3.56/1.00  
% 3.56/1.00  ------ QBF Options
% 3.56/1.00  
% 3.56/1.00  --qbf_mode                              false
% 3.56/1.00  --qbf_elim_univ                         false
% 3.56/1.00  --qbf_dom_inst                          none
% 3.56/1.00  --qbf_dom_pre_inst                      false
% 3.56/1.00  --qbf_sk_in                             false
% 3.56/1.00  --qbf_pred_elim                         true
% 3.56/1.00  --qbf_split                             512
% 3.56/1.00  
% 3.56/1.00  ------ BMC1 Options
% 3.56/1.00  
% 3.56/1.00  --bmc1_incremental                      false
% 3.56/1.00  --bmc1_axioms                           reachable_all
% 3.56/1.00  --bmc1_min_bound                        0
% 3.56/1.00  --bmc1_max_bound                        -1
% 3.56/1.00  --bmc1_max_bound_default                -1
% 3.56/1.00  --bmc1_symbol_reachability              true
% 3.56/1.00  --bmc1_property_lemmas                  false
% 3.56/1.00  --bmc1_k_induction                      false
% 3.56/1.00  --bmc1_non_equiv_states                 false
% 3.56/1.00  --bmc1_deadlock                         false
% 3.56/1.00  --bmc1_ucm                              false
% 3.56/1.00  --bmc1_add_unsat_core                   none
% 3.56/1.00  --bmc1_unsat_core_children              false
% 3.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.00  --bmc1_out_stat                         full
% 3.56/1.00  --bmc1_ground_init                      false
% 3.56/1.00  --bmc1_pre_inst_next_state              false
% 3.56/1.00  --bmc1_pre_inst_state                   false
% 3.56/1.00  --bmc1_pre_inst_reach_state             false
% 3.56/1.00  --bmc1_out_unsat_core                   false
% 3.56/1.00  --bmc1_aig_witness_out                  false
% 3.56/1.00  --bmc1_verbose                          false
% 3.56/1.00  --bmc1_dump_clauses_tptp                false
% 3.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.00  --bmc1_dump_file                        -
% 3.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.00  --bmc1_ucm_extend_mode                  1
% 3.56/1.00  --bmc1_ucm_init_mode                    2
% 3.56/1.00  --bmc1_ucm_cone_mode                    none
% 3.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.00  --bmc1_ucm_relax_model                  4
% 3.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.00  --bmc1_ucm_layered_model                none
% 3.56/1.00  --bmc1_ucm_max_lemma_size               10
% 3.56/1.00  
% 3.56/1.00  ------ AIG Options
% 3.56/1.00  
% 3.56/1.00  --aig_mode                              false
% 3.56/1.00  
% 3.56/1.00  ------ Instantiation Options
% 3.56/1.00  
% 3.56/1.00  --instantiation_flag                    true
% 3.56/1.00  --inst_sos_flag                         true
% 3.56/1.00  --inst_sos_phase                        true
% 3.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel_side                     num_symb
% 3.56/1.00  --inst_solver_per_active                1400
% 3.56/1.00  --inst_solver_calls_frac                1.
% 3.56/1.00  --inst_passive_queue_type               priority_queues
% 3.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.00  --inst_passive_queues_freq              [25;2]
% 3.56/1.00  --inst_dismatching                      true
% 3.56/1.00  --inst_eager_unprocessed_to_passive     true
% 3.56/1.00  --inst_prop_sim_given                   true
% 3.56/1.00  --inst_prop_sim_new                     false
% 3.56/1.00  --inst_subs_new                         false
% 3.56/1.00  --inst_eq_res_simp                      false
% 3.56/1.00  --inst_subs_given                       false
% 3.56/1.00  --inst_orphan_elimination               true
% 3.56/1.00  --inst_learning_loop_flag               true
% 3.56/1.00  --inst_learning_start                   3000
% 3.56/1.00  --inst_learning_factor                  2
% 3.56/1.00  --inst_start_prop_sim_after_learn       3
% 3.56/1.00  --inst_sel_renew                        solver
% 3.56/1.00  --inst_lit_activity_flag                true
% 3.56/1.00  --inst_restr_to_given                   false
% 3.56/1.00  --inst_activity_threshold               500
% 3.56/1.00  --inst_out_proof                        true
% 3.56/1.00  
% 3.56/1.00  ------ Resolution Options
% 3.56/1.00  
% 3.56/1.00  --resolution_flag                       true
% 3.56/1.00  --res_lit_sel                           adaptive
% 3.56/1.00  --res_lit_sel_side                      none
% 3.56/1.00  --res_ordering                          kbo
% 3.56/1.00  --res_to_prop_solver                    active
% 3.56/1.00  --res_prop_simpl_new                    false
% 3.56/1.00  --res_prop_simpl_given                  true
% 3.56/1.00  --res_passive_queue_type                priority_queues
% 3.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.00  --res_passive_queues_freq               [15;5]
% 3.56/1.00  --res_forward_subs                      full
% 3.56/1.00  --res_backward_subs                     full
% 3.56/1.00  --res_forward_subs_resolution           true
% 3.56/1.00  --res_backward_subs_resolution          true
% 3.56/1.00  --res_orphan_elimination                true
% 3.56/1.00  --res_time_limit                        2.
% 3.56/1.00  --res_out_proof                         true
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Options
% 3.56/1.00  
% 3.56/1.00  --superposition_flag                    true
% 3.56/1.00  --sup_passive_queue_type                priority_queues
% 3.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.56/1.00  --demod_completeness_check              fast
% 3.56/1.00  --demod_use_ground                      true
% 3.56/1.00  --sup_to_prop_solver                    passive
% 3.56/1.00  --sup_prop_simpl_new                    true
% 3.56/1.00  --sup_prop_simpl_given                  true
% 3.56/1.00  --sup_fun_splitting                     true
% 3.56/1.00  --sup_smt_interval                      50000
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Simplification Setup
% 3.56/1.00  
% 3.56/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.56/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.56/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.56/1.00  --sup_immed_triv                        [TrivRules]
% 3.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_immed_bw_main                     []
% 3.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_input_bw                          []
% 3.56/1.00  
% 3.56/1.00  ------ Combination Options
% 3.56/1.00  
% 3.56/1.00  --comb_res_mult                         3
% 3.56/1.00  --comb_sup_mult                         2
% 3.56/1.00  --comb_inst_mult                        10
% 3.56/1.00  
% 3.56/1.00  ------ Debug Options
% 3.56/1.00  
% 3.56/1.00  --dbg_backtrace                         false
% 3.56/1.00  --dbg_dump_prop_clauses                 false
% 3.56/1.00  --dbg_dump_prop_clauses_file            -
% 3.56/1.00  --dbg_out_stat                          false
% 3.56/1.00  ------ Parsing...
% 3.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  ------ Proving...
% 3.56/1.00  ------ Problem Properties 
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  clauses                                 24
% 3.56/1.00  conjectures                             2
% 3.56/1.00  EPR                                     9
% 3.56/1.00  Horn                                    20
% 3.56/1.00  unary                                   11
% 3.56/1.00  binary                                  6
% 3.56/1.00  lits                                    46
% 3.56/1.00  lits eq                                 14
% 3.56/1.00  fd_pure                                 0
% 3.56/1.00  fd_pseudo                               0
% 3.56/1.00  fd_cond                                 0
% 3.56/1.00  fd_pseudo_cond                          5
% 3.56/1.00  AC symbols                              0
% 3.56/1.00  
% 3.56/1.00  ------ Schedule dynamic 5 is on 
% 3.56/1.00  
% 3.56/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ 
% 3.56/1.00  Current options:
% 3.56/1.00  ------ 
% 3.56/1.00  
% 3.56/1.00  ------ Input Options
% 3.56/1.00  
% 3.56/1.00  --out_options                           all
% 3.56/1.00  --tptp_safe_out                         true
% 3.56/1.00  --problem_path                          ""
% 3.56/1.00  --include_path                          ""
% 3.56/1.00  --clausifier                            res/vclausify_rel
% 3.56/1.00  --clausifier_options                    ""
% 3.56/1.00  --stdin                                 false
% 3.56/1.00  --stats_out                             all
% 3.56/1.00  
% 3.56/1.00  ------ General Options
% 3.56/1.00  
% 3.56/1.00  --fof                                   false
% 3.56/1.00  --time_out_real                         305.
% 3.56/1.00  --time_out_virtual                      -1.
% 3.56/1.00  --symbol_type_check                     false
% 3.56/1.00  --clausify_out                          false
% 3.56/1.00  --sig_cnt_out                           false
% 3.56/1.00  --trig_cnt_out                          false
% 3.56/1.00  --trig_cnt_out_tolerance                1.
% 3.56/1.00  --trig_cnt_out_sk_spl                   false
% 3.56/1.00  --abstr_cl_out                          false
% 3.56/1.00  
% 3.56/1.00  ------ Global Options
% 3.56/1.00  
% 3.56/1.00  --schedule                              default
% 3.56/1.00  --add_important_lit                     false
% 3.56/1.00  --prop_solver_per_cl                    1000
% 3.56/1.00  --min_unsat_core                        false
% 3.56/1.00  --soft_assumptions                      false
% 3.56/1.00  --soft_lemma_size                       3
% 3.56/1.00  --prop_impl_unit_size                   0
% 3.56/1.00  --prop_impl_unit                        []
% 3.56/1.00  --share_sel_clauses                     true
% 3.56/1.00  --reset_solvers                         false
% 3.56/1.00  --bc_imp_inh                            [conj_cone]
% 3.56/1.00  --conj_cone_tolerance                   3.
% 3.56/1.00  --extra_neg_conj                        none
% 3.56/1.00  --large_theory_mode                     true
% 3.56/1.00  --prolific_symb_bound                   200
% 3.56/1.00  --lt_threshold                          2000
% 3.56/1.00  --clause_weak_htbl                      true
% 3.56/1.00  --gc_record_bc_elim                     false
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing Options
% 3.56/1.00  
% 3.56/1.00  --preprocessing_flag                    true
% 3.56/1.00  --time_out_prep_mult                    0.1
% 3.56/1.00  --splitting_mode                        input
% 3.56/1.00  --splitting_grd                         true
% 3.56/1.00  --splitting_cvd                         false
% 3.56/1.00  --splitting_cvd_svl                     false
% 3.56/1.00  --splitting_nvd                         32
% 3.56/1.00  --sub_typing                            true
% 3.56/1.00  --prep_gs_sim                           true
% 3.56/1.00  --prep_unflatten                        true
% 3.56/1.00  --prep_res_sim                          true
% 3.56/1.00  --prep_upred                            true
% 3.56/1.00  --prep_sem_filter                       exhaustive
% 3.56/1.00  --prep_sem_filter_out                   false
% 3.56/1.00  --pred_elim                             true
% 3.56/1.00  --res_sim_input                         true
% 3.56/1.00  --eq_ax_congr_red                       true
% 3.56/1.00  --pure_diseq_elim                       true
% 3.56/1.00  --brand_transform                       false
% 3.56/1.00  --non_eq_to_eq                          false
% 3.56/1.00  --prep_def_merge                        true
% 3.56/1.00  --prep_def_merge_prop_impl              false
% 3.56/1.00  --prep_def_merge_mbd                    true
% 3.56/1.00  --prep_def_merge_tr_red                 false
% 3.56/1.00  --prep_def_merge_tr_cl                  false
% 3.56/1.00  --smt_preprocessing                     true
% 3.56/1.00  --smt_ac_axioms                         fast
% 3.56/1.00  --preprocessed_out                      false
% 3.56/1.00  --preprocessed_stats                    false
% 3.56/1.00  
% 3.56/1.00  ------ Abstraction refinement Options
% 3.56/1.00  
% 3.56/1.00  --abstr_ref                             []
% 3.56/1.00  --abstr_ref_prep                        false
% 3.56/1.00  --abstr_ref_until_sat                   false
% 3.56/1.00  --abstr_ref_sig_restrict                funpre
% 3.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.00  --abstr_ref_under                       []
% 3.56/1.00  
% 3.56/1.00  ------ SAT Options
% 3.56/1.00  
% 3.56/1.00  --sat_mode                              false
% 3.56/1.00  --sat_fm_restart_options                ""
% 3.56/1.00  --sat_gr_def                            false
% 3.56/1.00  --sat_epr_types                         true
% 3.56/1.00  --sat_non_cyclic_types                  false
% 3.56/1.00  --sat_finite_models                     false
% 3.56/1.00  --sat_fm_lemmas                         false
% 3.56/1.00  --sat_fm_prep                           false
% 3.56/1.00  --sat_fm_uc_incr                        true
% 3.56/1.00  --sat_out_model                         small
% 3.56/1.00  --sat_out_clauses                       false
% 3.56/1.00  
% 3.56/1.00  ------ QBF Options
% 3.56/1.00  
% 3.56/1.00  --qbf_mode                              false
% 3.56/1.00  --qbf_elim_univ                         false
% 3.56/1.00  --qbf_dom_inst                          none
% 3.56/1.00  --qbf_dom_pre_inst                      false
% 3.56/1.00  --qbf_sk_in                             false
% 3.56/1.00  --qbf_pred_elim                         true
% 3.56/1.00  --qbf_split                             512
% 3.56/1.00  
% 3.56/1.00  ------ BMC1 Options
% 3.56/1.00  
% 3.56/1.00  --bmc1_incremental                      false
% 3.56/1.00  --bmc1_axioms                           reachable_all
% 3.56/1.00  --bmc1_min_bound                        0
% 3.56/1.00  --bmc1_max_bound                        -1
% 3.56/1.00  --bmc1_max_bound_default                -1
% 3.56/1.00  --bmc1_symbol_reachability              true
% 3.56/1.00  --bmc1_property_lemmas                  false
% 3.56/1.00  --bmc1_k_induction                      false
% 3.56/1.00  --bmc1_non_equiv_states                 false
% 3.56/1.00  --bmc1_deadlock                         false
% 3.56/1.00  --bmc1_ucm                              false
% 3.56/1.00  --bmc1_add_unsat_core                   none
% 3.56/1.00  --bmc1_unsat_core_children              false
% 3.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.00  --bmc1_out_stat                         full
% 3.56/1.00  --bmc1_ground_init                      false
% 3.56/1.00  --bmc1_pre_inst_next_state              false
% 3.56/1.00  --bmc1_pre_inst_state                   false
% 3.56/1.00  --bmc1_pre_inst_reach_state             false
% 3.56/1.00  --bmc1_out_unsat_core                   false
% 3.56/1.00  --bmc1_aig_witness_out                  false
% 3.56/1.00  --bmc1_verbose                          false
% 3.56/1.00  --bmc1_dump_clauses_tptp                false
% 3.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.00  --bmc1_dump_file                        -
% 3.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.00  --bmc1_ucm_extend_mode                  1
% 3.56/1.00  --bmc1_ucm_init_mode                    2
% 3.56/1.00  --bmc1_ucm_cone_mode                    none
% 3.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.00  --bmc1_ucm_relax_model                  4
% 3.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.00  --bmc1_ucm_layered_model                none
% 3.56/1.00  --bmc1_ucm_max_lemma_size               10
% 3.56/1.00  
% 3.56/1.00  ------ AIG Options
% 3.56/1.00  
% 3.56/1.00  --aig_mode                              false
% 3.56/1.00  
% 3.56/1.00  ------ Instantiation Options
% 3.56/1.00  
% 3.56/1.00  --instantiation_flag                    true
% 3.56/1.00  --inst_sos_flag                         true
% 3.56/1.00  --inst_sos_phase                        true
% 3.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel_side                     none
% 3.56/1.00  --inst_solver_per_active                1400
% 3.56/1.00  --inst_solver_calls_frac                1.
% 3.56/1.00  --inst_passive_queue_type               priority_queues
% 3.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.00  --inst_passive_queues_freq              [25;2]
% 3.56/1.00  --inst_dismatching                      true
% 3.56/1.00  --inst_eager_unprocessed_to_passive     true
% 3.56/1.00  --inst_prop_sim_given                   true
% 3.56/1.00  --inst_prop_sim_new                     false
% 3.56/1.00  --inst_subs_new                         false
% 3.56/1.00  --inst_eq_res_simp                      false
% 3.56/1.00  --inst_subs_given                       false
% 3.56/1.00  --inst_orphan_elimination               true
% 3.56/1.00  --inst_learning_loop_flag               true
% 3.56/1.00  --inst_learning_start                   3000
% 3.56/1.00  --inst_learning_factor                  2
% 3.56/1.00  --inst_start_prop_sim_after_learn       3
% 3.56/1.00  --inst_sel_renew                        solver
% 3.56/1.00  --inst_lit_activity_flag                true
% 3.56/1.00  --inst_restr_to_given                   false
% 3.56/1.00  --inst_activity_threshold               500
% 3.56/1.00  --inst_out_proof                        true
% 3.56/1.00  
% 3.56/1.00  ------ Resolution Options
% 3.56/1.00  
% 3.56/1.00  --resolution_flag                       false
% 3.56/1.00  --res_lit_sel                           adaptive
% 3.56/1.00  --res_lit_sel_side                      none
% 3.56/1.00  --res_ordering                          kbo
% 3.56/1.00  --res_to_prop_solver                    active
% 3.56/1.00  --res_prop_simpl_new                    false
% 3.56/1.00  --res_prop_simpl_given                  true
% 3.56/1.00  --res_passive_queue_type                priority_queues
% 3.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.00  --res_passive_queues_freq               [15;5]
% 3.56/1.00  --res_forward_subs                      full
% 3.56/1.00  --res_backward_subs                     full
% 3.56/1.00  --res_forward_subs_resolution           true
% 3.56/1.00  --res_backward_subs_resolution          true
% 3.56/1.00  --res_orphan_elimination                true
% 3.56/1.00  --res_time_limit                        2.
% 3.56/1.00  --res_out_proof                         true
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Options
% 3.56/1.00  
% 3.56/1.00  --superposition_flag                    true
% 3.56/1.00  --sup_passive_queue_type                priority_queues
% 3.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.56/1.00  --demod_completeness_check              fast
% 3.56/1.00  --demod_use_ground                      true
% 3.56/1.00  --sup_to_prop_solver                    passive
% 3.56/1.00  --sup_prop_simpl_new                    true
% 3.56/1.00  --sup_prop_simpl_given                  true
% 3.56/1.00  --sup_fun_splitting                     true
% 3.56/1.00  --sup_smt_interval                      50000
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Simplification Setup
% 3.56/1.00  
% 3.56/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.56/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.56/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.56/1.00  --sup_immed_triv                        [TrivRules]
% 3.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_immed_bw_main                     []
% 3.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_input_bw                          []
% 3.56/1.00  
% 3.56/1.00  ------ Combination Options
% 3.56/1.00  
% 3.56/1.00  --comb_res_mult                         3
% 3.56/1.00  --comb_sup_mult                         2
% 3.56/1.00  --comb_inst_mult                        10
% 3.56/1.00  
% 3.56/1.00  ------ Debug Options
% 3.56/1.00  
% 3.56/1.00  --dbg_backtrace                         false
% 3.56/1.00  --dbg_dump_prop_clauses                 false
% 3.56/1.00  --dbg_dump_prop_clauses_file            -
% 3.56/1.00  --dbg_out_stat                          false
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS status Theorem for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  fof(f8,axiom,(
% 3.56/1.00    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f15,plain,(
% 3.56/1.00    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f8])).
% 3.56/1.00  
% 3.56/1.00  fof(f61,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f15])).
% 3.56/1.00  
% 3.56/1.00  fof(f7,axiom,(
% 3.56/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f60,plain,(
% 3.56/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f7])).
% 3.56/1.00  
% 3.56/1.00  fof(f72,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k2_tarski(X0,X0)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f61,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f2,axiom,(
% 3.56/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f14,plain,(
% 3.56/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.56/1.00    inference(ennf_transformation,[],[f2])).
% 3.56/1.00  
% 3.56/1.00  fof(f26,plain,(
% 3.56/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.56/1.00    inference(nnf_transformation,[],[f14])).
% 3.56/1.00  
% 3.56/1.00  fof(f27,plain,(
% 3.56/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.56/1.00    inference(rectify,[],[f26])).
% 3.56/1.00  
% 3.56/1.00  fof(f28,plain,(
% 3.56/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f29,plain,(
% 3.56/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 3.56/1.00  
% 3.56/1.00  fof(f47,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f29])).
% 3.56/1.00  
% 3.56/1.00  fof(f3,axiom,(
% 3.56/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f30,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/1.00    inference(nnf_transformation,[],[f3])).
% 3.56/1.00  
% 3.56/1.00  fof(f31,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/1.00    inference(flattening,[],[f30])).
% 3.56/1.00  
% 3.56/1.00  fof(f32,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/1.00    inference(rectify,[],[f31])).
% 3.56/1.00  
% 3.56/1.00  fof(f33,plain,(
% 3.56/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f34,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 3.56/1.00  
% 3.56/1.00  fof(f49,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.56/1.00    inference(cnf_transformation,[],[f34])).
% 3.56/1.00  
% 3.56/1.00  fof(f76,plain,(
% 3.56/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.56/1.00    inference(equality_resolution,[],[f49])).
% 3.56/1.00  
% 3.56/1.00  fof(f12,conjecture,(
% 3.56/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f13,negated_conjecture,(
% 3.56/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.56/1.00    inference(negated_conjecture,[],[f12])).
% 3.56/1.00  
% 3.56/1.00  fof(f20,plain,(
% 3.56/1.00    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f13])).
% 3.56/1.00  
% 3.56/1.00  fof(f21,plain,(
% 3.56/1.00    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.56/1.00    inference(flattening,[],[f20])).
% 3.56/1.00  
% 3.56/1.00  fof(f42,plain,(
% 3.56/1.00    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK5 != X0 & r1_tarski(X0,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5))) )),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f41,plain,(
% 3.56/1.00    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK4 != X1 & r1_tarski(sK4,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f43,plain,(
% 3.56/1.00    (sK4 != sK5 & r1_tarski(sK4,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 3.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f42,f41])).
% 3.56/1.00  
% 3.56/1.00  fof(f70,plain,(
% 3.56/1.00    r1_tarski(sK4,sK5)),
% 3.56/1.00    inference(cnf_transformation,[],[f43])).
% 3.56/1.00  
% 3.56/1.00  fof(f46,plain,(
% 3.56/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f29])).
% 3.56/1.00  
% 3.56/1.00  fof(f48,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f29])).
% 3.56/1.00  
% 3.56/1.00  fof(f51,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.56/1.00    inference(cnf_transformation,[],[f34])).
% 3.56/1.00  
% 3.56/1.00  fof(f74,plain,(
% 3.56/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.56/1.00    inference(equality_resolution,[],[f51])).
% 3.56/1.00  
% 3.56/1.00  fof(f5,axiom,(
% 3.56/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f35,plain,(
% 3.56/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.00    inference(nnf_transformation,[],[f5])).
% 3.56/1.00  
% 3.56/1.00  fof(f36,plain,(
% 3.56/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.00    inference(flattening,[],[f35])).
% 3.56/1.00  
% 3.56/1.00  fof(f58,plain,(
% 3.56/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f36])).
% 3.56/1.00  
% 3.56/1.00  fof(f10,axiom,(
% 3.56/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f17,plain,(
% 3.56/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.56/1.00    inference(ennf_transformation,[],[f10])).
% 3.56/1.00  
% 3.56/1.00  fof(f18,plain,(
% 3.56/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.56/1.00    inference(flattening,[],[f17])).
% 3.56/1.00  
% 3.56/1.00  fof(f63,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f18])).
% 3.56/1.00  
% 3.56/1.00  fof(f73,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f63,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f11,axiom,(
% 3.56/1.00    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f19,plain,(
% 3.56/1.00    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f11])).
% 3.56/1.00  
% 3.56/1.00  fof(f37,plain,(
% 3.56/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.56/1.00    inference(nnf_transformation,[],[f19])).
% 3.56/1.00  
% 3.56/1.00  fof(f38,plain,(
% 3.56/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.56/1.00    inference(rectify,[],[f37])).
% 3.56/1.00  
% 3.56/1.00  fof(f39,plain,(
% 3.56/1.00    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f40,plain,(
% 3.56/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 3.56/1.00  
% 3.56/1.00  fof(f64,plain,(
% 3.56/1.00    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f40])).
% 3.56/1.00  
% 3.56/1.00  fof(f69,plain,(
% 3.56/1.00    v1_zfmisc_1(sK5)),
% 3.56/1.00    inference(cnf_transformation,[],[f43])).
% 3.56/1.00  
% 3.56/1.00  fof(f68,plain,(
% 3.56/1.00    ~v1_xboole_0(sK5)),
% 3.56/1.00    inference(cnf_transformation,[],[f43])).
% 3.56/1.00  
% 3.56/1.00  fof(f65,plain,(
% 3.56/1.00    ( ! [X0] : (k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f40])).
% 3.56/1.00  
% 3.56/1.00  fof(f4,axiom,(
% 3.56/1.00    v1_xboole_0(k1_xboole_0)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f55,plain,(
% 3.56/1.00    v1_xboole_0(k1_xboole_0)),
% 3.56/1.00    inference(cnf_transformation,[],[f4])).
% 3.56/1.00  
% 3.56/1.00  fof(f67,plain,(
% 3.56/1.00    ~v1_xboole_0(sK4)),
% 3.56/1.00    inference(cnf_transformation,[],[f43])).
% 3.56/1.00  
% 3.56/1.00  fof(f71,plain,(
% 3.56/1.00    sK4 != sK5),
% 3.56/1.00    inference(cnf_transformation,[],[f43])).
% 3.56/1.00  
% 3.56/1.00  cnf(c_16,plain,
% 3.56/1.00      ( X0 = X1
% 3.56/1.00      | k2_tarski(X2,X2) != k2_xboole_0(X0,X1)
% 3.56/1.00      | k1_xboole_0 = X1
% 3.56/1.00      | k1_xboole_0 = X0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1136,plain,
% 3.56/1.00      ( X0 = sK5
% 3.56/1.00      | k2_tarski(X1,X1) != k2_xboole_0(X0,sK5)
% 3.56/1.00      | k1_xboole_0 = X0
% 3.56/1.00      | k1_xboole_0 = sK5 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_2314,plain,
% 3.56/1.00      ( k2_tarski(X0,X0) != k2_xboole_0(sK4,sK5)
% 3.56/1.00      | sK4 = sK5
% 3.56/1.00      | k1_xboole_0 = sK5
% 3.56/1.00      | k1_xboole_0 = sK4 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_1136]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_12428,plain,
% 3.56/1.00      ( k2_tarski(sK3(sK5),sK3(sK5)) != k2_xboole_0(sK4,sK5)
% 3.56/1.00      | sK4 = sK5
% 3.56/1.00      | k1_xboole_0 = sK5
% 3.56/1.00      | k1_xboole_0 = sK4 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_2314]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_465,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3714,plain,
% 3.56/1.00      ( k2_tarski(X0,X0) != X1
% 3.56/1.00      | k2_tarski(X0,X0) = k2_xboole_0(sK4,sK5)
% 3.56/1.00      | k2_xboole_0(sK4,sK5) != X1 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_465]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_10120,plain,
% 3.56/1.00      ( k2_tarski(sK3(sK5),sK3(sK5)) = k2_xboole_0(sK4,sK5)
% 3.56/1.00      | k2_tarski(sK3(sK5),sK3(sK5)) != sK5
% 3.56/1.00      | k2_xboole_0(sK4,sK5) != sK5 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_3714]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3,plain,
% 3.56/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_757,plain,
% 3.56/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_10,plain,
% 3.56/1.00      ( r2_hidden(X0,X1)
% 3.56/1.00      | r2_hidden(X0,X2)
% 3.56/1.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.56/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_750,plain,
% 3.56/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.56/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.56/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1888,plain,
% 3.56/1.00      ( r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(k2_xboole_0(X0,X1),X2),X1) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(k2_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_757,c_750]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_23,negated_conjecture,
% 3.56/1.00      ( r1_tarski(sK4,sK5) ),
% 3.56/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_746,plain,
% 3.56/1.00      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4,plain,
% 3.56/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.56/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_756,plain,
% 3.56/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.56/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.56/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1789,plain,
% 3.56/1.00      ( r2_hidden(X0,sK5) = iProver_top
% 3.56/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_746,c_756]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4867,plain,
% 3.56/1.00      ( r1_tarski(k2_xboole_0(sK4,X0),X1) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(k2_xboole_0(sK4,X0),X1),X0) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(k2_xboole_0(sK4,X0),X1),sK5) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_1888,c_1789]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_2,plain,
% 3.56/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.56/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_758,plain,
% 3.56/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_5225,plain,
% 3.56/1.00      ( r1_tarski(k2_xboole_0(sK4,X0),sK5) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(k2_xboole_0(sK4,X0),sK5),X0) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_4867,c_758]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_5696,plain,
% 3.56/1.00      ( r1_tarski(k2_xboole_0(sK4,sK5),sK5) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_5225,c_758]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_8,plain,
% 3.56/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.56/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_752,plain,
% 3.56/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.56/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1781,plain,
% 3.56/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 3.56/1.00      | r2_hidden(sK1(X0,k2_xboole_0(X1,X2)),X2) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_752,c_758]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3385,plain,
% 3.56/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_757,c_1781]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_12,plain,
% 3.56/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_749,plain,
% 3.56/1.00      ( X0 = X1
% 3.56/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.56/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3478,plain,
% 3.56/1.00      ( k2_xboole_0(X0,X1) = X1
% 3.56/1.00      | r1_tarski(k2_xboole_0(X0,X1),X1) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_3385,c_749]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_8736,plain,
% 3.56/1.00      ( k2_xboole_0(sK4,sK5) = sK5 ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_5696,c_3478]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_464,plain,( X0 = X0 ),theory(equality) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1139,plain,
% 3.56/1.00      ( sK4 = sK4 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_464]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_983,plain,
% 3.56/1.00      ( sK5 = sK5 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_464]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_797,plain,
% 3.56/1.00      ( sK4 != X0 | sK4 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_465]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_910,plain,
% 3.56/1.00      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_797]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_793,plain,
% 3.56/1.00      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_465]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_885,plain,
% 3.56/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_793]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_18,plain,
% 3.56/1.00      ( ~ m1_subset_1(X0,X1)
% 3.56/1.00      | v1_xboole_0(X1)
% 3.56/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_21,plain,
% 3.56/1.00      ( m1_subset_1(sK3(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_256,plain,
% 3.56/1.00      ( ~ v1_zfmisc_1(X0)
% 3.56/1.00      | v1_xboole_0(X1)
% 3.56/1.00      | v1_xboole_0(X0)
% 3.56/1.00      | X0 != X1
% 3.56/1.00      | k6_domain_1(X1,X2) = k2_tarski(X2,X2)
% 3.56/1.00      | sK3(X0) != X2 ),
% 3.56/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_257,plain,
% 3.56/1.00      ( ~ v1_zfmisc_1(X0)
% 3.56/1.00      | v1_xboole_0(X0)
% 3.56/1.00      | k6_domain_1(X0,sK3(X0)) = k2_tarski(sK3(X0),sK3(X0)) ),
% 3.56/1.00      inference(unflattening,[status(thm)],[c_256]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_24,negated_conjecture,
% 3.56/1.00      ( v1_zfmisc_1(sK5) ),
% 3.56/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_273,plain,
% 3.56/1.00      ( v1_xboole_0(X0)
% 3.56/1.00      | k2_tarski(sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0))
% 3.56/1.00      | sK5 != X0 ),
% 3.56/1.00      inference(resolution_lifted,[status(thm)],[c_257,c_24]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_274,plain,
% 3.56/1.00      ( v1_xboole_0(sK5)
% 3.56/1.00      | k2_tarski(sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
% 3.56/1.00      inference(unflattening,[status(thm)],[c_273]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_25,negated_conjecture,
% 3.56/1.00      ( ~ v1_xboole_0(sK5) ),
% 3.56/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_276,plain,
% 3.56/1.00      ( k2_tarski(sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
% 3.56/1.00      inference(global_propositional_subsumption,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_274,c_25]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_20,plain,
% 3.56/1.00      ( ~ v1_zfmisc_1(X0)
% 3.56/1.00      | v1_xboole_0(X0)
% 3.56/1.00      | k6_domain_1(X0,sK3(X0)) = X0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_281,plain,
% 3.56/1.00      ( v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | sK5 != X0 ),
% 3.56/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_282,plain,
% 3.56/1.00      ( v1_xboole_0(sK5) | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 3.56/1.00      inference(unflattening,[status(thm)],[c_281]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_284,plain,
% 3.56/1.00      ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 3.56/1.00      inference(global_propositional_subsumption,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_282,c_25]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_759,plain,
% 3.56/1.00      ( k2_tarski(sK3(sK5),sK3(sK5)) = sK5 ),
% 3.56/1.00      inference(light_normalisation,[status(thm)],[c_276,c_284]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_11,plain,
% 3.56/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_26,negated_conjecture,
% 3.56/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.56/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_330,plain,
% 3.56/1.00      ( sK4 != k1_xboole_0 ),
% 3.56/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_326,plain,
% 3.56/1.00      ( sK5 != k1_xboole_0 ),
% 3.56/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_22,negated_conjecture,
% 3.56/1.00      ( sK4 != sK5 ),
% 3.56/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(contradiction,plain,
% 3.56/1.00      ( $false ),
% 3.56/1.00      inference(minisat,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_12428,c_10120,c_8736,c_1139,c_983,c_910,c_885,c_759,
% 3.56/1.00                 c_330,c_326,c_22]) ).
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  ------                               Statistics
% 3.56/1.00  
% 3.56/1.00  ------ General
% 3.56/1.00  
% 3.56/1.00  abstr_ref_over_cycles:                  0
% 3.56/1.00  abstr_ref_under_cycles:                 0
% 3.56/1.00  gc_basic_clause_elim:                   0
% 3.56/1.00  forced_gc_time:                         0
% 3.56/1.00  parsing_time:                           0.007
% 3.56/1.00  unif_index_cands_time:                  0.
% 3.56/1.00  unif_index_add_time:                    0.
% 3.56/1.00  orderings_time:                         0.
% 3.56/1.00  out_proof_time:                         0.008
% 3.56/1.00  total_time:                             0.411
% 3.56/1.00  num_of_symbols:                         46
% 3.56/1.00  num_of_terms:                           12171
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing
% 3.56/1.00  
% 3.56/1.00  num_of_splits:                          0
% 3.56/1.00  num_of_split_atoms:                     0
% 3.56/1.00  num_of_reused_defs:                     0
% 3.56/1.00  num_eq_ax_congr_red:                    24
% 3.56/1.00  num_of_sem_filtered_clauses:            1
% 3.56/1.00  num_of_subtypes:                        0
% 3.56/1.00  monotx_restored_types:                  0
% 3.56/1.00  sat_num_of_epr_types:                   0
% 3.56/1.00  sat_num_of_non_cyclic_types:            0
% 3.56/1.00  sat_guarded_non_collapsed_types:        0
% 3.56/1.00  num_pure_diseq_elim:                    0
% 3.56/1.00  simp_replaced_by:                       0
% 3.56/1.00  res_preprocessed:                       117
% 3.56/1.00  prep_upred:                             0
% 3.56/1.00  prep_unflattend:                        10
% 3.56/1.00  smt_new_axioms:                         0
% 3.56/1.00  pred_elim_cands:                        2
% 3.56/1.00  pred_elim:                              3
% 3.56/1.00  pred_elim_cl:                           2
% 3.56/1.00  pred_elim_cycles:                       5
% 3.56/1.00  merged_defs:                            0
% 3.56/1.00  merged_defs_ncl:                        0
% 3.56/1.00  bin_hyper_res:                          0
% 3.56/1.00  prep_cycles:                            4
% 3.56/1.00  pred_elim_time:                         0.002
% 3.56/1.00  splitting_time:                         0.
% 3.56/1.00  sem_filter_time:                        0.
% 3.56/1.00  monotx_time:                            0.
% 3.56/1.00  subtype_inf_time:                       0.
% 3.56/1.00  
% 3.56/1.00  ------ Problem properties
% 3.56/1.00  
% 3.56/1.00  clauses:                                24
% 3.56/1.00  conjectures:                            2
% 3.56/1.00  epr:                                    9
% 3.56/1.00  horn:                                   20
% 3.56/1.00  ground:                                 8
% 3.56/1.00  unary:                                  11
% 3.56/1.00  binary:                                 6
% 3.56/1.00  lits:                                   46
% 3.56/1.00  lits_eq:                                14
% 3.56/1.00  fd_pure:                                0
% 3.56/1.00  fd_pseudo:                              0
% 3.56/1.00  fd_cond:                                0
% 3.56/1.00  fd_pseudo_cond:                         5
% 3.56/1.00  ac_symbols:                             0
% 3.56/1.00  
% 3.56/1.00  ------ Propositional Solver
% 3.56/1.00  
% 3.56/1.00  prop_solver_calls:                      31
% 3.56/1.00  prop_fast_solver_calls:                 843
% 3.56/1.00  smt_solver_calls:                       0
% 3.56/1.00  smt_fast_solver_calls:                  0
% 3.56/1.00  prop_num_of_clauses:                    5499
% 3.56/1.00  prop_preprocess_simplified:             11346
% 3.56/1.00  prop_fo_subsumed:                       10
% 3.56/1.00  prop_solver_time:                       0.
% 3.56/1.00  smt_solver_time:                        0.
% 3.56/1.00  smt_fast_solver_time:                   0.
% 3.56/1.00  prop_fast_solver_time:                  0.
% 3.56/1.00  prop_unsat_core_time:                   0.
% 3.56/1.00  
% 3.56/1.00  ------ QBF
% 3.56/1.00  
% 3.56/1.00  qbf_q_res:                              0
% 3.56/1.00  qbf_num_tautologies:                    0
% 3.56/1.00  qbf_prep_cycles:                        0
% 3.56/1.00  
% 3.56/1.00  ------ BMC1
% 3.56/1.00  
% 3.56/1.00  bmc1_current_bound:                     -1
% 3.56/1.00  bmc1_last_solved_bound:                 -1
% 3.56/1.00  bmc1_unsat_core_size:                   -1
% 3.56/1.00  bmc1_unsat_core_parents_size:           -1
% 3.56/1.00  bmc1_merge_next_fun:                    0
% 3.56/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.56/1.00  
% 3.56/1.00  ------ Instantiation
% 3.56/1.00  
% 3.56/1.00  inst_num_of_clauses:                    1502
% 3.56/1.00  inst_num_in_passive:                    807
% 3.56/1.00  inst_num_in_active:                     675
% 3.56/1.00  inst_num_in_unprocessed:                19
% 3.56/1.00  inst_num_of_loops:                      785
% 3.56/1.00  inst_num_of_learning_restarts:          0
% 3.56/1.00  inst_num_moves_active_passive:          105
% 3.56/1.00  inst_lit_activity:                      0
% 3.56/1.00  inst_lit_activity_moves:                0
% 3.56/1.00  inst_num_tautologies:                   0
% 3.56/1.00  inst_num_prop_implied:                  0
% 3.56/1.00  inst_num_existing_simplified:           0
% 3.56/1.00  inst_num_eq_res_simplified:             0
% 3.56/1.00  inst_num_child_elim:                    0
% 3.56/1.00  inst_num_of_dismatching_blockings:      876
% 3.56/1.00  inst_num_of_non_proper_insts:           2065
% 3.56/1.00  inst_num_of_duplicates:                 0
% 3.56/1.00  inst_inst_num_from_inst_to_res:         0
% 3.56/1.00  inst_dismatching_checking_time:         0.
% 3.56/1.00  
% 3.56/1.00  ------ Resolution
% 3.56/1.00  
% 3.56/1.00  res_num_of_clauses:                     0
% 3.56/1.00  res_num_in_passive:                     0
% 3.56/1.00  res_num_in_active:                      0
% 3.56/1.00  res_num_of_loops:                       121
% 3.56/1.00  res_forward_subset_subsumed:            148
% 3.56/1.00  res_backward_subset_subsumed:           0
% 3.56/1.00  res_forward_subsumed:                   0
% 3.56/1.00  res_backward_subsumed:                  0
% 3.56/1.00  res_forward_subsumption_resolution:     0
% 3.56/1.00  res_backward_subsumption_resolution:    0
% 3.56/1.00  res_clause_to_clause_subsumption:       4442
% 3.56/1.00  res_orphan_elimination:                 0
% 3.56/1.00  res_tautology_del:                      91
% 3.56/1.00  res_num_eq_res_simplified:              0
% 3.56/1.00  res_num_sel_changes:                    0
% 3.56/1.00  res_moves_from_active_to_pass:          0
% 3.56/1.00  
% 3.56/1.00  ------ Superposition
% 3.56/1.00  
% 3.56/1.00  sup_time_total:                         0.
% 3.56/1.00  sup_time_generating:                    0.
% 3.56/1.00  sup_time_sim_full:                      0.
% 3.56/1.00  sup_time_sim_immed:                     0.
% 3.56/1.00  
% 3.56/1.00  sup_num_of_clauses:                     493
% 3.56/1.00  sup_num_in_active:                      156
% 3.56/1.00  sup_num_in_passive:                     337
% 3.56/1.00  sup_num_of_loops:                       156
% 3.56/1.00  sup_fw_superposition:                   277
% 3.56/1.00  sup_bw_superposition:                   601
% 3.56/1.00  sup_immediate_simplified:               195
% 3.56/1.00  sup_given_eliminated:                   0
% 3.56/1.00  comparisons_done:                       0
% 3.56/1.00  comparisons_avoided:                    0
% 3.56/1.00  
% 3.56/1.00  ------ Simplifications
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  sim_fw_subset_subsumed:                 122
% 3.56/1.00  sim_bw_subset_subsumed:                 2
% 3.56/1.00  sim_fw_subsumed:                        51
% 3.56/1.00  sim_bw_subsumed:                        2
% 3.56/1.00  sim_fw_subsumption_res:                 0
% 3.56/1.00  sim_bw_subsumption_res:                 0
% 3.56/1.00  sim_tautology_del:                      22
% 3.56/1.00  sim_eq_tautology_del:                   28
% 3.56/1.00  sim_eq_res_simp:                        61
% 3.56/1.00  sim_fw_demodulated:                     53
% 3.56/1.00  sim_bw_demodulated:                     0
% 3.56/1.00  sim_light_normalised:                   26
% 3.56/1.00  sim_joinable_taut:                      0
% 3.56/1.00  sim_joinable_simp:                      0
% 3.56/1.00  sim_ac_normalised:                      0
% 3.56/1.00  sim_smt_subsumption:                    0
% 3.56/1.00  
%------------------------------------------------------------------------------
