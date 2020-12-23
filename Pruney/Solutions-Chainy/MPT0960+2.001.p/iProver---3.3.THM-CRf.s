%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:48 EST 2020

% Result     : Theorem 22.92s
% Output     : CNFRefutation 22.92s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 281 expanded)
%              Number of clauses        :   38 (  85 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  299 ( 935 expanded)
%              Number of equality atoms :   95 ( 224 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f35,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f35,f34])).

fof(f57,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK2(X4),sK3(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ~ r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f42])).

fof(f70,plain,(
    ~ r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_24,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_25,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_147,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_25])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2899,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2890,plain,
    ( k4_tarski(sK2(X0),sK3(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5611,plain,
    ( k4_tarski(sK2(sK0(X0,X1)),sK3(sK0(X0,X1))) = sK0(X0,X1)
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2899,c_2890])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2880,plain,
    ( r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_52005,plain,
    ( k4_tarski(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)))) = sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))
    | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5611,c_2880])).

cnf(c_29,plain,
    ( v1_relat_1(k1_wellord2(sK6)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_557,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_zfmisc_1(sK6,sK6) != X1
    | k1_wellord2(sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_26])).

cnf(c_558,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_3078,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6))
    | ~ v1_relat_1(k1_wellord2(sK6))
    | k4_tarski(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)))) = sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_54222,plain,
    ( k4_tarski(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)))) = sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_52005,c_29,c_558,c_3078])).

cnf(c_17,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2888,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_54231,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),X0) != iProver_top
    | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),k3_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54222,c_2888])).

cnf(c_54494,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(X0)) != iProver_top
    | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X0) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_147,c_54231])).

cnf(c_54527,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) != iProver_top
    | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) = iProver_top
    | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54494])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2889,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_54227,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),X0) != iProver_top
    | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),k3_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54222,c_2889])).

cnf(c_54422,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(X0)) != iProver_top
    | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X0) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_147,c_54227])).

cnf(c_54455,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) != iProver_top
    | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) = iProver_top
    | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54422])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2896,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_54226,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X1) != iProver_top
    | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54222,c_2896])).

cnf(c_54283,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(sK6,sK6)) = iProver_top
    | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) != iProver_top
    | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54226])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_564,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k2_zfmisc_1(sK6,sK6) != X1
    | k1_wellord2(sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_565,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(sK6,sK6)) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_566,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(sK6,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_559,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_28,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_30,plain,
    ( v1_relat_1(k1_wellord2(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54527,c_54455,c_54283,c_566,c_559,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 22.92/3.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.92/3.50  
% 22.92/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 22.92/3.50  
% 22.92/3.50  ------  iProver source info
% 22.92/3.50  
% 22.92/3.50  git: date: 2020-06-30 10:37:57 +0100
% 22.92/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 22.92/3.50  git: non_committed_changes: false
% 22.92/3.50  git: last_make_outside_of_git: false
% 22.92/3.50  
% 22.92/3.50  ------ 
% 22.92/3.50  ------ Parsing...
% 22.92/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  ------ Proving...
% 22.92/3.50  ------ Problem Properties 
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  clauses                                 25
% 22.92/3.50  conjectures                             1
% 22.92/3.50  EPR                                     2
% 22.92/3.50  Horn                                    20
% 22.92/3.50  unary                                   6
% 22.92/3.50  binary                                  7
% 22.92/3.50  lits                                    62
% 22.92/3.50  lits eq                                 10
% 22.92/3.50  fd_pure                                 0
% 22.92/3.50  fd_pseudo                               0
% 22.92/3.50  fd_cond                                 0
% 22.92/3.50  fd_pseudo_cond                          0
% 22.92/3.50  AC symbols                              0
% 22.92/3.50  
% 22.92/3.50  ------ Input Options Time Limit: Unbounded
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 22.92/3.50  Current options:
% 22.92/3.50  ------ 
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 16 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 16 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 16 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 22.92/3.50  
% 22.92/3.50  ------ Proving...
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  % SZS status Theorem for theBenchmark.p
% 22.92/3.50  
% 22.92/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 22.92/3.50  
% 22.92/3.50  fof(f11,axiom,(
% 22.92/3.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 22.92/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/3.50  
% 22.92/3.50  fof(f22,plain,(
% 22.92/3.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 22.92/3.50    inference(ennf_transformation,[],[f11])).
% 22.92/3.50  
% 22.92/3.50  fof(f23,plain,(
% 22.92/3.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 22.92/3.50    inference(flattening,[],[f22])).
% 22.92/3.50  
% 22.92/3.50  fof(f37,plain,(
% 22.92/3.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 22.92/3.50    inference(nnf_transformation,[],[f23])).
% 22.92/3.50  
% 22.92/3.50  fof(f38,plain,(
% 22.92/3.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 22.92/3.50    inference(flattening,[],[f37])).
% 22.92/3.50  
% 22.92/3.50  fof(f39,plain,(
% 22.92/3.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 22.92/3.50    inference(rectify,[],[f38])).
% 22.92/3.50  
% 22.92/3.50  fof(f40,plain,(
% 22.92/3.50    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)))),
% 22.92/3.50    introduced(choice_axiom,[])).
% 22.92/3.50  
% 22.92/3.50  fof(f41,plain,(
% 22.92/3.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 22.92/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).
% 22.92/3.50  
% 22.92/3.50  fof(f62,plain,(
% 22.92/3.50    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 22.92/3.50    inference(cnf_transformation,[],[f41])).
% 22.92/3.50  
% 22.92/3.50  fof(f77,plain,(
% 22.92/3.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 22.92/3.50    inference(equality_resolution,[],[f62])).
% 22.92/3.50  
% 22.92/3.50  fof(f12,axiom,(
% 22.92/3.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 22.92/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/3.50  
% 22.92/3.50  fof(f69,plain,(
% 22.92/3.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 22.92/3.50    inference(cnf_transformation,[],[f12])).
% 22.92/3.50  
% 22.92/3.50  fof(f1,axiom,(
% 22.92/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 22.92/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/3.50  
% 22.92/3.50  fof(f16,plain,(
% 22.92/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 22.92/3.50    inference(ennf_transformation,[],[f1])).
% 22.92/3.50  
% 22.92/3.50  fof(f25,plain,(
% 22.92/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 22.92/3.50    inference(nnf_transformation,[],[f16])).
% 22.92/3.50  
% 22.92/3.50  fof(f26,plain,(
% 22.92/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 22.92/3.50    inference(rectify,[],[f25])).
% 22.92/3.50  
% 22.92/3.50  fof(f27,plain,(
% 22.92/3.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 22.92/3.50    introduced(choice_axiom,[])).
% 22.92/3.50  
% 22.92/3.50  fof(f28,plain,(
% 22.92/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 22.92/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 22.92/3.50  
% 22.92/3.50  fof(f45,plain,(
% 22.92/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 22.92/3.50    inference(cnf_transformation,[],[f28])).
% 22.92/3.50  
% 22.92/3.50  fof(f9,axiom,(
% 22.92/3.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 22.92/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/3.50  
% 22.92/3.50  fof(f19,plain,(
% 22.92/3.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 22.92/3.50    inference(ennf_transformation,[],[f9])).
% 22.92/3.50  
% 22.92/3.50  fof(f32,plain,(
% 22.92/3.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 22.92/3.50    inference(nnf_transformation,[],[f19])).
% 22.92/3.50  
% 22.92/3.50  fof(f33,plain,(
% 22.92/3.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 22.92/3.50    inference(rectify,[],[f32])).
% 22.92/3.50  
% 22.92/3.50  fof(f35,plain,(
% 22.92/3.50    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 22.92/3.50    introduced(choice_axiom,[])).
% 22.92/3.50  
% 22.92/3.50  fof(f34,plain,(
% 22.92/3.50    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 22.92/3.50    introduced(choice_axiom,[])).
% 22.92/3.50  
% 22.92/3.50  fof(f36,plain,(
% 22.92/3.50    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 22.92/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f35,f34])).
% 22.92/3.50  
% 22.92/3.50  fof(f57,plain,(
% 22.92/3.50    ( ! [X4,X0] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 22.92/3.50    inference(cnf_transformation,[],[f36])).
% 22.92/3.50  
% 22.92/3.50  fof(f13,conjecture,(
% 22.92/3.50    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 22.92/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/3.50  
% 22.92/3.50  fof(f14,negated_conjecture,(
% 22.92/3.50    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 22.92/3.50    inference(negated_conjecture,[],[f13])).
% 22.92/3.50  
% 22.92/3.50  fof(f24,plain,(
% 22.92/3.50    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 22.92/3.50    inference(ennf_transformation,[],[f14])).
% 22.92/3.50  
% 22.92/3.50  fof(f42,plain,(
% 22.92/3.50    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),
% 22.92/3.50    introduced(choice_axiom,[])).
% 22.92/3.50  
% 22.92/3.50  fof(f43,plain,(
% 22.92/3.50    ~r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),
% 22.92/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f42])).
% 22.92/3.50  
% 22.92/3.50  fof(f70,plain,(
% 22.92/3.50    ~r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),
% 22.92/3.50    inference(cnf_transformation,[],[f43])).
% 22.92/3.50  
% 22.92/3.50  fof(f10,axiom,(
% 22.92/3.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 22.92/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/3.50  
% 22.92/3.50  fof(f20,plain,(
% 22.92/3.50    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 22.92/3.50    inference(ennf_transformation,[],[f10])).
% 22.92/3.50  
% 22.92/3.50  fof(f21,plain,(
% 22.92/3.50    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 22.92/3.50    inference(flattening,[],[f20])).
% 22.92/3.50  
% 22.92/3.50  fof(f60,plain,(
% 22.92/3.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 22.92/3.50    inference(cnf_transformation,[],[f21])).
% 22.92/3.50  
% 22.92/3.50  fof(f61,plain,(
% 22.92/3.50    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 22.92/3.50    inference(cnf_transformation,[],[f21])).
% 22.92/3.50  
% 22.92/3.50  fof(f5,axiom,(
% 22.92/3.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 22.92/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.92/3.50  
% 22.92/3.50  fof(f29,plain,(
% 22.92/3.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 22.92/3.50    inference(nnf_transformation,[],[f5])).
% 22.92/3.50  
% 22.92/3.50  fof(f30,plain,(
% 22.92/3.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 22.92/3.50    inference(flattening,[],[f29])).
% 22.92/3.50  
% 22.92/3.50  fof(f52,plain,(
% 22.92/3.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 22.92/3.50    inference(cnf_transformation,[],[f30])).
% 22.92/3.50  
% 22.92/3.50  fof(f46,plain,(
% 22.92/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 22.92/3.50    inference(cnf_transformation,[],[f28])).
% 22.92/3.50  
% 22.92/3.50  cnf(c_24,plain,
% 22.92/3.50      ( ~ v1_relat_1(k1_wellord2(X0))
% 22.92/3.50      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 22.92/3.50      inference(cnf_transformation,[],[f77]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_25,plain,
% 22.92/3.50      ( v1_relat_1(k1_wellord2(X0)) ),
% 22.92/3.50      inference(cnf_transformation,[],[f69]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_147,plain,
% 22.92/3.50      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 22.92/3.50      inference(global_propositional_subsumption,
% 22.92/3.50                [status(thm)],
% 22.92/3.50                [c_24,c_25]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_1,plain,
% 22.92/3.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 22.92/3.50      inference(cnf_transformation,[],[f45]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_2899,plain,
% 22.92/3.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 22.92/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_15,plain,
% 22.92/3.50      ( ~ r2_hidden(X0,X1)
% 22.92/3.50      | ~ v1_relat_1(X1)
% 22.92/3.50      | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
% 22.92/3.50      inference(cnf_transformation,[],[f57]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_2890,plain,
% 22.92/3.50      ( k4_tarski(sK2(X0),sK3(X0)) = X0
% 22.92/3.50      | r2_hidden(X0,X1) != iProver_top
% 22.92/3.50      | v1_relat_1(X1) != iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_5611,plain,
% 22.92/3.50      ( k4_tarski(sK2(sK0(X0,X1)),sK3(sK0(X0,X1))) = sK0(X0,X1)
% 22.92/3.50      | r1_tarski(X0,X1) = iProver_top
% 22.92/3.50      | v1_relat_1(X0) != iProver_top ),
% 22.92/3.50      inference(superposition,[status(thm)],[c_2899,c_2890]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_26,negated_conjecture,
% 22.92/3.50      ( ~ r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
% 22.92/3.50      inference(cnf_transformation,[],[f70]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_2880,plain,
% 22.92/3.50      ( r1_tarski(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) != iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_52005,plain,
% 22.92/3.50      ( k4_tarski(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)))) = sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))
% 22.92/3.50      | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
% 22.92/3.50      inference(superposition,[status(thm)],[c_5611,c_2880]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_29,plain,
% 22.92/3.50      ( v1_relat_1(k1_wellord2(sK6)) ),
% 22.92/3.50      inference(instantiation,[status(thm)],[c_25]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_557,plain,
% 22.92/3.50      ( r2_hidden(sK0(X0,X1),X0)
% 22.92/3.50      | k2_zfmisc_1(sK6,sK6) != X1
% 22.92/3.50      | k1_wellord2(sK6) != X0 ),
% 22.92/3.50      inference(resolution_lifted,[status(thm)],[c_1,c_26]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_558,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) ),
% 22.92/3.50      inference(unflattening,[status(thm)],[c_557]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_3078,plain,
% 22.92/3.50      ( ~ r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6))
% 22.92/3.50      | ~ v1_relat_1(k1_wellord2(sK6))
% 22.92/3.50      | k4_tarski(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)))) = sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
% 22.92/3.50      inference(instantiation,[status(thm)],[c_15]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54222,plain,
% 22.92/3.50      ( k4_tarski(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)))) = sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)) ),
% 22.92/3.50      inference(global_propositional_subsumption,
% 22.92/3.50                [status(thm)],
% 22.92/3.50                [c_52005,c_29,c_558,c_3078]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_17,plain,
% 22.92/3.50      ( r2_hidden(X0,k3_relat_1(X1))
% 22.92/3.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 22.92/3.50      | ~ v1_relat_1(X1) ),
% 22.92/3.50      inference(cnf_transformation,[],[f60]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_2888,plain,
% 22.92/3.50      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 22.92/3.50      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 22.92/3.50      | v1_relat_1(X1) != iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54231,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),X0) != iProver_top
% 22.92/3.50      | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),k3_relat_1(X0)) = iProver_top
% 22.92/3.50      | v1_relat_1(X0) != iProver_top ),
% 22.92/3.50      inference(superposition,[status(thm)],[c_54222,c_2888]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54494,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(X0)) != iProver_top
% 22.92/3.50      | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X0) = iProver_top
% 22.92/3.50      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 22.92/3.50      inference(superposition,[status(thm)],[c_147,c_54231]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54527,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) != iProver_top
% 22.92/3.50      | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) = iProver_top
% 22.92/3.50      | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
% 22.92/3.50      inference(instantiation,[status(thm)],[c_54494]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_16,plain,
% 22.92/3.50      ( r2_hidden(X0,k3_relat_1(X1))
% 22.92/3.50      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 22.92/3.50      | ~ v1_relat_1(X1) ),
% 22.92/3.50      inference(cnf_transformation,[],[f61]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_2889,plain,
% 22.92/3.50      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 22.92/3.50      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 22.92/3.50      | v1_relat_1(X1) != iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54227,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),X0) != iProver_top
% 22.92/3.50      | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),k3_relat_1(X0)) = iProver_top
% 22.92/3.50      | v1_relat_1(X0) != iProver_top ),
% 22.92/3.50      inference(superposition,[status(thm)],[c_54222,c_2889]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54422,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(X0)) != iProver_top
% 22.92/3.50      | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X0) = iProver_top
% 22.92/3.50      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 22.92/3.50      inference(superposition,[status(thm)],[c_147,c_54227]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54455,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) != iProver_top
% 22.92/3.50      | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) = iProver_top
% 22.92/3.50      | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
% 22.92/3.50      inference(instantiation,[status(thm)],[c_54422]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_6,plain,
% 22.92/3.50      ( ~ r2_hidden(X0,X1)
% 22.92/3.50      | ~ r2_hidden(X2,X3)
% 22.92/3.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 22.92/3.50      inference(cnf_transformation,[],[f52]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_2896,plain,
% 22.92/3.50      ( r2_hidden(X0,X1) != iProver_top
% 22.92/3.50      | r2_hidden(X2,X3) != iProver_top
% 22.92/3.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54226,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(X0,X1)) = iProver_top
% 22.92/3.50      | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X1) != iProver_top
% 22.92/3.50      | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),X0) != iProver_top ),
% 22.92/3.50      inference(superposition,[status(thm)],[c_54222,c_2896]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_54283,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(sK6,sK6)) = iProver_top
% 22.92/3.50      | r2_hidden(sK3(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) != iProver_top
% 22.92/3.50      | r2_hidden(sK2(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6))),sK6) != iProver_top ),
% 22.92/3.50      inference(instantiation,[status(thm)],[c_54226]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_0,plain,
% 22.92/3.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 22.92/3.50      inference(cnf_transformation,[],[f46]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_564,plain,
% 22.92/3.50      ( ~ r2_hidden(sK0(X0,X1),X1)
% 22.92/3.50      | k2_zfmisc_1(sK6,sK6) != X1
% 22.92/3.50      | k1_wellord2(sK6) != X0 ),
% 22.92/3.50      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_565,plain,
% 22.92/3.50      ( ~ r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(sK6,sK6)) ),
% 22.92/3.50      inference(unflattening,[status(thm)],[c_564]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_566,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k2_zfmisc_1(sK6,sK6)) != iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_559,plain,
% 22.92/3.50      ( r2_hidden(sK0(k1_wellord2(sK6),k2_zfmisc_1(sK6,sK6)),k1_wellord2(sK6)) = iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_28,plain,
% 22.92/3.50      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 22.92/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(c_30,plain,
% 22.92/3.50      ( v1_relat_1(k1_wellord2(sK6)) = iProver_top ),
% 22.92/3.50      inference(instantiation,[status(thm)],[c_28]) ).
% 22.92/3.50  
% 22.92/3.50  cnf(contradiction,plain,
% 22.92/3.50      ( $false ),
% 22.92/3.50      inference(minisat,
% 22.92/3.50                [status(thm)],
% 22.92/3.50                [c_54527,c_54455,c_54283,c_566,c_559,c_30]) ).
% 22.92/3.50  
% 22.92/3.50  
% 22.92/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 22.92/3.50  
% 22.92/3.50  ------                               Statistics
% 22.92/3.50  
% 22.92/3.50  ------ Selected
% 22.92/3.50  
% 22.92/3.50  total_time:                             2.575
% 22.92/3.50  
%------------------------------------------------------------------------------
