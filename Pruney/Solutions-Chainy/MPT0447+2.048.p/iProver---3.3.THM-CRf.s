%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:17 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 209 expanded)
%              Number of clauses        :   66 (  88 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  283 ( 681 expanded)
%              Number of equality atoms :  102 ( 129 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK2))
        & r1_tarski(X0,sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(X1))
          & r1_tarski(sK1,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f23,f22])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_128,plain,
    ( r2_hidden(sK0(X0_38,X1_38),X0_38)
    | r1_tarski(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_363,plain,
    ( r2_hidden(sK0(X0_38,X1_38),X0_38) = iProver_top
    | r1_tarski(X0_38,X1_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_128])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_121,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k1_relat_1(X0_38),k1_relat_1(X1_38))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_370,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(k1_relat_1(X0_38),k1_relat_1(X1_38)) = iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_121])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_127,plain,
    ( ~ r2_hidden(X0_39,X0_38)
    | r2_hidden(X0_39,X1_38)
    | ~ r1_tarski(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_364,plain,
    ( r2_hidden(X0_39,X0_38) != iProver_top
    | r2_hidden(X0_39,X1_38) = iProver_top
    | r1_tarski(X0_38,X1_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_1077,plain,
    ( r2_hidden(X0_39,k1_relat_1(X0_38)) != iProver_top
    | r2_hidden(X0_39,k1_relat_1(X1_38)) = iProver_top
    | r1_tarski(X0_38,X1_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_370,c_364])).

cnf(c_2738,plain,
    ( r2_hidden(sK0(k1_relat_1(X0_38),X1_38),k1_relat_1(X2_38)) = iProver_top
    | r1_tarski(X0_38,X2_38) != iProver_top
    | r1_tarski(k1_relat_1(X0_38),X1_38) = iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X2_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_363,c_1077])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_118,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_373,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_123,plain,
    ( ~ v1_relat_1(X0_38)
    | k2_xboole_0(k1_relat_1(X0_38),k2_relat_1(X0_38)) = k3_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_368,plain,
    ( k2_xboole_0(k1_relat_1(X0_38),k2_relat_1(X0_38)) = k3_relat_1(X0_38)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123])).

cnf(c_785,plain,
    ( k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_373,c_368])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_125,plain,
    ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_366,plain,
    ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_796,plain,
    ( r2_hidden(X0_39,X0_38) != iProver_top
    | r2_hidden(X0_39,k2_xboole_0(X0_38,X1_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_364])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_129,plain,
    ( ~ r2_hidden(sK0(X0_38,X1_38),X1_38)
    | r1_tarski(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_362,plain,
    ( r2_hidden(sK0(X0_38,X1_38),X1_38) != iProver_top
    | r1_tarski(X0_38,X1_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_1805,plain,
    ( r2_hidden(sK0(X0_38,k2_xboole_0(X1_38,X2_38)),X1_38) != iProver_top
    | r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_362])).

cnf(c_2570,plain,
    ( r2_hidden(sK0(X0_38,k3_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(X0_38,k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_1805])).

cnf(c_2573,plain,
    ( r2_hidden(sK0(X0_38,k3_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(X0_38,k3_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2570,c_785])).

cnf(c_17686,plain,
    ( r1_tarski(X0_38,sK2) != iProver_top
    | r1_tarski(k1_relat_1(X0_38),k3_relat_1(sK2)) = iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_2573])).

cnf(c_17710,plain,
    ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17686])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k2_relat_1(X0_38),k2_relat_1(X1_38))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_369,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(k2_relat_1(X0_38),k2_relat_1(X1_38)) = iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_126,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X0_38,k2_xboole_0(X2_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_365,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X0_38,k2_xboole_0(X2_38,X1_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_126])).

cnf(c_1250,plain,
    ( r1_tarski(X0_38,k3_relat_1(sK2)) = iProver_top
    | r1_tarski(X0_38,k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_365])).

cnf(c_1895,plain,
    ( r1_tarski(X0_38,sK2) != iProver_top
    | r1_tarski(k2_relat_1(X0_38),k3_relat_1(sK2)) = iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_1250])).

cnf(c_1915,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_124,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X2_38,X1_38)
    | r1_tarski(k2_xboole_0(X0_38,X2_38),X1_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1024,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_1025,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2)) = iProver_top
    | r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_134,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X2_38,X3_38)
    | X2_38 != X0_38
    | X3_38 != X1_38 ),
    theory(equality)).

cnf(c_492,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
    | k3_relat_1(sK2) != X1_38
    | k3_relat_1(sK1) != X0_38 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_753,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),X0_38)
    | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
    | k3_relat_1(sK2) != X0_38
    | k3_relat_1(sK1) != k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_841,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2))
    | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
    | k3_relat_1(sK2) != k3_relat_1(sK2)
    | k3_relat_1(sK1) != k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_842,plain,
    ( k3_relat_1(sK2) != k3_relat_1(sK2)
    | k3_relat_1(sK1) != k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2)) != iProver_top
    | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_133,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_537,plain,
    ( X0_38 != X1_38
    | k3_relat_1(sK1) != X1_38
    | k3_relat_1(sK1) = X0_38 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_550,plain,
    ( X0_38 != k3_relat_1(sK1)
    | k3_relat_1(sK1) = X0_38
    | k3_relat_1(sK1) != k3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_639,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) != k3_relat_1(sK1)
    | k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_131,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_630,plain,
    ( k3_relat_1(sK2) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_154,plain,
    ( ~ v1_relat_1(sK1)
    | k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_145,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_137,plain,
    ( X0_38 != X1_38
    | k3_relat_1(X0_38) = k3_relat_1(X1_38) ),
    theory(equality)).

cnf(c_142,plain,
    ( k3_relat_1(sK1) = k3_relat_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17710,c_1915,c_1025,c_842,c_639,c_630,c_154,c_145,c_142,c_16,c_15,c_14,c_13,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.04/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/0.99  
% 4.04/0.99  ------  iProver source info
% 4.04/0.99  
% 4.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/0.99  git: non_committed_changes: false
% 4.04/0.99  git: last_make_outside_of_git: false
% 4.04/0.99  
% 4.04/0.99  ------ 
% 4.04/0.99  
% 4.04/0.99  ------ Input Options
% 4.04/0.99  
% 4.04/0.99  --out_options                           all
% 4.04/0.99  --tptp_safe_out                         true
% 4.04/0.99  --problem_path                          ""
% 4.04/0.99  --include_path                          ""
% 4.04/0.99  --clausifier                            res/vclausify_rel
% 4.04/0.99  --clausifier_options                    --mode clausify
% 4.04/0.99  --stdin                                 false
% 4.04/0.99  --stats_out                             sel
% 4.04/0.99  
% 4.04/0.99  ------ General Options
% 4.04/0.99  
% 4.04/0.99  --fof                                   false
% 4.04/0.99  --time_out_real                         604.99
% 4.04/0.99  --time_out_virtual                      -1.
% 4.04/0.99  --symbol_type_check                     false
% 4.04/0.99  --clausify_out                          false
% 4.04/0.99  --sig_cnt_out                           false
% 4.04/0.99  --trig_cnt_out                          false
% 4.04/0.99  --trig_cnt_out_tolerance                1.
% 4.04/0.99  --trig_cnt_out_sk_spl                   false
% 4.04/0.99  --abstr_cl_out                          false
% 4.04/0.99  
% 4.04/0.99  ------ Global Options
% 4.04/0.99  
% 4.04/0.99  --schedule                              none
% 4.04/0.99  --add_important_lit                     false
% 4.04/0.99  --prop_solver_per_cl                    1000
% 4.04/0.99  --min_unsat_core                        false
% 4.04/0.99  --soft_assumptions                      false
% 4.04/0.99  --soft_lemma_size                       3
% 4.04/0.99  --prop_impl_unit_size                   0
% 4.04/0.99  --prop_impl_unit                        []
% 4.04/0.99  --share_sel_clauses                     true
% 4.04/0.99  --reset_solvers                         false
% 4.04/0.99  --bc_imp_inh                            [conj_cone]
% 4.04/0.99  --conj_cone_tolerance                   3.
% 4.04/0.99  --extra_neg_conj                        none
% 4.04/0.99  --large_theory_mode                     true
% 4.04/0.99  --prolific_symb_bound                   200
% 4.04/0.99  --lt_threshold                          2000
% 4.04/0.99  --clause_weak_htbl                      true
% 4.04/0.99  --gc_record_bc_elim                     false
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing Options
% 4.04/0.99  
% 4.04/0.99  --preprocessing_flag                    true
% 4.04/0.99  --time_out_prep_mult                    0.1
% 4.04/0.99  --splitting_mode                        input
% 4.04/0.99  --splitting_grd                         true
% 4.04/0.99  --splitting_cvd                         false
% 4.04/0.99  --splitting_cvd_svl                     false
% 4.04/0.99  --splitting_nvd                         32
% 4.04/0.99  --sub_typing                            true
% 4.04/0.99  --prep_gs_sim                           false
% 4.04/0.99  --prep_unflatten                        true
% 4.04/0.99  --prep_res_sim                          true
% 4.04/0.99  --prep_upred                            true
% 4.04/0.99  --prep_sem_filter                       exhaustive
% 4.04/0.99  --prep_sem_filter_out                   false
% 4.04/0.99  --pred_elim                             false
% 4.04/0.99  --res_sim_input                         true
% 4.04/0.99  --eq_ax_congr_red                       true
% 4.04/0.99  --pure_diseq_elim                       true
% 4.04/0.99  --brand_transform                       false
% 4.04/0.99  --non_eq_to_eq                          false
% 4.04/0.99  --prep_def_merge                        true
% 4.04/0.99  --prep_def_merge_prop_impl              false
% 4.04/0.99  --prep_def_merge_mbd                    true
% 4.04/0.99  --prep_def_merge_tr_red                 false
% 4.04/0.99  --prep_def_merge_tr_cl                  false
% 4.04/0.99  --smt_preprocessing                     true
% 4.04/0.99  --smt_ac_axioms                         fast
% 4.04/0.99  --preprocessed_out                      false
% 4.04/0.99  --preprocessed_stats                    false
% 4.04/0.99  
% 4.04/0.99  ------ Abstraction refinement Options
% 4.04/0.99  
% 4.04/0.99  --abstr_ref                             []
% 4.04/0.99  --abstr_ref_prep                        false
% 4.04/0.99  --abstr_ref_until_sat                   false
% 4.04/0.99  --abstr_ref_sig_restrict                funpre
% 4.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/0.99  --abstr_ref_under                       []
% 4.04/0.99  
% 4.04/0.99  ------ SAT Options
% 4.04/0.99  
% 4.04/0.99  --sat_mode                              false
% 4.04/0.99  --sat_fm_restart_options                ""
% 4.04/0.99  --sat_gr_def                            false
% 4.04/0.99  --sat_epr_types                         true
% 4.04/0.99  --sat_non_cyclic_types                  false
% 4.04/0.99  --sat_finite_models                     false
% 4.04/0.99  --sat_fm_lemmas                         false
% 4.04/0.99  --sat_fm_prep                           false
% 4.04/0.99  --sat_fm_uc_incr                        true
% 4.04/0.99  --sat_out_model                         small
% 4.04/0.99  --sat_out_clauses                       false
% 4.04/0.99  
% 4.04/0.99  ------ QBF Options
% 4.04/0.99  
% 4.04/0.99  --qbf_mode                              false
% 4.04/0.99  --qbf_elim_univ                         false
% 4.04/0.99  --qbf_dom_inst                          none
% 4.04/0.99  --qbf_dom_pre_inst                      false
% 4.04/0.99  --qbf_sk_in                             false
% 4.04/0.99  --qbf_pred_elim                         true
% 4.04/0.99  --qbf_split                             512
% 4.04/0.99  
% 4.04/0.99  ------ BMC1 Options
% 4.04/0.99  
% 4.04/0.99  --bmc1_incremental                      false
% 4.04/0.99  --bmc1_axioms                           reachable_all
% 4.04/0.99  --bmc1_min_bound                        0
% 4.04/0.99  --bmc1_max_bound                        -1
% 4.04/0.99  --bmc1_max_bound_default                -1
% 4.04/0.99  --bmc1_symbol_reachability              true
% 4.04/0.99  --bmc1_property_lemmas                  false
% 4.04/0.99  --bmc1_k_induction                      false
% 4.04/0.99  --bmc1_non_equiv_states                 false
% 4.04/0.99  --bmc1_deadlock                         false
% 4.04/0.99  --bmc1_ucm                              false
% 4.04/0.99  --bmc1_add_unsat_core                   none
% 4.04/0.99  --bmc1_unsat_core_children              false
% 4.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/0.99  --bmc1_out_stat                         full
% 4.04/0.99  --bmc1_ground_init                      false
% 4.04/0.99  --bmc1_pre_inst_next_state              false
% 4.04/0.99  --bmc1_pre_inst_state                   false
% 4.04/0.99  --bmc1_pre_inst_reach_state             false
% 4.04/0.99  --bmc1_out_unsat_core                   false
% 4.04/0.99  --bmc1_aig_witness_out                  false
% 4.04/0.99  --bmc1_verbose                          false
% 4.04/0.99  --bmc1_dump_clauses_tptp                false
% 4.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.04/0.99  --bmc1_dump_file                        -
% 4.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.04/0.99  --bmc1_ucm_extend_mode                  1
% 4.04/0.99  --bmc1_ucm_init_mode                    2
% 4.04/0.99  --bmc1_ucm_cone_mode                    none
% 4.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.04/0.99  --bmc1_ucm_relax_model                  4
% 4.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/0.99  --bmc1_ucm_layered_model                none
% 4.04/0.99  --bmc1_ucm_max_lemma_size               10
% 4.04/0.99  
% 4.04/0.99  ------ AIG Options
% 4.04/0.99  
% 4.04/0.99  --aig_mode                              false
% 4.04/0.99  
% 4.04/0.99  ------ Instantiation Options
% 4.04/0.99  
% 4.04/0.99  --instantiation_flag                    true
% 4.04/0.99  --inst_sos_flag                         false
% 4.04/0.99  --inst_sos_phase                        true
% 4.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel_side                     num_symb
% 4.04/0.99  --inst_solver_per_active                1400
% 4.04/0.99  --inst_solver_calls_frac                1.
% 4.04/0.99  --inst_passive_queue_type               priority_queues
% 4.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/0.99  --inst_passive_queues_freq              [25;2]
% 4.04/0.99  --inst_dismatching                      true
% 4.04/0.99  --inst_eager_unprocessed_to_passive     true
% 4.04/0.99  --inst_prop_sim_given                   true
% 4.04/0.99  --inst_prop_sim_new                     false
% 4.04/0.99  --inst_subs_new                         false
% 4.04/0.99  --inst_eq_res_simp                      false
% 4.04/0.99  --inst_subs_given                       false
% 4.04/0.99  --inst_orphan_elimination               true
% 4.04/0.99  --inst_learning_loop_flag               true
% 4.04/0.99  --inst_learning_start                   3000
% 4.04/0.99  --inst_learning_factor                  2
% 4.04/0.99  --inst_start_prop_sim_after_learn       3
% 4.04/0.99  --inst_sel_renew                        solver
% 4.04/0.99  --inst_lit_activity_flag                true
% 4.04/0.99  --inst_restr_to_given                   false
% 4.04/0.99  --inst_activity_threshold               500
% 4.04/0.99  --inst_out_proof                        true
% 4.04/0.99  
% 4.04/0.99  ------ Resolution Options
% 4.04/0.99  
% 4.04/0.99  --resolution_flag                       true
% 4.04/0.99  --res_lit_sel                           adaptive
% 4.04/0.99  --res_lit_sel_side                      none
% 4.04/0.99  --res_ordering                          kbo
% 4.04/0.99  --res_to_prop_solver                    active
% 4.04/0.99  --res_prop_simpl_new                    false
% 4.04/0.99  --res_prop_simpl_given                  true
% 4.04/0.99  --res_passive_queue_type                priority_queues
% 4.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/0.99  --res_passive_queues_freq               [15;5]
% 4.04/0.99  --res_forward_subs                      full
% 4.04/0.99  --res_backward_subs                     full
% 4.04/0.99  --res_forward_subs_resolution           true
% 4.04/0.99  --res_backward_subs_resolution          true
% 4.04/0.99  --res_orphan_elimination                true
% 4.04/0.99  --res_time_limit                        2.
% 4.04/0.99  --res_out_proof                         true
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Options
% 4.04/0.99  
% 4.04/0.99  --superposition_flag                    true
% 4.04/0.99  --sup_passive_queue_type                priority_queues
% 4.04/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/0.99  --sup_passive_queues_freq               [1;4]
% 4.04/0.99  --demod_completeness_check              fast
% 4.04/0.99  --demod_use_ground                      true
% 4.04/0.99  --sup_to_prop_solver                    passive
% 4.04/0.99  --sup_prop_simpl_new                    true
% 4.04/0.99  --sup_prop_simpl_given                  true
% 4.04/0.99  --sup_fun_splitting                     false
% 4.04/0.99  --sup_smt_interval                      50000
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Simplification Setup
% 4.04/0.99  
% 4.04/0.99  --sup_indices_passive                   []
% 4.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/0.99  --sup_full_bw                           [BwDemod]
% 4.04/0.99  --sup_immed_triv                        [TrivRules]
% 4.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/0.99  --sup_immed_bw_main                     []
% 4.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/0.99  
% 4.04/0.99  ------ Combination Options
% 4.04/0.99  
% 4.04/0.99  --comb_res_mult                         3
% 4.04/0.99  --comb_sup_mult                         2
% 4.04/0.99  --comb_inst_mult                        10
% 4.04/0.99  
% 4.04/0.99  ------ Debug Options
% 4.04/0.99  
% 4.04/0.99  --dbg_backtrace                         false
% 4.04/0.99  --dbg_dump_prop_clauses                 false
% 4.04/0.99  --dbg_dump_prop_clauses_file            -
% 4.04/0.99  --dbg_out_stat                          false
% 4.04/0.99  ------ Parsing...
% 4.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/0.99  ------ Proving...
% 4.04/0.99  ------ Problem Properties 
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  clauses                                 13
% 4.04/0.99  conjectures                             4
% 4.04/0.99  EPR                                     4
% 4.04/0.99  Horn                                    12
% 4.04/0.99  unary                                   5
% 4.04/0.99  binary                                  4
% 4.04/0.99  lits                                    27
% 4.04/0.99  lits eq                                 1
% 4.04/0.99  fd_pure                                 0
% 4.04/0.99  fd_pseudo                               0
% 4.04/0.99  fd_cond                                 0
% 4.04/0.99  fd_pseudo_cond                          0
% 4.04/0.99  AC symbols                              0
% 4.04/0.99  
% 4.04/0.99  ------ Input Options Time Limit: Unbounded
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  ------ 
% 4.04/0.99  Current options:
% 4.04/0.99  ------ 
% 4.04/0.99  
% 4.04/0.99  ------ Input Options
% 4.04/0.99  
% 4.04/0.99  --out_options                           all
% 4.04/0.99  --tptp_safe_out                         true
% 4.04/0.99  --problem_path                          ""
% 4.04/0.99  --include_path                          ""
% 4.04/0.99  --clausifier                            res/vclausify_rel
% 4.04/0.99  --clausifier_options                    --mode clausify
% 4.04/0.99  --stdin                                 false
% 4.04/0.99  --stats_out                             sel
% 4.04/0.99  
% 4.04/0.99  ------ General Options
% 4.04/0.99  
% 4.04/0.99  --fof                                   false
% 4.04/0.99  --time_out_real                         604.99
% 4.04/0.99  --time_out_virtual                      -1.
% 4.04/0.99  --symbol_type_check                     false
% 4.04/0.99  --clausify_out                          false
% 4.04/0.99  --sig_cnt_out                           false
% 4.04/0.99  --trig_cnt_out                          false
% 4.04/0.99  --trig_cnt_out_tolerance                1.
% 4.04/0.99  --trig_cnt_out_sk_spl                   false
% 4.04/0.99  --abstr_cl_out                          false
% 4.04/0.99  
% 4.04/0.99  ------ Global Options
% 4.04/0.99  
% 4.04/0.99  --schedule                              none
% 4.04/0.99  --add_important_lit                     false
% 4.04/0.99  --prop_solver_per_cl                    1000
% 4.04/0.99  --min_unsat_core                        false
% 4.04/0.99  --soft_assumptions                      false
% 4.04/0.99  --soft_lemma_size                       3
% 4.04/0.99  --prop_impl_unit_size                   0
% 4.04/0.99  --prop_impl_unit                        []
% 4.04/0.99  --share_sel_clauses                     true
% 4.04/0.99  --reset_solvers                         false
% 4.04/0.99  --bc_imp_inh                            [conj_cone]
% 4.04/0.99  --conj_cone_tolerance                   3.
% 4.04/0.99  --extra_neg_conj                        none
% 4.04/0.99  --large_theory_mode                     true
% 4.04/0.99  --prolific_symb_bound                   200
% 4.04/0.99  --lt_threshold                          2000
% 4.04/0.99  --clause_weak_htbl                      true
% 4.04/0.99  --gc_record_bc_elim                     false
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing Options
% 4.04/0.99  
% 4.04/0.99  --preprocessing_flag                    true
% 4.04/0.99  --time_out_prep_mult                    0.1
% 4.04/0.99  --splitting_mode                        input
% 4.04/0.99  --splitting_grd                         true
% 4.04/0.99  --splitting_cvd                         false
% 4.04/0.99  --splitting_cvd_svl                     false
% 4.04/0.99  --splitting_nvd                         32
% 4.04/0.99  --sub_typing                            true
% 4.04/0.99  --prep_gs_sim                           false
% 4.04/0.99  --prep_unflatten                        true
% 4.04/0.99  --prep_res_sim                          true
% 4.04/0.99  --prep_upred                            true
% 4.04/0.99  --prep_sem_filter                       exhaustive
% 4.04/0.99  --prep_sem_filter_out                   false
% 4.04/0.99  --pred_elim                             false
% 4.04/0.99  --res_sim_input                         true
% 4.04/0.99  --eq_ax_congr_red                       true
% 4.04/0.99  --pure_diseq_elim                       true
% 4.04/0.99  --brand_transform                       false
% 4.04/0.99  --non_eq_to_eq                          false
% 4.04/0.99  --prep_def_merge                        true
% 4.04/0.99  --prep_def_merge_prop_impl              false
% 4.04/0.99  --prep_def_merge_mbd                    true
% 4.04/0.99  --prep_def_merge_tr_red                 false
% 4.04/0.99  --prep_def_merge_tr_cl                  false
% 4.04/0.99  --smt_preprocessing                     true
% 4.04/0.99  --smt_ac_axioms                         fast
% 4.04/0.99  --preprocessed_out                      false
% 4.04/0.99  --preprocessed_stats                    false
% 4.04/0.99  
% 4.04/0.99  ------ Abstraction refinement Options
% 4.04/0.99  
% 4.04/0.99  --abstr_ref                             []
% 4.04/0.99  --abstr_ref_prep                        false
% 4.04/0.99  --abstr_ref_until_sat                   false
% 4.04/0.99  --abstr_ref_sig_restrict                funpre
% 4.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/0.99  --abstr_ref_under                       []
% 4.04/0.99  
% 4.04/0.99  ------ SAT Options
% 4.04/0.99  
% 4.04/0.99  --sat_mode                              false
% 4.04/0.99  --sat_fm_restart_options                ""
% 4.04/0.99  --sat_gr_def                            false
% 4.04/0.99  --sat_epr_types                         true
% 4.04/0.99  --sat_non_cyclic_types                  false
% 4.04/0.99  --sat_finite_models                     false
% 4.04/0.99  --sat_fm_lemmas                         false
% 4.04/0.99  --sat_fm_prep                           false
% 4.04/0.99  --sat_fm_uc_incr                        true
% 4.04/0.99  --sat_out_model                         small
% 4.04/0.99  --sat_out_clauses                       false
% 4.04/0.99  
% 4.04/0.99  ------ QBF Options
% 4.04/0.99  
% 4.04/0.99  --qbf_mode                              false
% 4.04/0.99  --qbf_elim_univ                         false
% 4.04/0.99  --qbf_dom_inst                          none
% 4.04/0.99  --qbf_dom_pre_inst                      false
% 4.04/0.99  --qbf_sk_in                             false
% 4.04/0.99  --qbf_pred_elim                         true
% 4.04/0.99  --qbf_split                             512
% 4.04/0.99  
% 4.04/0.99  ------ BMC1 Options
% 4.04/0.99  
% 4.04/0.99  --bmc1_incremental                      false
% 4.04/0.99  --bmc1_axioms                           reachable_all
% 4.04/0.99  --bmc1_min_bound                        0
% 4.04/0.99  --bmc1_max_bound                        -1
% 4.04/0.99  --bmc1_max_bound_default                -1
% 4.04/0.99  --bmc1_symbol_reachability              true
% 4.04/0.99  --bmc1_property_lemmas                  false
% 4.04/0.99  --bmc1_k_induction                      false
% 4.04/0.99  --bmc1_non_equiv_states                 false
% 4.04/0.99  --bmc1_deadlock                         false
% 4.04/0.99  --bmc1_ucm                              false
% 4.04/0.99  --bmc1_add_unsat_core                   none
% 4.04/0.99  --bmc1_unsat_core_children              false
% 4.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/0.99  --bmc1_out_stat                         full
% 4.04/0.99  --bmc1_ground_init                      false
% 4.04/0.99  --bmc1_pre_inst_next_state              false
% 4.04/0.99  --bmc1_pre_inst_state                   false
% 4.04/0.99  --bmc1_pre_inst_reach_state             false
% 4.04/0.99  --bmc1_out_unsat_core                   false
% 4.04/0.99  --bmc1_aig_witness_out                  false
% 4.04/0.99  --bmc1_verbose                          false
% 4.04/0.99  --bmc1_dump_clauses_tptp                false
% 4.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.04/0.99  --bmc1_dump_file                        -
% 4.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.04/0.99  --bmc1_ucm_extend_mode                  1
% 4.04/0.99  --bmc1_ucm_init_mode                    2
% 4.04/0.99  --bmc1_ucm_cone_mode                    none
% 4.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.04/0.99  --bmc1_ucm_relax_model                  4
% 4.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/0.99  --bmc1_ucm_layered_model                none
% 4.04/0.99  --bmc1_ucm_max_lemma_size               10
% 4.04/0.99  
% 4.04/0.99  ------ AIG Options
% 4.04/0.99  
% 4.04/0.99  --aig_mode                              false
% 4.04/0.99  
% 4.04/0.99  ------ Instantiation Options
% 4.04/0.99  
% 4.04/0.99  --instantiation_flag                    true
% 4.04/0.99  --inst_sos_flag                         false
% 4.04/0.99  --inst_sos_phase                        true
% 4.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel_side                     num_symb
% 4.04/0.99  --inst_solver_per_active                1400
% 4.04/0.99  --inst_solver_calls_frac                1.
% 4.04/0.99  --inst_passive_queue_type               priority_queues
% 4.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/0.99  --inst_passive_queues_freq              [25;2]
% 4.04/0.99  --inst_dismatching                      true
% 4.04/0.99  --inst_eager_unprocessed_to_passive     true
% 4.04/0.99  --inst_prop_sim_given                   true
% 4.04/0.99  --inst_prop_sim_new                     false
% 4.04/0.99  --inst_subs_new                         false
% 4.04/0.99  --inst_eq_res_simp                      false
% 4.04/0.99  --inst_subs_given                       false
% 4.04/0.99  --inst_orphan_elimination               true
% 4.04/0.99  --inst_learning_loop_flag               true
% 4.04/0.99  --inst_learning_start                   3000
% 4.04/0.99  --inst_learning_factor                  2
% 4.04/0.99  --inst_start_prop_sim_after_learn       3
% 4.04/0.99  --inst_sel_renew                        solver
% 4.04/0.99  --inst_lit_activity_flag                true
% 4.04/0.99  --inst_restr_to_given                   false
% 4.04/0.99  --inst_activity_threshold               500
% 4.04/0.99  --inst_out_proof                        true
% 4.04/0.99  
% 4.04/0.99  ------ Resolution Options
% 4.04/0.99  
% 4.04/0.99  --resolution_flag                       true
% 4.04/0.99  --res_lit_sel                           adaptive
% 4.04/0.99  --res_lit_sel_side                      none
% 4.04/0.99  --res_ordering                          kbo
% 4.04/0.99  --res_to_prop_solver                    active
% 4.04/0.99  --res_prop_simpl_new                    false
% 4.04/0.99  --res_prop_simpl_given                  true
% 4.04/0.99  --res_passive_queue_type                priority_queues
% 4.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/0.99  --res_passive_queues_freq               [15;5]
% 4.04/0.99  --res_forward_subs                      full
% 4.04/0.99  --res_backward_subs                     full
% 4.04/0.99  --res_forward_subs_resolution           true
% 4.04/0.99  --res_backward_subs_resolution          true
% 4.04/0.99  --res_orphan_elimination                true
% 4.04/0.99  --res_time_limit                        2.
% 4.04/0.99  --res_out_proof                         true
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Options
% 4.04/0.99  
% 4.04/0.99  --superposition_flag                    true
% 4.04/0.99  --sup_passive_queue_type                priority_queues
% 4.04/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/0.99  --sup_passive_queues_freq               [1;4]
% 4.04/0.99  --demod_completeness_check              fast
% 4.04/0.99  --demod_use_ground                      true
% 4.04/0.99  --sup_to_prop_solver                    passive
% 4.04/0.99  --sup_prop_simpl_new                    true
% 4.04/0.99  --sup_prop_simpl_given                  true
% 4.04/0.99  --sup_fun_splitting                     false
% 4.04/0.99  --sup_smt_interval                      50000
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Simplification Setup
% 4.04/0.99  
% 4.04/0.99  --sup_indices_passive                   []
% 4.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/0.99  --sup_full_bw                           [BwDemod]
% 4.04/0.99  --sup_immed_triv                        [TrivRules]
% 4.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/0.99  --sup_immed_bw_main                     []
% 4.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/0.99  
% 4.04/0.99  ------ Combination Options
% 4.04/0.99  
% 4.04/0.99  --comb_res_mult                         3
% 4.04/0.99  --comb_sup_mult                         2
% 4.04/0.99  --comb_inst_mult                        10
% 4.04/0.99  
% 4.04/0.99  ------ Debug Options
% 4.04/0.99  
% 4.04/0.99  --dbg_backtrace                         false
% 4.04/0.99  --dbg_dump_prop_clauses                 false
% 4.04/0.99  --dbg_dump_prop_clauses_file            -
% 4.04/0.99  --dbg_out_stat                          false
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  ------ Proving...
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  % SZS status Theorem for theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  fof(f1,axiom,(
% 4.04/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f9,plain,(
% 4.04/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.04/0.99    inference(ennf_transformation,[],[f1])).
% 4.04/0.99  
% 4.04/0.99  fof(f18,plain,(
% 4.04/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/0.99    inference(nnf_transformation,[],[f9])).
% 4.04/0.99  
% 4.04/0.99  fof(f19,plain,(
% 4.04/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/0.99    inference(rectify,[],[f18])).
% 4.04/0.99  
% 4.04/0.99  fof(f20,plain,(
% 4.04/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.04/0.99    introduced(choice_axiom,[])).
% 4.04/0.99  
% 4.04/0.99  fof(f21,plain,(
% 4.04/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 4.04/0.99  
% 4.04/0.99  fof(f26,plain,(
% 4.04/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f21])).
% 4.04/0.99  
% 4.04/0.99  fof(f6,axiom,(
% 4.04/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 4.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f14,plain,(
% 4.04/0.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.04/0.99    inference(ennf_transformation,[],[f6])).
% 4.04/0.99  
% 4.04/0.99  fof(f15,plain,(
% 4.04/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.04/0.99    inference(flattening,[],[f14])).
% 4.04/0.99  
% 4.04/0.99  fof(f32,plain,(
% 4.04/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f15])).
% 4.04/0.99  
% 4.04/0.99  fof(f25,plain,(
% 4.04/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f21])).
% 4.04/0.99  
% 4.04/0.99  fof(f7,conjecture,(
% 4.04/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 4.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f8,negated_conjecture,(
% 4.04/0.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 4.04/0.99    inference(negated_conjecture,[],[f7])).
% 4.04/0.99  
% 4.04/0.99  fof(f16,plain,(
% 4.04/0.99    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 4.04/0.99    inference(ennf_transformation,[],[f8])).
% 4.04/0.99  
% 4.04/0.99  fof(f17,plain,(
% 4.04/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 4.04/0.99    inference(flattening,[],[f16])).
% 4.04/0.99  
% 4.04/0.99  fof(f23,plain,(
% 4.04/0.99    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK2)) & r1_tarski(X0,sK2) & v1_relat_1(sK2))) )),
% 4.04/0.99    introduced(choice_axiom,[])).
% 4.04/0.99  
% 4.04/0.99  fof(f22,plain,(
% 4.04/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK1),k3_relat_1(X1)) & r1_tarski(sK1,X1) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 4.04/0.99    introduced(choice_axiom,[])).
% 4.04/0.99  
% 4.04/0.99  fof(f24,plain,(
% 4.04/0.99    (~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 4.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f23,f22])).
% 4.04/0.99  
% 4.04/0.99  fof(f35,plain,(
% 4.04/0.99    v1_relat_1(sK2)),
% 4.04/0.99    inference(cnf_transformation,[],[f24])).
% 4.04/0.99  
% 4.04/0.99  fof(f5,axiom,(
% 4.04/0.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 4.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f13,plain,(
% 4.04/0.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 4.04/0.99    inference(ennf_transformation,[],[f5])).
% 4.04/0.99  
% 4.04/0.99  fof(f31,plain,(
% 4.04/0.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f13])).
% 4.04/0.99  
% 4.04/0.99  fof(f3,axiom,(
% 4.04/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f29,plain,(
% 4.04/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.04/0.99    inference(cnf_transformation,[],[f3])).
% 4.04/0.99  
% 4.04/0.99  fof(f27,plain,(
% 4.04/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f21])).
% 4.04/0.99  
% 4.04/0.99  fof(f33,plain,(
% 4.04/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f15])).
% 4.04/0.99  
% 4.04/0.99  fof(f2,axiom,(
% 4.04/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 4.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f10,plain,(
% 4.04/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.04/0.99    inference(ennf_transformation,[],[f2])).
% 4.04/0.99  
% 4.04/0.99  fof(f28,plain,(
% 4.04/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f10])).
% 4.04/0.99  
% 4.04/0.99  fof(f4,axiom,(
% 4.04/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 4.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f11,plain,(
% 4.04/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 4.04/0.99    inference(ennf_transformation,[],[f4])).
% 4.04/0.99  
% 4.04/0.99  fof(f12,plain,(
% 4.04/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 4.04/0.99    inference(flattening,[],[f11])).
% 4.04/0.99  
% 4.04/0.99  fof(f30,plain,(
% 4.04/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f12])).
% 4.04/0.99  
% 4.04/0.99  fof(f37,plain,(
% 4.04/0.99    ~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))),
% 4.04/0.99    inference(cnf_transformation,[],[f24])).
% 4.04/0.99  
% 4.04/0.99  fof(f36,plain,(
% 4.04/0.99    r1_tarski(sK1,sK2)),
% 4.04/0.99    inference(cnf_transformation,[],[f24])).
% 4.04/0.99  
% 4.04/0.99  fof(f34,plain,(
% 4.04/0.99    v1_relat_1(sK1)),
% 4.04/0.99    inference(cnf_transformation,[],[f24])).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1,plain,
% 4.04/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 4.04/0.99      inference(cnf_transformation,[],[f26]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_128,plain,
% 4.04/0.99      ( r2_hidden(sK0(X0_38,X1_38),X0_38) | r1_tarski(X0_38,X1_38) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_363,plain,
% 4.04/0.99      ( r2_hidden(sK0(X0_38,X1_38),X0_38) = iProver_top
% 4.04/0.99      | r1_tarski(X0_38,X1_38) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_128]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8,plain,
% 4.04/0.99      ( ~ r1_tarski(X0,X1)
% 4.04/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 4.04/0.99      | ~ v1_relat_1(X0)
% 4.04/0.99      | ~ v1_relat_1(X1) ),
% 4.04/0.99      inference(cnf_transformation,[],[f32]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_121,plain,
% 4.04/0.99      ( ~ r1_tarski(X0_38,X1_38)
% 4.04/0.99      | r1_tarski(k1_relat_1(X0_38),k1_relat_1(X1_38))
% 4.04/0.99      | ~ v1_relat_1(X0_38)
% 4.04/0.99      | ~ v1_relat_1(X1_38) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_370,plain,
% 4.04/0.99      ( r1_tarski(X0_38,X1_38) != iProver_top
% 4.04/0.99      | r1_tarski(k1_relat_1(X0_38),k1_relat_1(X1_38)) = iProver_top
% 4.04/0.99      | v1_relat_1(X0_38) != iProver_top
% 4.04/0.99      | v1_relat_1(X1_38) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_121]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_2,plain,
% 4.04/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 4.04/0.99      inference(cnf_transformation,[],[f25]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_127,plain,
% 4.04/0.99      ( ~ r2_hidden(X0_39,X0_38)
% 4.04/0.99      | r2_hidden(X0_39,X1_38)
% 4.04/0.99      | ~ r1_tarski(X0_38,X1_38) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_364,plain,
% 4.04/0.99      ( r2_hidden(X0_39,X0_38) != iProver_top
% 4.04/0.99      | r2_hidden(X0_39,X1_38) = iProver_top
% 4.04/0.99      | r1_tarski(X0_38,X1_38) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1077,plain,
% 4.04/0.99      ( r2_hidden(X0_39,k1_relat_1(X0_38)) != iProver_top
% 4.04/0.99      | r2_hidden(X0_39,k1_relat_1(X1_38)) = iProver_top
% 4.04/0.99      | r1_tarski(X0_38,X1_38) != iProver_top
% 4.04/0.99      | v1_relat_1(X0_38) != iProver_top
% 4.04/0.99      | v1_relat_1(X1_38) != iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_370,c_364]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_2738,plain,
% 4.04/0.99      ( r2_hidden(sK0(k1_relat_1(X0_38),X1_38),k1_relat_1(X2_38)) = iProver_top
% 4.04/0.99      | r1_tarski(X0_38,X2_38) != iProver_top
% 4.04/0.99      | r1_tarski(k1_relat_1(X0_38),X1_38) = iProver_top
% 4.04/0.99      | v1_relat_1(X0_38) != iProver_top
% 4.04/0.99      | v1_relat_1(X2_38) != iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_363,c_1077]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_11,negated_conjecture,
% 4.04/0.99      ( v1_relat_1(sK2) ),
% 4.04/0.99      inference(cnf_transformation,[],[f35]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_118,negated_conjecture,
% 4.04/0.99      ( v1_relat_1(sK2) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_373,plain,
% 4.04/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_118]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_6,plain,
% 4.04/0.99      ( ~ v1_relat_1(X0)
% 4.04/0.99      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 4.04/0.99      inference(cnf_transformation,[],[f31]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_123,plain,
% 4.04/0.99      ( ~ v1_relat_1(X0_38)
% 4.04/0.99      | k2_xboole_0(k1_relat_1(X0_38),k2_relat_1(X0_38)) = k3_relat_1(X0_38) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_368,plain,
% 4.04/0.99      ( k2_xboole_0(k1_relat_1(X0_38),k2_relat_1(X0_38)) = k3_relat_1(X0_38)
% 4.04/0.99      | v1_relat_1(X0_38) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_123]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_785,plain,
% 4.04/0.99      ( k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) = k3_relat_1(sK2) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_373,c_368]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_4,plain,
% 4.04/0.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 4.04/0.99      inference(cnf_transformation,[],[f29]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_125,plain,
% 4.04/0.99      ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_366,plain,
% 4.04/0.99      ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_796,plain,
% 4.04/0.99      ( r2_hidden(X0_39,X0_38) != iProver_top
% 4.04/0.99      | r2_hidden(X0_39,k2_xboole_0(X0_38,X1_38)) = iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_366,c_364]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_0,plain,
% 4.04/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 4.04/0.99      inference(cnf_transformation,[],[f27]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_129,plain,
% 4.04/0.99      ( ~ r2_hidden(sK0(X0_38,X1_38),X1_38) | r1_tarski(X0_38,X1_38) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_362,plain,
% 4.04/0.99      ( r2_hidden(sK0(X0_38,X1_38),X1_38) != iProver_top
% 4.04/0.99      | r1_tarski(X0_38,X1_38) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_129]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1805,plain,
% 4.04/0.99      ( r2_hidden(sK0(X0_38,k2_xboole_0(X1_38,X2_38)),X1_38) != iProver_top
% 4.04/0.99      | r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38)) = iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_796,c_362]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_2570,plain,
% 4.04/0.99      ( r2_hidden(sK0(X0_38,k3_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top
% 4.04/0.99      | r1_tarski(X0_38,k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_785,c_1805]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_2573,plain,
% 4.04/0.99      ( r2_hidden(sK0(X0_38,k3_relat_1(sK2)),k1_relat_1(sK2)) != iProver_top
% 4.04/0.99      | r1_tarski(X0_38,k3_relat_1(sK2)) = iProver_top ),
% 4.04/0.99      inference(light_normalisation,[status(thm)],[c_2570,c_785]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_17686,plain,
% 4.04/0.99      ( r1_tarski(X0_38,sK2) != iProver_top
% 4.04/0.99      | r1_tarski(k1_relat_1(X0_38),k3_relat_1(sK2)) = iProver_top
% 4.04/0.99      | v1_relat_1(X0_38) != iProver_top
% 4.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_2738,c_2573]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_17710,plain,
% 4.04/0.99      ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) = iProver_top
% 4.04/0.99      | r1_tarski(sK1,sK2) != iProver_top
% 4.04/0.99      | v1_relat_1(sK2) != iProver_top
% 4.04/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_17686]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_7,plain,
% 4.04/0.99      ( ~ r1_tarski(X0,X1)
% 4.04/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 4.04/0.99      | ~ v1_relat_1(X0)
% 4.04/0.99      | ~ v1_relat_1(X1) ),
% 4.04/0.99      inference(cnf_transformation,[],[f33]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_122,plain,
% 4.04/0.99      ( ~ r1_tarski(X0_38,X1_38)
% 4.04/0.99      | r1_tarski(k2_relat_1(X0_38),k2_relat_1(X1_38))
% 4.04/0.99      | ~ v1_relat_1(X0_38)
% 4.04/0.99      | ~ v1_relat_1(X1_38) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_369,plain,
% 4.04/0.99      ( r1_tarski(X0_38,X1_38) != iProver_top
% 4.04/0.99      | r1_tarski(k2_relat_1(X0_38),k2_relat_1(X1_38)) = iProver_top
% 4.04/0.99      | v1_relat_1(X0_38) != iProver_top
% 4.04/0.99      | v1_relat_1(X1_38) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_122]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_3,plain,
% 4.04/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 4.04/0.99      inference(cnf_transformation,[],[f28]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_126,plain,
% 4.04/0.99      ( ~ r1_tarski(X0_38,X1_38)
% 4.04/0.99      | r1_tarski(X0_38,k2_xboole_0(X2_38,X1_38)) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_365,plain,
% 4.04/0.99      ( r1_tarski(X0_38,X1_38) != iProver_top
% 4.04/0.99      | r1_tarski(X0_38,k2_xboole_0(X2_38,X1_38)) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_126]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1250,plain,
% 4.04/0.99      ( r1_tarski(X0_38,k3_relat_1(sK2)) = iProver_top
% 4.04/0.99      | r1_tarski(X0_38,k2_relat_1(sK2)) != iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_785,c_365]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1895,plain,
% 4.04/0.99      ( r1_tarski(X0_38,sK2) != iProver_top
% 4.04/0.99      | r1_tarski(k2_relat_1(X0_38),k3_relat_1(sK2)) = iProver_top
% 4.04/0.99      | v1_relat_1(X0_38) != iProver_top
% 4.04/0.99      | v1_relat_1(sK2) != iProver_top ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_369,c_1250]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1915,plain,
% 4.04/0.99      ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2)) = iProver_top
% 4.04/0.99      | r1_tarski(sK1,sK2) != iProver_top
% 4.04/0.99      | v1_relat_1(sK2) != iProver_top
% 4.04/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_1895]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_5,plain,
% 4.04/0.99      ( ~ r1_tarski(X0,X1)
% 4.04/0.99      | ~ r1_tarski(X2,X1)
% 4.04/0.99      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.04/0.99      inference(cnf_transformation,[],[f30]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_124,plain,
% 4.04/0.99      ( ~ r1_tarski(X0_38,X1_38)
% 4.04/0.99      | ~ r1_tarski(X2_38,X1_38)
% 4.04/0.99      | r1_tarski(k2_xboole_0(X0_38,X2_38),X1_38) ),
% 4.04/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1024,plain,
% 4.04/0.99      ( r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2))
% 4.04/0.99      | ~ r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2))
% 4.04/0.99      | ~ r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_124]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1025,plain,
% 4.04/0.99      ( r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2)) = iProver_top
% 4.04/0.99      | r1_tarski(k2_relat_1(sK1),k3_relat_1(sK2)) != iProver_top
% 4.04/0.99      | r1_tarski(k1_relat_1(sK1),k3_relat_1(sK2)) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_134,plain,
% 4.04/0.99      ( ~ r1_tarski(X0_38,X1_38)
% 4.04/0.99      | r1_tarski(X2_38,X3_38)
% 4.04/0.99      | X2_38 != X0_38
% 4.04/0.99      | X3_38 != X1_38 ),
% 4.04/0.99      theory(equality) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_492,plain,
% 4.04/0.99      ( ~ r1_tarski(X0_38,X1_38)
% 4.04/0.99      | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
% 4.04/0.99      | k3_relat_1(sK2) != X1_38
% 4.04/0.99      | k3_relat_1(sK1) != X0_38 ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_134]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_753,plain,
% 4.04/0.99      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),X0_38)
% 4.04/0.99      | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
% 4.04/0.99      | k3_relat_1(sK2) != X0_38
% 4.04/0.99      | k3_relat_1(sK1) != k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_492]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_841,plain,
% 4.04/0.99      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2))
% 4.04/0.99      | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2))
% 4.04/0.99      | k3_relat_1(sK2) != k3_relat_1(sK2)
% 4.04/0.99      | k3_relat_1(sK1) != k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_753]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_842,plain,
% 4.04/0.99      ( k3_relat_1(sK2) != k3_relat_1(sK2)
% 4.04/0.99      | k3_relat_1(sK1) != k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
% 4.04/0.99      | r1_tarski(k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)),k3_relat_1(sK2)) != iProver_top
% 4.04/0.99      | r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_133,plain,
% 4.04/0.99      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 4.04/0.99      theory(equality) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_537,plain,
% 4.04/0.99      ( X0_38 != X1_38
% 4.04/0.99      | k3_relat_1(sK1) != X1_38
% 4.04/0.99      | k3_relat_1(sK1) = X0_38 ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_133]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_550,plain,
% 4.04/0.99      ( X0_38 != k3_relat_1(sK1)
% 4.04/0.99      | k3_relat_1(sK1) = X0_38
% 4.04/0.99      | k3_relat_1(sK1) != k3_relat_1(sK1) ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_537]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_639,plain,
% 4.04/0.99      ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) != k3_relat_1(sK1)
% 4.04/0.99      | k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
% 4.04/0.99      | k3_relat_1(sK1) != k3_relat_1(sK1) ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_550]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_131,plain,( X0_38 = X0_38 ),theory(equality) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_630,plain,
% 4.04/0.99      ( k3_relat_1(sK2) = k3_relat_1(sK2) ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_131]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_154,plain,
% 4.04/0.99      ( ~ v1_relat_1(sK1)
% 4.04/0.99      | k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_123]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_145,plain,
% 4.04/0.99      ( sK1 = sK1 ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_131]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_137,plain,
% 4.04/0.99      ( X0_38 != X1_38 | k3_relat_1(X0_38) = k3_relat_1(X1_38) ),
% 4.04/0.99      theory(equality) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_142,plain,
% 4.04/0.99      ( k3_relat_1(sK1) = k3_relat_1(sK1) | sK1 != sK1 ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_137]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_9,negated_conjecture,
% 4.04/0.99      ( ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) ),
% 4.04/0.99      inference(cnf_transformation,[],[f37]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_16,plain,
% 4.04/0.99      ( r1_tarski(k3_relat_1(sK1),k3_relat_1(sK2)) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_10,negated_conjecture,
% 4.04/0.99      ( r1_tarski(sK1,sK2) ),
% 4.04/0.99      inference(cnf_transformation,[],[f36]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_15,plain,
% 4.04/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_14,plain,
% 4.04/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_12,negated_conjecture,
% 4.04/0.99      ( v1_relat_1(sK1) ),
% 4.04/0.99      inference(cnf_transformation,[],[f34]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_13,plain,
% 4.04/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(contradiction,plain,
% 4.04/0.99      ( $false ),
% 4.04/0.99      inference(minisat,
% 4.04/0.99                [status(thm)],
% 4.04/0.99                [c_17710,c_1915,c_1025,c_842,c_639,c_630,c_154,c_145,
% 4.04/0.99                 c_142,c_16,c_15,c_14,c_13,c_12]) ).
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  ------                               Statistics
% 4.04/0.99  
% 4.04/0.99  ------ Selected
% 4.04/0.99  
% 4.04/0.99  total_time:                             0.472
% 4.04/0.99  
%------------------------------------------------------------------------------
