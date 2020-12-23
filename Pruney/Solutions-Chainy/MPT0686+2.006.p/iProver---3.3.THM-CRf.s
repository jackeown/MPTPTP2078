%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:29 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 179 expanded)
%              Number of clauses        :   43 (  65 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  215 ( 593 expanded)
%              Number of equality atoms :   54 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
     => ( ~ r1_xboole_0(k10_relat_1(X0,sK3),k10_relat_1(X0,sK4))
        & r1_xboole_0(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK2,X1),k10_relat_1(sK2,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4))
    & r1_xboole_0(sK3,sK4)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f23,f22])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_632,plain,
    ( k3_xboole_0(X0_43,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_190,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_191,plain,
    ( ~ v1_relat_1(sK2)
    | k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_195,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_191,c_14])).

cnf(c_629,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0_43),k10_relat_1(sK2,X1_43)) = k10_relat_1(sK2,k3_xboole_0(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_195])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_637,plain,
    ( r1_xboole_0(X0_43,X1_43)
    | k3_xboole_0(X0_43,X1_43) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_969,plain,
    ( k3_xboole_0(X0_43,X1_43) != k1_xboole_0
    | r1_xboole_0(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_1150,plain,
    ( r1_xboole_0(X0_43,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_969])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_633,plain,
    ( r2_hidden(sK0(X0_43,X1_43),X0_43)
    | r1_xboole_0(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_973,plain,
    ( r2_hidden(sK0(X0_43,X1_43),X0_43) = iProver_top
    | r1_xboole_0(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
    | r2_hidden(sK1(X0,X1,sK2),X1) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_625,plain,
    ( ~ r2_hidden(X0_42,k10_relat_1(sK2,X0_43))
    | r2_hidden(sK1(X0_42,X0_43,sK2),X0_43) ),
    inference(subtyping,[status(esa)],[c_245])).

cnf(c_979,plain,
    ( r2_hidden(X0_42,k10_relat_1(sK2,X0_43)) != iProver_top
    | r2_hidden(sK1(X0_42,X0_43,sK2),X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_635,plain,
    ( ~ r2_hidden(X0_42,X0_43)
    | ~ r2_hidden(X0_42,X1_43)
    | ~ r1_xboole_0(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_971,plain,
    ( r2_hidden(X0_42,X0_43) != iProver_top
    | r2_hidden(X0_42,X1_43) != iProver_top
    | r1_xboole_0(X1_43,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_2405,plain,
    ( r2_hidden(X0_42,k10_relat_1(sK2,X0_43)) != iProver_top
    | r2_hidden(sK1(X0_42,X0_43,sK2),X1_43) != iProver_top
    | r1_xboole_0(X0_43,X1_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_971])).

cnf(c_2527,plain,
    ( r2_hidden(X0_42,k10_relat_1(sK2,X0_43)) != iProver_top
    | r1_xboole_0(X0_43,X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_2405])).

cnf(c_2605,plain,
    ( r1_xboole_0(X0_43,X0_43) != iProver_top
    | r1_xboole_0(k10_relat_1(sK2,X0_43),X1_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_2527])).

cnf(c_2720,plain,
    ( r1_xboole_0(k10_relat_1(sK2,k1_xboole_0),X0_43) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_2605])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_636,plain,
    ( ~ r1_xboole_0(X0_43,X1_43)
    | k3_xboole_0(X0_43,X1_43) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_970,plain,
    ( k3_xboole_0(X0_43,X1_43) = k1_xboole_0
    | r1_xboole_0(X0_43,X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_2727,plain,
    ( k3_xboole_0(k10_relat_1(sK2,k1_xboole_0),X0_43) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2720,c_970])).

cnf(c_2777,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k1_xboole_0,X0_43)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_629,c_2727])).

cnf(c_3082,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_632,c_2777])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_630,negated_conjecture,
    ( r1_xboole_0(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_975,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1158,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_975,c_970])).

cnf(c_1149,plain,
    ( k10_relat_1(sK2,k3_xboole_0(X0_43,X1_43)) != k1_xboole_0
    | r1_xboole_0(k10_relat_1(sK2,X0_43),k10_relat_1(sK2,X1_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_969])).

cnf(c_1557,plain,
    ( k10_relat_1(sK2,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1149])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3082,c_1557,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.29/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.98  
% 3.29/0.98  ------  iProver source info
% 3.29/0.98  
% 3.29/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.98  git: non_committed_changes: false
% 3.29/0.98  git: last_make_outside_of_git: false
% 3.29/0.98  
% 3.29/0.98  ------ 
% 3.29/0.98  ------ Parsing...
% 3.29/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.98  ------ Proving...
% 3.29/0.98  ------ Problem Properties 
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  clauses                                 13
% 3.29/0.98  conjectures                             2
% 3.29/0.98  EPR                                     2
% 3.29/0.98  Horn                                    11
% 3.29/0.98  unary                                   4
% 3.29/0.98  binary                                  7
% 3.29/0.98  lits                                    25
% 3.29/0.98  lits eq                                 4
% 3.29/0.98  fd_pure                                 0
% 3.29/0.98  fd_pseudo                               0
% 3.29/0.98  fd_cond                                 0
% 3.29/0.98  fd_pseudo_cond                          0
% 3.29/0.98  AC symbols                              0
% 3.29/0.98  
% 3.29/0.98  ------ Input Options Time Limit: Unbounded
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  ------ 
% 3.29/0.98  Current options:
% 3.29/0.98  ------ 
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  ------ Proving...
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  % SZS status Theorem for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  fof(f3,axiom,(
% 3.29/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f30,plain,(
% 3.29/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.29/0.98    inference(cnf_transformation,[],[f3])).
% 3.29/0.98  
% 3.29/0.98  fof(f5,axiom,(
% 3.29/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f11,plain,(
% 3.29/0.98    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.29/0.98    inference(ennf_transformation,[],[f5])).
% 3.29/0.98  
% 3.29/0.98  fof(f12,plain,(
% 3.29/0.98    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.29/0.98    inference(flattening,[],[f11])).
% 3.29/0.98  
% 3.29/0.98  fof(f35,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f12])).
% 3.29/0.98  
% 3.29/0.98  fof(f6,conjecture,(
% 3.29/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f7,negated_conjecture,(
% 3.29/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 3.29/0.98    inference(negated_conjecture,[],[f6])).
% 3.29/0.98  
% 3.29/0.98  fof(f13,plain,(
% 3.29/0.98    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f7])).
% 3.29/0.98  
% 3.29/0.98  fof(f14,plain,(
% 3.29/0.98    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.29/0.98    inference(flattening,[],[f13])).
% 3.29/0.98  
% 3.29/0.98  fof(f23,plain,(
% 3.29/0.98    ( ! [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(X0,sK3),k10_relat_1(X0,sK4)) & r1_xboole_0(sK3,sK4))) )),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f22,plain,(
% 3.29/0.98    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK2,X1),k10_relat_1(sK2,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f24,plain,(
% 3.29/0.98    (~r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) & r1_xboole_0(sK3,sK4)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.29/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f23,f22])).
% 3.29/0.98  
% 3.29/0.98  fof(f37,plain,(
% 3.29/0.98    v1_funct_1(sK2)),
% 3.29/0.98    inference(cnf_transformation,[],[f24])).
% 3.29/0.98  
% 3.29/0.98  fof(f36,plain,(
% 3.29/0.98    v1_relat_1(sK2)),
% 3.29/0.98    inference(cnf_transformation,[],[f24])).
% 3.29/0.98  
% 3.29/0.98  fof(f1,axiom,(
% 3.29/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f15,plain,(
% 3.29/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.29/0.98    inference(nnf_transformation,[],[f1])).
% 3.29/0.98  
% 3.29/0.98  fof(f26,plain,(
% 3.29/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.29/0.98    inference(cnf_transformation,[],[f15])).
% 3.29/0.98  
% 3.29/0.98  fof(f2,axiom,(
% 3.29/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f8,plain,(
% 3.29/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.29/0.98    inference(rectify,[],[f2])).
% 3.29/0.98  
% 3.29/0.98  fof(f9,plain,(
% 3.29/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.29/0.98    inference(ennf_transformation,[],[f8])).
% 3.29/0.98  
% 3.29/0.98  fof(f16,plain,(
% 3.29/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f17,plain,(
% 3.29/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.29/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f16])).
% 3.29/0.98  
% 3.29/0.98  fof(f27,plain,(
% 3.29/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f17])).
% 3.29/0.98  
% 3.29/0.98  fof(f4,axiom,(
% 3.29/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f10,plain,(
% 3.29/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.29/0.98    inference(ennf_transformation,[],[f4])).
% 3.29/0.98  
% 3.29/0.98  fof(f18,plain,(
% 3.29/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.29/0.98    inference(nnf_transformation,[],[f10])).
% 3.29/0.98  
% 3.29/0.98  fof(f19,plain,(
% 3.29/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.29/0.98    inference(rectify,[],[f18])).
% 3.29/0.98  
% 3.29/0.98  fof(f20,plain,(
% 3.29/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f21,plain,(
% 3.29/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.29/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 3.29/0.98  
% 3.29/0.98  fof(f33,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f21])).
% 3.29/0.98  
% 3.29/0.98  fof(f29,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f17])).
% 3.29/0.98  
% 3.29/0.98  fof(f25,plain,(
% 3.29/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f15])).
% 3.29/0.98  
% 3.29/0.98  fof(f38,plain,(
% 3.29/0.98    r1_xboole_0(sK3,sK4)),
% 3.29/0.98    inference(cnf_transformation,[],[f24])).
% 3.29/0.98  
% 3.29/0.98  fof(f39,plain,(
% 3.29/0.98    ~r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4))),
% 3.29/0.98    inference(cnf_transformation,[],[f24])).
% 3.29/0.98  
% 3.29/0.98  cnf(c_5,plain,
% 3.29/0.98      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.29/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_632,plain,
% 3.29/0.98      ( k3_xboole_0(X0_43,k1_xboole_0) = k1_xboole_0 ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_10,plain,
% 3.29/0.98      ( ~ v1_funct_1(X0)
% 3.29/0.98      | ~ v1_relat_1(X0)
% 3.29/0.98      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 3.29/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_13,negated_conjecture,
% 3.29/0.98      ( v1_funct_1(sK2) ),
% 3.29/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_190,plain,
% 3.29/0.98      ( ~ v1_relat_1(X0)
% 3.29/0.98      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
% 3.29/0.98      | sK2 != X0 ),
% 3.29/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_191,plain,
% 3.29/0.98      ( ~ v1_relat_1(sK2)
% 3.29/0.98      | k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
% 3.29/0.98      inference(unflattening,[status(thm)],[c_190]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_14,negated_conjecture,
% 3.29/0.98      ( v1_relat_1(sK2) ),
% 3.29/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_195,plain,
% 3.29/0.98      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_191,c_14]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_629,plain,
% 3.29/0.98      ( k3_xboole_0(k10_relat_1(sK2,X0_43),k10_relat_1(sK2,X1_43)) = k10_relat_1(sK2,k3_xboole_0(X0_43,X1_43)) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_195]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_0,plain,
% 3.29/0.98      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.29/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_637,plain,
% 3.29/0.98      ( r1_xboole_0(X0_43,X1_43)
% 3.29/0.98      | k3_xboole_0(X0_43,X1_43) != k1_xboole_0 ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_969,plain,
% 3.29/0.98      ( k3_xboole_0(X0_43,X1_43) != k1_xboole_0
% 3.29/0.98      | r1_xboole_0(X0_43,X1_43) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1150,plain,
% 3.29/0.98      ( r1_xboole_0(X0_43,k1_xboole_0) = iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_632,c_969]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_4,plain,
% 3.29/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_633,plain,
% 3.29/0.98      ( r2_hidden(sK0(X0_43,X1_43),X0_43) | r1_xboole_0(X0_43,X1_43) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_973,plain,
% 3.29/0.98      ( r2_hidden(sK0(X0_43,X1_43),X0_43) = iProver_top
% 3.29/0.98      | r1_xboole_0(X0_43,X1_43) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_7,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.29/0.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.29/0.98      | ~ v1_relat_1(X1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_244,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.29/0.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.29/0.98      | sK2 != X1 ),
% 3.29/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_245,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
% 3.29/0.98      | r2_hidden(sK1(X0,X1,sK2),X1) ),
% 3.29/0.98      inference(unflattening,[status(thm)],[c_244]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_625,plain,
% 3.29/0.98      ( ~ r2_hidden(X0_42,k10_relat_1(sK2,X0_43))
% 3.29/0.98      | r2_hidden(sK1(X0_42,X0_43,sK2),X0_43) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_245]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_979,plain,
% 3.29/0.98      ( r2_hidden(X0_42,k10_relat_1(sK2,X0_43)) != iProver_top
% 3.29/0.98      | r2_hidden(sK1(X0_42,X0_43,sK2),X0_43) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_635,plain,
% 3.29/0.98      ( ~ r2_hidden(X0_42,X0_43)
% 3.29/0.98      | ~ r2_hidden(X0_42,X1_43)
% 3.29/0.98      | ~ r1_xboole_0(X0_43,X1_43) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_971,plain,
% 3.29/0.98      ( r2_hidden(X0_42,X0_43) != iProver_top
% 3.29/0.98      | r2_hidden(X0_42,X1_43) != iProver_top
% 3.29/0.98      | r1_xboole_0(X1_43,X0_43) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2405,plain,
% 3.29/0.98      ( r2_hidden(X0_42,k10_relat_1(sK2,X0_43)) != iProver_top
% 3.29/0.98      | r2_hidden(sK1(X0_42,X0_43,sK2),X1_43) != iProver_top
% 3.29/0.98      | r1_xboole_0(X0_43,X1_43) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_979,c_971]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2527,plain,
% 3.29/0.98      ( r2_hidden(X0_42,k10_relat_1(sK2,X0_43)) != iProver_top
% 3.29/0.98      | r1_xboole_0(X0_43,X0_43) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_979,c_2405]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2605,plain,
% 3.29/0.98      ( r1_xboole_0(X0_43,X0_43) != iProver_top
% 3.29/0.98      | r1_xboole_0(k10_relat_1(sK2,X0_43),X1_43) = iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_973,c_2527]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2720,plain,
% 3.29/0.98      ( r1_xboole_0(k10_relat_1(sK2,k1_xboole_0),X0_43) = iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1150,c_2605]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1,plain,
% 3.29/0.98      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.29/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_636,plain,
% 3.29/0.98      ( ~ r1_xboole_0(X0_43,X1_43)
% 3.29/0.98      | k3_xboole_0(X0_43,X1_43) = k1_xboole_0 ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_970,plain,
% 3.29/0.98      ( k3_xboole_0(X0_43,X1_43) = k1_xboole_0
% 3.29/0.98      | r1_xboole_0(X0_43,X1_43) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2727,plain,
% 3.29/0.98      ( k3_xboole_0(k10_relat_1(sK2,k1_xboole_0),X0_43) = k1_xboole_0 ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_2720,c_970]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2777,plain,
% 3.29/0.98      ( k10_relat_1(sK2,k3_xboole_0(k1_xboole_0,X0_43)) = k1_xboole_0 ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_629,c_2727]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_3082,plain,
% 3.29/0.98      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_632,c_2777]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_12,negated_conjecture,
% 3.29/0.98      ( r1_xboole_0(sK3,sK4) ),
% 3.29/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_630,negated_conjecture,
% 3.29/0.98      ( r1_xboole_0(sK3,sK4) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_975,plain,
% 3.29/0.98      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1158,plain,
% 3.29/0.98      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_975,c_970]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1149,plain,
% 3.29/0.98      ( k10_relat_1(sK2,k3_xboole_0(X0_43,X1_43)) != k1_xboole_0
% 3.29/0.98      | r1_xboole_0(k10_relat_1(sK2,X0_43),k10_relat_1(sK2,X1_43)) = iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_629,c_969]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1557,plain,
% 3.29/0.98      ( k10_relat_1(sK2,k1_xboole_0) != k1_xboole_0
% 3.29/0.98      | r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1158,c_1149]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_11,negated_conjecture,
% 3.29/0.98      ( ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) ),
% 3.29/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_18,plain,
% 3.29/0.98      ( r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(contradiction,plain,
% 3.29/0.98      ( $false ),
% 3.29/0.98      inference(minisat,[status(thm)],[c_3082,c_1557,c_18]) ).
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  ------                               Statistics
% 3.29/0.98  
% 3.29/0.98  ------ Selected
% 3.29/0.98  
% 3.29/0.98  total_time:                             0.117
% 3.29/0.98  
%------------------------------------------------------------------------------
