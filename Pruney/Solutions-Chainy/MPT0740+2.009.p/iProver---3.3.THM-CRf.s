%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:32 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 169 expanded)
%              Number of clauses        :   69 (  72 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  376 ( 529 expanded)
%              Number of equality atoms :   86 (  86 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f15])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) )
     => v1_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f37])).

fof(f49,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK3))
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ v3_ordinal1(k3_tarski(sK3))
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f40])).

fof(f59,plain,(
    ~ v3_ordinal1(k3_tarski(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2528,plain,
    ( r1_ordinal1(X0,sK1(X1,X0))
    | r1_ordinal1(sK1(X1,X0),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2529,plain,
    ( r1_ordinal1(X0,sK1(X1,X0)) = iProver_top
    | r1_ordinal1(sK1(X1,X0),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2528])).

cnf(c_2531,plain,
    ( r1_ordinal1(sK1(sK3,sK3),sK3) = iProver_top
    | r1_ordinal1(sK3,sK1(sK3,sK3)) = iProver_top
    | v3_ordinal1(sK1(sK3,sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1692,plain,
    ( ~ r2_hidden(sK1(X0,X1),X2)
    | ~ v3_ordinal1(X2)
    | v3_ordinal1(sK1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1693,plain,
    ( r2_hidden(sK1(X0,X1),X2) != iProver_top
    | v3_ordinal1(X2) != iProver_top
    | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1692])).

cnf(c_1695,plain,
    ( r2_hidden(sK1(sK3,sK3),sK3) != iProver_top
    | v3_ordinal1(sK1(sK3,sK3)) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_528,plain,
    ( r2_hidden(sK0(k3_tarski(sK3),X0),k3_tarski(sK3))
    | r1_tarski(k3_tarski(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1019,plain,
    ( r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3))
    | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1022,plain,
    ( r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
    | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_529,plain,
    ( ~ r2_hidden(sK0(k3_tarski(sK3),X0),X0)
    | r1_tarski(k3_tarski(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1018,plain,
    ( ~ r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3))
    | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_1020,plain,
    ( r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
    | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_698,plain,
    ( ~ r2_hidden(sK2(k3_tarski(sK3)),X0)
    | r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3))
    | ~ r1_tarski(k3_tarski(X0),k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_699,plain,
    ( r2_hidden(sK2(k3_tarski(sK3)),X0) != iProver_top
    | r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_701,plain,
    ( r2_hidden(sK2(k3_tarski(sK3)),sK3) != iProver_top
    | r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
    | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_10,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_661,plain,
    ( ~ r1_ordinal1(X0,sK1(X0,X1))
    | r1_tarski(X0,sK1(X0,X1))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_662,plain,
    ( r1_ordinal1(X0,sK1(X0,X1)) != iProver_top
    | r1_tarski(X0,sK1(X0,X1)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_664,plain,
    ( r1_ordinal1(sK3,sK1(sK3,sK3)) != iProver_top
    | r1_tarski(sK3,sK1(sK3,sK3)) = iProver_top
    | v3_ordinal1(sK1(sK3,sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_591,plain,
    ( ~ r2_hidden(sK1(X0,X1),X0)
    | ~ r1_tarski(X0,sK1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_597,plain,
    ( r2_hidden(sK1(X0,X1),X0) != iProver_top
    | r1_tarski(X0,sK1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_599,plain,
    ( r2_hidden(sK1(sK3,sK3),sK3) != iProver_top
    | r1_tarski(sK3,sK1(sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_572,plain,
    ( ~ r1_ordinal1(sK1(X0,X1),X1)
    | r1_tarski(sK1(X0,X1),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(sK1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_573,plain,
    ( r1_ordinal1(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(sK1(X0,X1),X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_575,plain,
    ( r1_ordinal1(sK1(sK3,sK3),sK3) != iProver_top
    | r1_tarski(sK1(sK3,sK3),sK3) = iProver_top
    | v3_ordinal1(sK1(sK3,sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_519,plain,
    ( r2_hidden(sK2(k3_tarski(sK3)),X0)
    | ~ r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3))
    | ~ r1_tarski(k3_tarski(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_524,plain,
    ( r2_hidden(sK2(k3_tarski(sK3)),X0) = iProver_top
    | r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
    | r1_tarski(k3_tarski(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_526,plain,
    ( r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
    | r2_hidden(sK2(k3_tarski(sK3)),sK3) = iProver_top
    | r1_tarski(k3_tarski(sK3),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_418,plain,
    ( r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3))
    | v1_ordinal1(k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_422,plain,
    ( r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
    | v1_ordinal1(k3_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_7,plain,
    ( ~ r1_tarski(sK2(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_419,plain,
    ( ~ r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3))
    | v1_ordinal1(k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_420,plain,
    ( r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
    | v1_ordinal1(k3_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_318,plain,
    ( ~ r2_hidden(k3_tarski(sK3),X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_350,plain,
    ( ~ r2_hidden(k3_tarski(sK3),k1_ordinal1(X0))
    | ~ v3_ordinal1(k1_ordinal1(X0))
    | v3_ordinal1(k3_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_355,plain,
    ( r2_hidden(k3_tarski(sK3),k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(k3_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_357,plain,
    ( r2_hidden(k3_tarski(sK3),k1_ordinal1(sK3)) != iProver_top
    | v3_ordinal1(k1_ordinal1(sK3)) != iProver_top
    | v3_ordinal1(k3_tarski(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ v1_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_104,plain,
    ( ~ v1_ordinal1(X2)
    | ~ r1_tarski(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_13])).

cnf(c_105,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ v1_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_104])).

cnf(c_323,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(X1,k1_ordinal1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(k3_tarski(sK3),k1_ordinal1(X0))
    | ~ r1_tarski(k3_tarski(sK3),X0)
    | ~ v1_ordinal1(k3_tarski(sK3))
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_351,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
    | r2_hidden(k3_tarski(sK3),k1_ordinal1(X0)) = iProver_top
    | r1_tarski(k3_tarski(sK3),X0) != iProver_top
    | v1_ordinal1(k3_tarski(sK3)) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_353,plain,
    ( r2_hidden(k3_tarski(sK3),k1_ordinal1(sK3)) = iProver_top
    | r2_hidden(sK3,k1_ordinal1(sK3)) != iProver_top
    | r1_tarski(k3_tarski(sK3),sK3) != iProver_top
    | v1_ordinal1(k3_tarski(sK3)) != iProver_top
    | v3_ordinal1(k1_ordinal1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_3,plain,
    ( ~ r1_tarski(sK1(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_52,plain,
    ( r1_tarski(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_54,plain,
    ( r1_tarski(sK1(sK3,sK3),sK3) != iProver_top
    | r1_tarski(k3_tarski(sK3),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_49,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_51,plain,
    ( r2_hidden(sK1(sK3,sK3),sK3) = iProver_top
    | r1_tarski(k3_tarski(sK3),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_30,plain,
    ( r2_hidden(sK3,k1_ordinal1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_25,plain,
    ( v3_ordinal1(k1_ordinal1(sK3)) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_16,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( v3_ordinal1(k3_tarski(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_18,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2531,c_1695,c_1022,c_1020,c_701,c_664,c_599,c_575,c_526,c_422,c_420,c_357,c_353,c_54,c_51,c_30,c_25,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:36:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.52/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.52/0.97  
% 1.52/0.97  ------  iProver source info
% 1.52/0.97  
% 1.52/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.52/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.52/0.97  git: non_committed_changes: false
% 1.52/0.97  git: last_make_outside_of_git: false
% 1.52/0.97  
% 1.52/0.97  ------ 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options
% 1.52/0.97  
% 1.52/0.97  --out_options                           all
% 1.52/0.97  --tptp_safe_out                         true
% 1.52/0.97  --problem_path                          ""
% 1.52/0.97  --include_path                          ""
% 1.52/0.97  --clausifier                            res/vclausify_rel
% 1.52/0.97  --clausifier_options                    --mode clausify
% 1.52/0.97  --stdin                                 false
% 1.52/0.97  --stats_out                             all
% 1.52/0.97  
% 1.52/0.97  ------ General Options
% 1.52/0.97  
% 1.52/0.97  --fof                                   false
% 1.52/0.97  --time_out_real                         305.
% 1.52/0.97  --time_out_virtual                      -1.
% 1.52/0.97  --symbol_type_check                     false
% 1.52/0.97  --clausify_out                          false
% 1.52/0.97  --sig_cnt_out                           false
% 1.52/0.97  --trig_cnt_out                          false
% 1.52/0.97  --trig_cnt_out_tolerance                1.
% 1.52/0.97  --trig_cnt_out_sk_spl                   false
% 1.52/0.97  --abstr_cl_out                          false
% 1.52/0.97  
% 1.52/0.97  ------ Global Options
% 1.52/0.97  
% 1.52/0.97  --schedule                              default
% 1.52/0.97  --add_important_lit                     false
% 1.52/0.97  --prop_solver_per_cl                    1000
% 1.52/0.97  --min_unsat_core                        false
% 1.52/0.97  --soft_assumptions                      false
% 1.52/0.97  --soft_lemma_size                       3
% 1.52/0.97  --prop_impl_unit_size                   0
% 1.52/0.97  --prop_impl_unit                        []
% 1.52/0.97  --share_sel_clauses                     true
% 1.52/0.97  --reset_solvers                         false
% 1.52/0.97  --bc_imp_inh                            [conj_cone]
% 1.52/0.97  --conj_cone_tolerance                   3.
% 1.52/0.97  --extra_neg_conj                        none
% 1.52/0.97  --large_theory_mode                     true
% 1.52/0.97  --prolific_symb_bound                   200
% 1.52/0.97  --lt_threshold                          2000
% 1.52/0.97  --clause_weak_htbl                      true
% 1.52/0.97  --gc_record_bc_elim                     false
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing Options
% 1.52/0.97  
% 1.52/0.97  --preprocessing_flag                    true
% 1.52/0.97  --time_out_prep_mult                    0.1
% 1.52/0.97  --splitting_mode                        input
% 1.52/0.97  --splitting_grd                         true
% 1.52/0.97  --splitting_cvd                         false
% 1.52/0.97  --splitting_cvd_svl                     false
% 1.52/0.97  --splitting_nvd                         32
% 1.52/0.97  --sub_typing                            true
% 1.52/0.97  --prep_gs_sim                           true
% 1.52/0.97  --prep_unflatten                        true
% 1.52/0.97  --prep_res_sim                          true
% 1.52/0.97  --prep_upred                            true
% 1.52/0.97  --prep_sem_filter                       exhaustive
% 1.52/0.97  --prep_sem_filter_out                   false
% 1.52/0.97  --pred_elim                             true
% 1.52/0.97  --res_sim_input                         true
% 1.52/0.97  --eq_ax_congr_red                       true
% 1.52/0.97  --pure_diseq_elim                       true
% 1.52/0.97  --brand_transform                       false
% 1.52/0.97  --non_eq_to_eq                          false
% 1.52/0.97  --prep_def_merge                        true
% 1.52/0.97  --prep_def_merge_prop_impl              false
% 1.52/0.97  --prep_def_merge_mbd                    true
% 1.52/0.97  --prep_def_merge_tr_red                 false
% 1.52/0.97  --prep_def_merge_tr_cl                  false
% 1.52/0.97  --smt_preprocessing                     true
% 1.52/0.97  --smt_ac_axioms                         fast
% 1.52/0.97  --preprocessed_out                      false
% 1.52/0.97  --preprocessed_stats                    false
% 1.52/0.97  
% 1.52/0.97  ------ Abstraction refinement Options
% 1.52/0.97  
% 1.52/0.97  --abstr_ref                             []
% 1.52/0.97  --abstr_ref_prep                        false
% 1.52/0.97  --abstr_ref_until_sat                   false
% 1.52/0.97  --abstr_ref_sig_restrict                funpre
% 1.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.97  --abstr_ref_under                       []
% 1.52/0.97  
% 1.52/0.97  ------ SAT Options
% 1.52/0.97  
% 1.52/0.97  --sat_mode                              false
% 1.52/0.97  --sat_fm_restart_options                ""
% 1.52/0.97  --sat_gr_def                            false
% 1.52/0.97  --sat_epr_types                         true
% 1.52/0.97  --sat_non_cyclic_types                  false
% 1.52/0.97  --sat_finite_models                     false
% 1.52/0.97  --sat_fm_lemmas                         false
% 1.52/0.97  --sat_fm_prep                           false
% 1.52/0.97  --sat_fm_uc_incr                        true
% 1.52/0.97  --sat_out_model                         small
% 1.52/0.97  --sat_out_clauses                       false
% 1.52/0.97  
% 1.52/0.97  ------ QBF Options
% 1.52/0.97  
% 1.52/0.97  --qbf_mode                              false
% 1.52/0.97  --qbf_elim_univ                         false
% 1.52/0.97  --qbf_dom_inst                          none
% 1.52/0.97  --qbf_dom_pre_inst                      false
% 1.52/0.97  --qbf_sk_in                             false
% 1.52/0.97  --qbf_pred_elim                         true
% 1.52/0.97  --qbf_split                             512
% 1.52/0.97  
% 1.52/0.97  ------ BMC1 Options
% 1.52/0.97  
% 1.52/0.97  --bmc1_incremental                      false
% 1.52/0.97  --bmc1_axioms                           reachable_all
% 1.52/0.97  --bmc1_min_bound                        0
% 1.52/0.97  --bmc1_max_bound                        -1
% 1.52/0.97  --bmc1_max_bound_default                -1
% 1.52/0.97  --bmc1_symbol_reachability              true
% 1.52/0.97  --bmc1_property_lemmas                  false
% 1.52/0.97  --bmc1_k_induction                      false
% 1.52/0.97  --bmc1_non_equiv_states                 false
% 1.52/0.97  --bmc1_deadlock                         false
% 1.52/0.97  --bmc1_ucm                              false
% 1.52/0.97  --bmc1_add_unsat_core                   none
% 1.52/0.97  --bmc1_unsat_core_children              false
% 1.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.97  --bmc1_out_stat                         full
% 1.52/0.97  --bmc1_ground_init                      false
% 1.52/0.97  --bmc1_pre_inst_next_state              false
% 1.52/0.97  --bmc1_pre_inst_state                   false
% 1.52/0.97  --bmc1_pre_inst_reach_state             false
% 1.52/0.97  --bmc1_out_unsat_core                   false
% 1.52/0.97  --bmc1_aig_witness_out                  false
% 1.52/0.97  --bmc1_verbose                          false
% 1.52/0.97  --bmc1_dump_clauses_tptp                false
% 1.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.97  --bmc1_dump_file                        -
% 1.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.97  --bmc1_ucm_extend_mode                  1
% 1.52/0.97  --bmc1_ucm_init_mode                    2
% 1.52/0.97  --bmc1_ucm_cone_mode                    none
% 1.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.97  --bmc1_ucm_relax_model                  4
% 1.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.97  --bmc1_ucm_layered_model                none
% 1.52/0.97  --bmc1_ucm_max_lemma_size               10
% 1.52/0.97  
% 1.52/0.97  ------ AIG Options
% 1.52/0.97  
% 1.52/0.97  --aig_mode                              false
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation Options
% 1.52/0.97  
% 1.52/0.97  --instantiation_flag                    true
% 1.52/0.97  --inst_sos_flag                         false
% 1.52/0.97  --inst_sos_phase                        true
% 1.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel_side                     num_symb
% 1.52/0.97  --inst_solver_per_active                1400
% 1.52/0.97  --inst_solver_calls_frac                1.
% 1.52/0.97  --inst_passive_queue_type               priority_queues
% 1.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.97  --inst_passive_queues_freq              [25;2]
% 1.52/0.97  --inst_dismatching                      true
% 1.52/0.97  --inst_eager_unprocessed_to_passive     true
% 1.52/0.97  --inst_prop_sim_given                   true
% 1.52/0.97  --inst_prop_sim_new                     false
% 1.52/0.97  --inst_subs_new                         false
% 1.52/0.97  --inst_eq_res_simp                      false
% 1.52/0.97  --inst_subs_given                       false
% 1.52/0.97  --inst_orphan_elimination               true
% 1.52/0.97  --inst_learning_loop_flag               true
% 1.52/0.97  --inst_learning_start                   3000
% 1.52/0.97  --inst_learning_factor                  2
% 1.52/0.97  --inst_start_prop_sim_after_learn       3
% 1.52/0.97  --inst_sel_renew                        solver
% 1.52/0.97  --inst_lit_activity_flag                true
% 1.52/0.97  --inst_restr_to_given                   false
% 1.52/0.97  --inst_activity_threshold               500
% 1.52/0.97  --inst_out_proof                        true
% 1.52/0.97  
% 1.52/0.97  ------ Resolution Options
% 1.52/0.97  
% 1.52/0.97  --resolution_flag                       true
% 1.52/0.97  --res_lit_sel                           adaptive
% 1.52/0.97  --res_lit_sel_side                      none
% 1.52/0.97  --res_ordering                          kbo
% 1.52/0.97  --res_to_prop_solver                    active
% 1.52/0.97  --res_prop_simpl_new                    false
% 1.52/0.97  --res_prop_simpl_given                  true
% 1.52/0.97  --res_passive_queue_type                priority_queues
% 1.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.97  --res_passive_queues_freq               [15;5]
% 1.52/0.97  --res_forward_subs                      full
% 1.52/0.97  --res_backward_subs                     full
% 1.52/0.97  --res_forward_subs_resolution           true
% 1.52/0.97  --res_backward_subs_resolution          true
% 1.52/0.97  --res_orphan_elimination                true
% 1.52/0.97  --res_time_limit                        2.
% 1.52/0.97  --res_out_proof                         true
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Options
% 1.52/0.97  
% 1.52/0.97  --superposition_flag                    true
% 1.52/0.97  --sup_passive_queue_type                priority_queues
% 1.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.97  --demod_completeness_check              fast
% 1.52/0.97  --demod_use_ground                      true
% 1.52/0.97  --sup_to_prop_solver                    passive
% 1.52/0.97  --sup_prop_simpl_new                    true
% 1.52/0.97  --sup_prop_simpl_given                  true
% 1.52/0.97  --sup_fun_splitting                     false
% 1.52/0.97  --sup_smt_interval                      50000
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Simplification Setup
% 1.52/0.97  
% 1.52/0.97  --sup_indices_passive                   []
% 1.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_full_bw                           [BwDemod]
% 1.52/0.97  --sup_immed_triv                        [TrivRules]
% 1.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_immed_bw_main                     []
% 1.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  
% 1.52/0.97  ------ Combination Options
% 1.52/0.97  
% 1.52/0.97  --comb_res_mult                         3
% 1.52/0.97  --comb_sup_mult                         2
% 1.52/0.97  --comb_inst_mult                        10
% 1.52/0.97  
% 1.52/0.97  ------ Debug Options
% 1.52/0.97  
% 1.52/0.97  --dbg_backtrace                         false
% 1.52/0.97  --dbg_dump_prop_clauses                 false
% 1.52/0.97  --dbg_dump_prop_clauses_file            -
% 1.52/0.97  --dbg_out_stat                          false
% 1.52/0.97  ------ Parsing...
% 1.52/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.52/0.97  ------ Proving...
% 1.52/0.97  ------ Problem Properties 
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  clauses                                 18
% 1.52/0.97  conjectures                             2
% 1.52/0.97  EPR                                     8
% 1.52/0.97  Horn                                    14
% 1.52/0.97  unary                                   3
% 1.52/0.97  binary                                  8
% 1.52/0.97  lits                                    45
% 1.52/0.97  lits eq                                 0
% 1.52/0.97  fd_pure                                 0
% 1.52/0.97  fd_pseudo                               0
% 1.52/0.97  fd_cond                                 0
% 1.52/0.97  fd_pseudo_cond                          0
% 1.52/0.97  AC symbols                              0
% 1.52/0.97  
% 1.52/0.97  ------ Schedule dynamic 5 is on 
% 1.52/0.97  
% 1.52/0.97  ------ no equalities: superposition off 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  ------ 
% 1.52/0.97  Current options:
% 1.52/0.97  ------ 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options
% 1.52/0.97  
% 1.52/0.97  --out_options                           all
% 1.52/0.97  --tptp_safe_out                         true
% 1.52/0.97  --problem_path                          ""
% 1.52/0.97  --include_path                          ""
% 1.52/0.97  --clausifier                            res/vclausify_rel
% 1.52/0.97  --clausifier_options                    --mode clausify
% 1.52/0.97  --stdin                                 false
% 1.52/0.97  --stats_out                             all
% 1.52/0.97  
% 1.52/0.97  ------ General Options
% 1.52/0.97  
% 1.52/0.97  --fof                                   false
% 1.52/0.97  --time_out_real                         305.
% 1.52/0.97  --time_out_virtual                      -1.
% 1.52/0.97  --symbol_type_check                     false
% 1.52/0.97  --clausify_out                          false
% 1.52/0.97  --sig_cnt_out                           false
% 1.52/0.97  --trig_cnt_out                          false
% 1.52/0.97  --trig_cnt_out_tolerance                1.
% 1.52/0.97  --trig_cnt_out_sk_spl                   false
% 1.52/0.97  --abstr_cl_out                          false
% 1.52/0.97  
% 1.52/0.97  ------ Global Options
% 1.52/0.97  
% 1.52/0.97  --schedule                              default
% 1.52/0.97  --add_important_lit                     false
% 1.52/0.97  --prop_solver_per_cl                    1000
% 1.52/0.97  --min_unsat_core                        false
% 1.52/0.97  --soft_assumptions                      false
% 1.52/0.97  --soft_lemma_size                       3
% 1.52/0.97  --prop_impl_unit_size                   0
% 1.52/0.97  --prop_impl_unit                        []
% 1.52/0.97  --share_sel_clauses                     true
% 1.52/0.97  --reset_solvers                         false
% 1.52/0.97  --bc_imp_inh                            [conj_cone]
% 1.52/0.97  --conj_cone_tolerance                   3.
% 1.52/0.97  --extra_neg_conj                        none
% 1.52/0.97  --large_theory_mode                     true
% 1.52/0.97  --prolific_symb_bound                   200
% 1.52/0.97  --lt_threshold                          2000
% 1.52/0.97  --clause_weak_htbl                      true
% 1.52/0.97  --gc_record_bc_elim                     false
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing Options
% 1.52/0.97  
% 1.52/0.97  --preprocessing_flag                    true
% 1.52/0.97  --time_out_prep_mult                    0.1
% 1.52/0.97  --splitting_mode                        input
% 1.52/0.97  --splitting_grd                         true
% 1.52/0.97  --splitting_cvd                         false
% 1.52/0.97  --splitting_cvd_svl                     false
% 1.52/0.97  --splitting_nvd                         32
% 1.52/0.97  --sub_typing                            true
% 1.52/0.97  --prep_gs_sim                           true
% 1.52/0.97  --prep_unflatten                        true
% 1.52/0.97  --prep_res_sim                          true
% 1.52/0.97  --prep_upred                            true
% 1.52/0.97  --prep_sem_filter                       exhaustive
% 1.52/0.97  --prep_sem_filter_out                   false
% 1.52/0.97  --pred_elim                             true
% 1.52/0.97  --res_sim_input                         true
% 1.52/0.97  --eq_ax_congr_red                       true
% 1.52/0.97  --pure_diseq_elim                       true
% 1.52/0.97  --brand_transform                       false
% 1.52/0.97  --non_eq_to_eq                          false
% 1.52/0.97  --prep_def_merge                        true
% 1.52/0.97  --prep_def_merge_prop_impl              false
% 1.52/0.97  --prep_def_merge_mbd                    true
% 1.52/0.97  --prep_def_merge_tr_red                 false
% 1.52/0.97  --prep_def_merge_tr_cl                  false
% 1.52/0.97  --smt_preprocessing                     true
% 1.52/0.97  --smt_ac_axioms                         fast
% 1.52/0.97  --preprocessed_out                      false
% 1.52/0.97  --preprocessed_stats                    false
% 1.52/0.97  
% 1.52/0.97  ------ Abstraction refinement Options
% 1.52/0.97  
% 1.52/0.97  --abstr_ref                             []
% 1.52/0.97  --abstr_ref_prep                        false
% 1.52/0.97  --abstr_ref_until_sat                   false
% 1.52/0.97  --abstr_ref_sig_restrict                funpre
% 1.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.97  --abstr_ref_under                       []
% 1.52/0.97  
% 1.52/0.97  ------ SAT Options
% 1.52/0.97  
% 1.52/0.97  --sat_mode                              false
% 1.52/0.97  --sat_fm_restart_options                ""
% 1.52/0.97  --sat_gr_def                            false
% 1.52/0.97  --sat_epr_types                         true
% 1.52/0.97  --sat_non_cyclic_types                  false
% 1.52/0.97  --sat_finite_models                     false
% 1.52/0.97  --sat_fm_lemmas                         false
% 1.52/0.97  --sat_fm_prep                           false
% 1.52/0.97  --sat_fm_uc_incr                        true
% 1.52/0.97  --sat_out_model                         small
% 1.52/0.97  --sat_out_clauses                       false
% 1.52/0.97  
% 1.52/0.97  ------ QBF Options
% 1.52/0.97  
% 1.52/0.97  --qbf_mode                              false
% 1.52/0.97  --qbf_elim_univ                         false
% 1.52/0.97  --qbf_dom_inst                          none
% 1.52/0.97  --qbf_dom_pre_inst                      false
% 1.52/0.97  --qbf_sk_in                             false
% 1.52/0.97  --qbf_pred_elim                         true
% 1.52/0.97  --qbf_split                             512
% 1.52/0.97  
% 1.52/0.97  ------ BMC1 Options
% 1.52/0.97  
% 1.52/0.97  --bmc1_incremental                      false
% 1.52/0.97  --bmc1_axioms                           reachable_all
% 1.52/0.97  --bmc1_min_bound                        0
% 1.52/0.97  --bmc1_max_bound                        -1
% 1.52/0.97  --bmc1_max_bound_default                -1
% 1.52/0.97  --bmc1_symbol_reachability              true
% 1.52/0.97  --bmc1_property_lemmas                  false
% 1.52/0.97  --bmc1_k_induction                      false
% 1.52/0.97  --bmc1_non_equiv_states                 false
% 1.52/0.97  --bmc1_deadlock                         false
% 1.52/0.97  --bmc1_ucm                              false
% 1.52/0.97  --bmc1_add_unsat_core                   none
% 1.52/0.97  --bmc1_unsat_core_children              false
% 1.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.97  --bmc1_out_stat                         full
% 1.52/0.97  --bmc1_ground_init                      false
% 1.52/0.97  --bmc1_pre_inst_next_state              false
% 1.52/0.97  --bmc1_pre_inst_state                   false
% 1.52/0.97  --bmc1_pre_inst_reach_state             false
% 1.52/0.97  --bmc1_out_unsat_core                   false
% 1.52/0.97  --bmc1_aig_witness_out                  false
% 1.52/0.97  --bmc1_verbose                          false
% 1.52/0.97  --bmc1_dump_clauses_tptp                false
% 1.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.97  --bmc1_dump_file                        -
% 1.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.97  --bmc1_ucm_extend_mode                  1
% 1.52/0.97  --bmc1_ucm_init_mode                    2
% 1.52/0.97  --bmc1_ucm_cone_mode                    none
% 1.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.97  --bmc1_ucm_relax_model                  4
% 1.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.97  --bmc1_ucm_layered_model                none
% 1.52/0.97  --bmc1_ucm_max_lemma_size               10
% 1.52/0.97  
% 1.52/0.97  ------ AIG Options
% 1.52/0.97  
% 1.52/0.97  --aig_mode                              false
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation Options
% 1.52/0.97  
% 1.52/0.97  --instantiation_flag                    true
% 1.52/0.97  --inst_sos_flag                         false
% 1.52/0.97  --inst_sos_phase                        true
% 1.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel_side                     none
% 1.52/0.97  --inst_solver_per_active                1400
% 1.52/0.97  --inst_solver_calls_frac                1.
% 1.52/0.97  --inst_passive_queue_type               priority_queues
% 1.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.97  --inst_passive_queues_freq              [25;2]
% 1.52/0.97  --inst_dismatching                      true
% 1.52/0.97  --inst_eager_unprocessed_to_passive     true
% 1.52/0.97  --inst_prop_sim_given                   true
% 1.52/0.97  --inst_prop_sim_new                     false
% 1.52/0.97  --inst_subs_new                         false
% 1.52/0.97  --inst_eq_res_simp                      false
% 1.52/0.97  --inst_subs_given                       false
% 1.52/0.97  --inst_orphan_elimination               true
% 1.52/0.97  --inst_learning_loop_flag               true
% 1.52/0.97  --inst_learning_start                   3000
% 1.52/0.97  --inst_learning_factor                  2
% 1.52/0.97  --inst_start_prop_sim_after_learn       3
% 1.52/0.97  --inst_sel_renew                        solver
% 1.52/0.97  --inst_lit_activity_flag                true
% 1.52/0.97  --inst_restr_to_given                   false
% 1.52/0.97  --inst_activity_threshold               500
% 1.52/0.97  --inst_out_proof                        true
% 1.52/0.97  
% 1.52/0.97  ------ Resolution Options
% 1.52/0.97  
% 1.52/0.97  --resolution_flag                       false
% 1.52/0.97  --res_lit_sel                           adaptive
% 1.52/0.97  --res_lit_sel_side                      none
% 1.52/0.97  --res_ordering                          kbo
% 1.52/0.97  --res_to_prop_solver                    active
% 1.52/0.97  --res_prop_simpl_new                    false
% 1.52/0.97  --res_prop_simpl_given                  true
% 1.52/0.97  --res_passive_queue_type                priority_queues
% 1.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.97  --res_passive_queues_freq               [15;5]
% 1.52/0.97  --res_forward_subs                      full
% 1.52/0.97  --res_backward_subs                     full
% 1.52/0.97  --res_forward_subs_resolution           true
% 1.52/0.97  --res_backward_subs_resolution          true
% 1.52/0.97  --res_orphan_elimination                true
% 1.52/0.97  --res_time_limit                        2.
% 1.52/0.97  --res_out_proof                         true
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Options
% 1.52/0.97  
% 1.52/0.97  --superposition_flag                    false
% 1.52/0.97  --sup_passive_queue_type                priority_queues
% 1.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.97  --demod_completeness_check              fast
% 1.52/0.97  --demod_use_ground                      true
% 1.52/0.97  --sup_to_prop_solver                    passive
% 1.52/0.97  --sup_prop_simpl_new                    true
% 1.52/0.97  --sup_prop_simpl_given                  true
% 1.52/0.97  --sup_fun_splitting                     false
% 1.52/0.97  --sup_smt_interval                      50000
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Simplification Setup
% 1.52/0.97  
% 1.52/0.97  --sup_indices_passive                   []
% 1.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_full_bw                           [BwDemod]
% 1.52/0.97  --sup_immed_triv                        [TrivRules]
% 1.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_immed_bw_main                     []
% 1.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  
% 1.52/0.97  ------ Combination Options
% 1.52/0.97  
% 1.52/0.97  --comb_res_mult                         3
% 1.52/0.97  --comb_sup_mult                         2
% 1.52/0.97  --comb_inst_mult                        10
% 1.52/0.97  
% 1.52/0.97  ------ Debug Options
% 1.52/0.97  
% 1.52/0.97  --dbg_backtrace                         false
% 1.52/0.97  --dbg_dump_prop_clauses                 false
% 1.52/0.97  --dbg_dump_prop_clauses_file            -
% 1.52/0.97  --dbg_out_stat                          false
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  ------ Proving...
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  % SZS status Theorem for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  fof(f4,axiom,(
% 1.52/0.97    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f19,plain,(
% 1.52/0.97    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f4])).
% 1.52/0.97  
% 1.52/0.97  fof(f20,plain,(
% 1.52/0.97    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.52/0.97    inference(flattening,[],[f19])).
% 1.52/0.97  
% 1.52/0.97  fof(f48,plain,(
% 1.52/0.97    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f20])).
% 1.52/0.97  
% 1.52/0.97  fof(f9,axiom,(
% 1.52/0.97    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f26,plain,(
% 1.52/0.97    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 1.52/0.97    inference(ennf_transformation,[],[f9])).
% 1.52/0.97  
% 1.52/0.97  fof(f27,plain,(
% 1.52/0.97    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 1.52/0.97    inference(flattening,[],[f26])).
% 1.52/0.97  
% 1.52/0.97  fof(f55,plain,(
% 1.52/0.97    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f27])).
% 1.52/0.97  
% 1.52/0.97  fof(f1,axiom,(
% 1.52/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f15,plain,(
% 1.52/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f1])).
% 1.52/0.97  
% 1.52/0.97  fof(f31,plain,(
% 1.52/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.97    inference(nnf_transformation,[],[f15])).
% 1.52/0.97  
% 1.52/0.97  fof(f32,plain,(
% 1.52/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.97    inference(rectify,[],[f31])).
% 1.52/0.97  
% 1.52/0.97  fof(f33,plain,(
% 1.52/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f34,plain,(
% 1.52/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 1.52/0.97  
% 1.52/0.97  fof(f43,plain,(
% 1.52/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f34])).
% 1.52/0.97  
% 1.52/0.97  fof(f44,plain,(
% 1.52/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f34])).
% 1.52/0.97  
% 1.52/0.97  fof(f3,axiom,(
% 1.52/0.97    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f17,plain,(
% 1.52/0.97    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 1.52/0.97    inference(ennf_transformation,[],[f3])).
% 1.52/0.97  
% 1.52/0.97  fof(f18,plain,(
% 1.52/0.97    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 1.52/0.97    inference(flattening,[],[f17])).
% 1.52/0.97  
% 1.52/0.97  fof(f47,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f18])).
% 1.52/0.97  
% 1.52/0.97  fof(f6,axiom,(
% 1.52/0.97    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f22,plain,(
% 1.52/0.97    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f6])).
% 1.52/0.97  
% 1.52/0.97  fof(f23,plain,(
% 1.52/0.97    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.52/0.97    inference(flattening,[],[f22])).
% 1.52/0.97  
% 1.52/0.97  fof(f39,plain,(
% 1.52/0.97    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.52/0.97    inference(nnf_transformation,[],[f23])).
% 1.52/0.97  
% 1.52/0.97  fof(f51,plain,(
% 1.52/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f39])).
% 1.52/0.97  
% 1.52/0.97  fof(f11,axiom,(
% 1.52/0.97    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f29,plain,(
% 1.52/0.97    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.52/0.97    inference(ennf_transformation,[],[f11])).
% 1.52/0.97  
% 1.52/0.97  fof(f57,plain,(
% 1.52/0.97    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f29])).
% 1.52/0.97  
% 1.52/0.97  fof(f42,plain,(
% 1.52/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f34])).
% 1.52/0.97  
% 1.52/0.97  fof(f5,axiom,(
% 1.52/0.97    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f14,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)) => v1_ordinal1(X0))),
% 1.52/0.97    inference(unused_predicate_definition_removal,[],[f5])).
% 1.52/0.97  
% 1.52/0.97  fof(f21,plain,(
% 1.52/0.97    ! [X0] : (v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f14])).
% 1.52/0.97  
% 1.52/0.97  fof(f37,plain,(
% 1.52/0.97    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f38,plain,(
% 1.52/0.97    ! [X0] : (v1_ordinal1(X0) | (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f37])).
% 1.52/0.97  
% 1.52/0.97  fof(f49,plain,(
% 1.52/0.97    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK2(X0),X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f38])).
% 1.52/0.97  
% 1.52/0.97  fof(f50,plain,(
% 1.52/0.97    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK2(X0),X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f38])).
% 1.52/0.97  
% 1.52/0.97  fof(f8,axiom,(
% 1.52/0.97    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f24,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r1_tarski(X0,X1))) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.52/0.97    inference(ennf_transformation,[],[f8])).
% 1.52/0.97  
% 1.52/0.97  fof(f25,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.52/0.97    inference(flattening,[],[f24])).
% 1.52/0.97  
% 1.52/0.97  fof(f54,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f25])).
% 1.52/0.97  
% 1.52/0.97  fof(f2,axiom,(
% 1.52/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f16,plain,(
% 1.52/0.97    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f2])).
% 1.52/0.97  
% 1.52/0.97  fof(f35,plain,(
% 1.52/0.97    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f36,plain,(
% 1.52/0.97    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f35])).
% 1.52/0.97  
% 1.52/0.97  fof(f46,plain,(
% 1.52/0.97    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK1(X0,X1),X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f36])).
% 1.52/0.97  
% 1.52/0.97  fof(f45,plain,(
% 1.52/0.97    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f36])).
% 1.52/0.97  
% 1.52/0.97  fof(f7,axiom,(
% 1.52/0.97    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f53,plain,(
% 1.52/0.97    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.52/0.97    inference(cnf_transformation,[],[f7])).
% 1.52/0.97  
% 1.52/0.97  fof(f10,axiom,(
% 1.52/0.97    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f28,plain,(
% 1.52/0.97    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.52/0.97    inference(ennf_transformation,[],[f10])).
% 1.52/0.97  
% 1.52/0.97  fof(f56,plain,(
% 1.52/0.97    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f28])).
% 1.52/0.97  
% 1.52/0.97  fof(f12,conjecture,(
% 1.52/0.97    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f13,negated_conjecture,(
% 1.52/0.97    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.52/0.97    inference(negated_conjecture,[],[f12])).
% 1.52/0.97  
% 1.52/0.97  fof(f30,plain,(
% 1.52/0.97    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 1.52/0.97    inference(ennf_transformation,[],[f13])).
% 1.52/0.97  
% 1.52/0.97  fof(f40,plain,(
% 1.52/0.97    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0)) => (~v3_ordinal1(k3_tarski(sK3)) & v3_ordinal1(sK3))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f41,plain,(
% 1.52/0.97    ~v3_ordinal1(k3_tarski(sK3)) & v3_ordinal1(sK3)),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f40])).
% 1.52/0.97  
% 1.52/0.97  fof(f59,plain,(
% 1.52/0.97    ~v3_ordinal1(k3_tarski(sK3))),
% 1.52/0.97    inference(cnf_transformation,[],[f41])).
% 1.52/0.97  
% 1.52/0.97  fof(f58,plain,(
% 1.52/0.97    v3_ordinal1(sK3)),
% 1.52/0.97    inference(cnf_transformation,[],[f41])).
% 1.52/0.97  
% 1.52/0.97  cnf(c_6,plain,
% 1.52/0.97      ( r1_ordinal1(X0,X1)
% 1.52/0.97      | r1_ordinal1(X1,X0)
% 1.52/0.97      | ~ v3_ordinal1(X1)
% 1.52/0.97      | ~ v3_ordinal1(X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2528,plain,
% 1.52/0.97      ( r1_ordinal1(X0,sK1(X1,X0))
% 1.52/0.97      | r1_ordinal1(sK1(X1,X0),X0)
% 1.52/0.97      | ~ v3_ordinal1(X0)
% 1.52/0.97      | ~ v3_ordinal1(sK1(X1,X0)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2529,plain,
% 1.52/0.97      ( r1_ordinal1(X0,sK1(X1,X0)) = iProver_top
% 1.52/0.97      | r1_ordinal1(sK1(X1,X0),X0) = iProver_top
% 1.52/0.97      | v3_ordinal1(X0) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(X1,X0)) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_2528]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2531,plain,
% 1.52/0.97      ( r1_ordinal1(sK1(sK3,sK3),sK3) = iProver_top
% 1.52/0.97      | r1_ordinal1(sK3,sK1(sK3,sK3)) = iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(sK3,sK3)) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK3) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_2529]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_13,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f55]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1692,plain,
% 1.52/0.97      ( ~ r2_hidden(sK1(X0,X1),X2)
% 1.52/0.97      | ~ v3_ordinal1(X2)
% 1.52/0.97      | v3_ordinal1(sK1(X0,X1)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1693,plain,
% 1.52/0.97      ( r2_hidden(sK1(X0,X1),X2) != iProver_top
% 1.52/0.97      | v3_ordinal1(X2) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_1692]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1695,plain,
% 1.52/0.97      ( r2_hidden(sK1(sK3,sK3),sK3) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(sK3,sK3)) = iProver_top
% 1.52/0.97      | v3_ordinal1(sK3) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_1693]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1,plain,
% 1.52/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.52/0.97      inference(cnf_transformation,[],[f43]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_528,plain,
% 1.52/0.97      ( r2_hidden(sK0(k3_tarski(sK3),X0),k3_tarski(sK3))
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),X0) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1019,plain,
% 1.52/0.97      ( r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3))
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_528]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1022,plain,
% 1.52/0.97      ( r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_0,plain,
% 1.52/0.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.52/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_529,plain,
% 1.52/0.97      ( ~ r2_hidden(sK0(k3_tarski(sK3),X0),X0)
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),X0) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1018,plain,
% 1.52/0.97      ( ~ r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3))
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_529]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1020,plain,
% 1.52/0.97      ( r2_hidden(sK0(k3_tarski(sK3),k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_5,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1)
% 1.52/0.97      | r1_tarski(X0,X2)
% 1.52/0.97      | ~ r1_tarski(k3_tarski(X1),X2) ),
% 1.52/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_698,plain,
% 1.52/0.97      ( ~ r2_hidden(sK2(k3_tarski(sK3)),X0)
% 1.52/0.97      | r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3))
% 1.52/0.97      | ~ r1_tarski(k3_tarski(X0),k3_tarski(sK3)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_699,plain,
% 1.52/0.97      ( r2_hidden(sK2(k3_tarski(sK3)),X0) != iProver_top
% 1.52/0.97      | r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(X0),k3_tarski(sK3)) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_701,plain,
% 1.52/0.97      ( r2_hidden(sK2(k3_tarski(sK3)),sK3) != iProver_top
% 1.52/0.97      | r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),k3_tarski(sK3)) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_699]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_10,plain,
% 1.52/0.97      ( ~ r1_ordinal1(X0,X1)
% 1.52/0.97      | r1_tarski(X0,X1)
% 1.52/0.97      | ~ v3_ordinal1(X1)
% 1.52/0.97      | ~ v3_ordinal1(X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_661,plain,
% 1.52/0.97      ( ~ r1_ordinal1(X0,sK1(X0,X1))
% 1.52/0.97      | r1_tarski(X0,sK1(X0,X1))
% 1.52/0.97      | ~ v3_ordinal1(X0)
% 1.52/0.97      | ~ v3_ordinal1(sK1(X0,X1)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_662,plain,
% 1.52/0.97      ( r1_ordinal1(X0,sK1(X0,X1)) != iProver_top
% 1.52/0.97      | r1_tarski(X0,sK1(X0,X1)) = iProver_top
% 1.52/0.97      | v3_ordinal1(X0) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(X0,X1)) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_664,plain,
% 1.52/0.97      ( r1_ordinal1(sK3,sK1(sK3,sK3)) != iProver_top
% 1.52/0.97      | r1_tarski(sK3,sK1(sK3,sK3)) = iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(sK3,sK3)) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK3) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_662]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_15,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f57]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_591,plain,
% 1.52/0.97      ( ~ r2_hidden(sK1(X0,X1),X0) | ~ r1_tarski(X0,sK1(X0,X1)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_15]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_597,plain,
% 1.52/0.97      ( r2_hidden(sK1(X0,X1),X0) != iProver_top
% 1.52/0.97      | r1_tarski(X0,sK1(X0,X1)) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_599,plain,
% 1.52/0.97      ( r2_hidden(sK1(sK3,sK3),sK3) != iProver_top
% 1.52/0.97      | r1_tarski(sK3,sK1(sK3,sK3)) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_597]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_572,plain,
% 1.52/0.97      ( ~ r1_ordinal1(sK1(X0,X1),X1)
% 1.52/0.97      | r1_tarski(sK1(X0,X1),X1)
% 1.52/0.97      | ~ v3_ordinal1(X1)
% 1.52/0.97      | ~ v3_ordinal1(sK1(X0,X1)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_573,plain,
% 1.52/0.97      ( r1_ordinal1(sK1(X0,X1),X1) != iProver_top
% 1.52/0.97      | r1_tarski(sK1(X0,X1),X1) = iProver_top
% 1.52/0.97      | v3_ordinal1(X1) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(X0,X1)) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_575,plain,
% 1.52/0.97      ( r1_ordinal1(sK1(sK3,sK3),sK3) != iProver_top
% 1.52/0.97      | r1_tarski(sK1(sK3,sK3),sK3) = iProver_top
% 1.52/0.97      | v3_ordinal1(sK1(sK3,sK3)) != iProver_top
% 1.52/0.97      | v3_ordinal1(sK3) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_573]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.52/0.97      inference(cnf_transformation,[],[f42]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_519,plain,
% 1.52/0.97      ( r2_hidden(sK2(k3_tarski(sK3)),X0)
% 1.52/0.97      | ~ r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3))
% 1.52/0.97      | ~ r1_tarski(k3_tarski(sK3),X0) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_524,plain,
% 1.52/0.97      ( r2_hidden(sK2(k3_tarski(sK3)),X0) = iProver_top
% 1.52/0.97      | r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),X0) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_526,plain,
% 1.52/0.97      ( r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
% 1.52/0.97      | r2_hidden(sK2(k3_tarski(sK3)),sK3) = iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),sK3) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_524]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_8,plain,
% 1.52/0.97      ( r2_hidden(sK2(X0),X0) | v1_ordinal1(X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_418,plain,
% 1.52/0.97      ( r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3))
% 1.52/0.97      | v1_ordinal1(k3_tarski(sK3)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_422,plain,
% 1.52/0.97      ( r2_hidden(sK2(k3_tarski(sK3)),k3_tarski(sK3)) = iProver_top
% 1.52/0.97      | v1_ordinal1(k3_tarski(sK3)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_7,plain,
% 1.52/0.97      ( ~ r1_tarski(sK2(X0),X0) | v1_ordinal1(X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_419,plain,
% 1.52/0.97      ( ~ r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3))
% 1.52/0.97      | v1_ordinal1(k3_tarski(sK3)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_420,plain,
% 1.52/0.97      ( r1_tarski(sK2(k3_tarski(sK3)),k3_tarski(sK3)) != iProver_top
% 1.52/0.97      | v1_ordinal1(k3_tarski(sK3)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_318,plain,
% 1.52/0.97      ( ~ r2_hidden(k3_tarski(sK3),X0)
% 1.52/0.97      | ~ v3_ordinal1(X0)
% 1.52/0.97      | v3_ordinal1(k3_tarski(sK3)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_350,plain,
% 1.52/0.97      ( ~ r2_hidden(k3_tarski(sK3),k1_ordinal1(X0))
% 1.52/0.97      | ~ v3_ordinal1(k1_ordinal1(X0))
% 1.52/0.97      | v3_ordinal1(k3_tarski(sK3)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_318]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_355,plain,
% 1.52/0.97      ( r2_hidden(k3_tarski(sK3),k1_ordinal1(X0)) != iProver_top
% 1.52/0.97      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top
% 1.52/0.97      | v3_ordinal1(k3_tarski(sK3)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_357,plain,
% 1.52/0.97      ( r2_hidden(k3_tarski(sK3),k1_ordinal1(sK3)) != iProver_top
% 1.52/0.97      | v3_ordinal1(k1_ordinal1(sK3)) != iProver_top
% 1.52/0.97      | v3_ordinal1(k3_tarski(sK3)) = iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_355]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_12,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1)
% 1.52/0.97      | r2_hidden(X2,X1)
% 1.52/0.97      | ~ r1_tarski(X2,X0)
% 1.52/0.97      | ~ v1_ordinal1(X2)
% 1.52/0.97      | ~ v3_ordinal1(X0)
% 1.52/0.97      | ~ v3_ordinal1(X1) ),
% 1.52/0.97      inference(cnf_transformation,[],[f54]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_104,plain,
% 1.52/0.97      ( ~ v1_ordinal1(X2)
% 1.52/0.97      | ~ r1_tarski(X2,X0)
% 1.52/0.97      | r2_hidden(X2,X1)
% 1.52/0.97      | ~ r2_hidden(X0,X1)
% 1.52/0.97      | ~ v3_ordinal1(X1) ),
% 1.52/0.97      inference(global_propositional_subsumption,
% 1.52/0.97                [status(thm)],
% 1.52/0.97                [c_12,c_13]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_105,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1)
% 1.52/0.97      | r2_hidden(X2,X1)
% 1.52/0.97      | ~ r1_tarski(X2,X0)
% 1.52/0.97      | ~ v1_ordinal1(X2)
% 1.52/0.97      | ~ v3_ordinal1(X1) ),
% 1.52/0.97      inference(renaming,[status(thm)],[c_104]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_323,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,k1_ordinal1(X0))
% 1.52/0.97      | r2_hidden(X1,k1_ordinal1(X0))
% 1.52/0.97      | ~ r1_tarski(X1,X0)
% 1.52/0.97      | ~ v1_ordinal1(X1)
% 1.52/0.97      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_105]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_349,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,k1_ordinal1(X0))
% 1.52/0.97      | r2_hidden(k3_tarski(sK3),k1_ordinal1(X0))
% 1.52/0.97      | ~ r1_tarski(k3_tarski(sK3),X0)
% 1.52/0.97      | ~ v1_ordinal1(k3_tarski(sK3))
% 1.52/0.97      | ~ v3_ordinal1(k1_ordinal1(X0)) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_323]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_351,plain,
% 1.52/0.97      ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
% 1.52/0.97      | r2_hidden(k3_tarski(sK3),k1_ordinal1(X0)) = iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),X0) != iProver_top
% 1.52/0.97      | v1_ordinal1(k3_tarski(sK3)) != iProver_top
% 1.52/0.97      | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_353,plain,
% 1.52/0.97      ( r2_hidden(k3_tarski(sK3),k1_ordinal1(sK3)) = iProver_top
% 1.52/0.97      | r2_hidden(sK3,k1_ordinal1(sK3)) != iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),sK3) != iProver_top
% 1.52/0.97      | v1_ordinal1(k3_tarski(sK3)) != iProver_top
% 1.52/0.97      | v3_ordinal1(k1_ordinal1(sK3)) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_351]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_3,plain,
% 1.52/0.97      ( ~ r1_tarski(sK1(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 1.52/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_52,plain,
% 1.52/0.97      ( r1_tarski(sK1(X0,X1),X1) != iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_54,plain,
% 1.52/0.97      ( r1_tarski(sK1(sK3,sK3),sK3) != iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),sK3) = iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_52]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_4,plain,
% 1.52/0.97      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 1.52/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_49,plain,
% 1.52/0.97      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_51,plain,
% 1.52/0.97      ( r2_hidden(sK1(sK3,sK3),sK3) = iProver_top
% 1.52/0.97      | r1_tarski(k3_tarski(sK3),sK3) = iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_49]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_11,plain,
% 1.52/0.97      ( r2_hidden(X0,k1_ordinal1(X0)) ),
% 1.52/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_28,plain,
% 1.52/0.97      ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_30,plain,
% 1.52/0.97      ( r2_hidden(sK3,k1_ordinal1(sK3)) = iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_28]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_14,plain,
% 1.52/0.97      ( ~ v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0)) ),
% 1.52/0.97      inference(cnf_transformation,[],[f56]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_23,plain,
% 1.52/0.97      ( v3_ordinal1(X0) != iProver_top
% 1.52/0.97      | v3_ordinal1(k1_ordinal1(X0)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_25,plain,
% 1.52/0.97      ( v3_ordinal1(k1_ordinal1(sK3)) = iProver_top
% 1.52/0.97      | v3_ordinal1(sK3) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_23]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_16,negated_conjecture,
% 1.52/0.97      ( ~ v3_ordinal1(k3_tarski(sK3)) ),
% 1.52/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_19,plain,
% 1.52/0.97      ( v3_ordinal1(k3_tarski(sK3)) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_17,negated_conjecture,
% 1.52/0.97      ( v3_ordinal1(sK3) ),
% 1.52/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_18,plain,
% 1.52/0.97      ( v3_ordinal1(sK3) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(contradiction,plain,
% 1.52/0.97      ( $false ),
% 1.52/0.97      inference(minisat,
% 1.52/0.97                [status(thm)],
% 1.52/0.97                [c_2531,c_1695,c_1022,c_1020,c_701,c_664,c_599,c_575,
% 1.52/0.97                 c_526,c_422,c_420,c_357,c_353,c_54,c_51,c_30,c_25,c_19,
% 1.52/0.97                 c_18]) ).
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  ------                               Statistics
% 1.52/0.97  
% 1.52/0.97  ------ General
% 1.52/0.97  
% 1.52/0.97  abstr_ref_over_cycles:                  0
% 1.52/0.97  abstr_ref_under_cycles:                 0
% 1.52/0.97  gc_basic_clause_elim:                   0
% 1.52/0.97  forced_gc_time:                         0
% 1.52/0.97  parsing_time:                           0.009
% 1.52/0.97  unif_index_cands_time:                  0.
% 1.52/0.97  unif_index_add_time:                    0.
% 1.52/0.97  orderings_time:                         0.
% 1.52/0.97  out_proof_time:                         0.008
% 1.52/0.97  total_time:                             0.154
% 1.52/0.97  num_of_symbols:                         42
% 1.52/0.97  num_of_terms:                           6382
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing
% 1.52/0.97  
% 1.52/0.97  num_of_splits:                          0
% 1.52/0.97  num_of_split_atoms:                     0
% 1.52/0.97  num_of_reused_defs:                     0
% 1.52/0.97  num_eq_ax_congr_red:                    0
% 1.52/0.97  num_of_sem_filtered_clauses:            0
% 1.52/0.97  num_of_subtypes:                        1
% 1.52/0.97  monotx_restored_types:                  0
% 1.52/0.97  sat_num_of_epr_types:                   0
% 1.52/0.97  sat_num_of_non_cyclic_types:            0
% 1.52/0.97  sat_guarded_non_collapsed_types:        0
% 1.52/0.97  num_pure_diseq_elim:                    0
% 1.52/0.97  simp_replaced_by:                       0
% 1.52/0.97  res_preprocessed:                       18
% 1.52/0.97  prep_upred:                             0
% 1.52/0.97  prep_unflattend:                        0
% 1.52/0.97  smt_new_axioms:                         0
% 1.52/0.97  pred_elim_cands:                        5
% 1.52/0.97  pred_elim:                              0
% 1.52/0.97  pred_elim_cl:                           0
% 1.52/0.97  pred_elim_cycles:                       1
% 1.52/0.97  merged_defs:                            0
% 1.52/0.97  merged_defs_ncl:                        0
% 1.52/0.97  bin_hyper_res:                          0
% 1.52/0.97  prep_cycles:                            1
% 1.52/0.97  pred_elim_time:                         0.
% 1.52/0.97  splitting_time:                         0.
% 1.52/0.97  sem_filter_time:                        0.
% 1.52/0.97  monotx_time:                            0.
% 1.52/0.97  subtype_inf_time:                       0.
% 1.52/0.97  
% 1.52/0.97  ------ Problem properties
% 1.52/0.97  
% 1.52/0.97  clauses:                                18
% 1.52/0.97  conjectures:                            2
% 1.52/0.97  epr:                                    8
% 1.52/0.97  horn:                                   14
% 1.52/0.97  ground:                                 2
% 1.52/0.97  unary:                                  3
% 1.52/0.97  binary:                                 8
% 1.52/0.97  lits:                                   45
% 1.52/0.97  lits_eq:                                0
% 1.52/0.97  fd_pure:                                0
% 1.52/0.97  fd_pseudo:                              0
% 1.52/0.97  fd_cond:                                0
% 1.52/0.97  fd_pseudo_cond:                         0
% 1.52/0.97  ac_symbols:                             0
% 1.52/0.97  
% 1.52/0.97  ------ Propositional Solver
% 1.52/0.97  
% 1.52/0.97  prop_solver_calls:                      18
% 1.52/0.97  prop_fast_solver_calls:                 106
% 1.52/0.97  smt_solver_calls:                       0
% 1.52/0.97  smt_fast_solver_calls:                  0
% 1.52/0.97  prop_num_of_clauses:                    2180
% 1.52/0.97  prop_preprocess_simplified:             4858
% 1.52/0.97  prop_fo_subsumed:                       1
% 1.52/0.97  prop_solver_time:                       0.
% 1.52/0.97  smt_solver_time:                        0.
% 1.52/0.97  smt_fast_solver_time:                   0.
% 1.52/0.97  prop_fast_solver_time:                  0.
% 1.52/0.97  prop_unsat_core_time:                   0.
% 1.52/0.97  
% 1.52/0.97  ------ QBF
% 1.52/0.97  
% 1.52/0.97  qbf_q_res:                              0
% 1.52/0.97  qbf_num_tautologies:                    0
% 1.52/0.97  qbf_prep_cycles:                        0
% 1.52/0.97  
% 1.52/0.97  ------ BMC1
% 1.52/0.97  
% 1.52/0.97  bmc1_current_bound:                     -1
% 1.52/0.97  bmc1_last_solved_bound:                 -1
% 1.52/0.97  bmc1_unsat_core_size:                   -1
% 1.52/0.97  bmc1_unsat_core_parents_size:           -1
% 1.52/0.97  bmc1_merge_next_fun:                    0
% 1.52/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation
% 1.52/0.97  
% 1.52/0.97  inst_num_of_clauses:                    671
% 1.52/0.97  inst_num_in_passive:                    23
% 1.52/0.97  inst_num_in_active:                     308
% 1.52/0.97  inst_num_in_unprocessed:                340
% 1.52/0.97  inst_num_of_loops:                      383
% 1.52/0.97  inst_num_of_learning_restarts:          0
% 1.52/0.97  inst_num_moves_active_passive:          69
% 1.52/0.97  inst_lit_activity:                      0
% 1.52/0.97  inst_lit_activity_moves:                0
% 1.52/0.97  inst_num_tautologies:                   0
% 1.52/0.97  inst_num_prop_implied:                  0
% 1.52/0.97  inst_num_existing_simplified:           0
% 1.52/0.97  inst_num_eq_res_simplified:             0
% 1.52/0.97  inst_num_child_elim:                    0
% 1.52/0.97  inst_num_of_dismatching_blockings:      464
% 1.52/0.97  inst_num_of_non_proper_insts:           682
% 1.52/0.97  inst_num_of_duplicates:                 0
% 1.52/0.97  inst_inst_num_from_inst_to_res:         0
% 1.52/0.97  inst_dismatching_checking_time:         0.
% 1.52/0.97  
% 1.52/0.97  ------ Resolution
% 1.52/0.97  
% 1.52/0.97  res_num_of_clauses:                     0
% 1.52/0.97  res_num_in_passive:                     0
% 1.52/0.97  res_num_in_active:                      0
% 1.52/0.97  res_num_of_loops:                       19
% 1.52/0.97  res_forward_subset_subsumed:            48
% 1.52/0.97  res_backward_subset_subsumed:           0
% 1.52/0.97  res_forward_subsumed:                   0
% 1.52/0.97  res_backward_subsumed:                  0
% 1.52/0.97  res_forward_subsumption_resolution:     0
% 1.52/0.97  res_backward_subsumption_resolution:    0
% 1.52/0.97  res_clause_to_clause_subsumption:       17
% 1.52/0.97  res_orphan_elimination:                 0
% 1.52/0.97  res_tautology_del:                      22
% 1.52/0.97  res_num_eq_res_simplified:              0
% 1.52/0.97  res_num_sel_changes:                    0
% 1.52/0.97  res_moves_from_active_to_pass:          0
% 1.52/0.97  
% 1.52/0.97  ------ Superposition
% 1.52/0.97  
% 1.52/0.97  sup_time_total:                         0.
% 1.52/0.97  sup_time_generating:                    0.
% 1.52/0.97  sup_time_sim_full:                      0.
% 1.52/0.97  sup_time_sim_immed:                     0.
% 1.52/0.97  
% 1.52/0.97  sup_num_of_clauses:                     0
% 1.52/0.97  sup_num_in_active:                      0
% 1.52/0.97  sup_num_in_passive:                     0
% 1.52/0.97  sup_num_of_loops:                       0
% 1.52/0.97  sup_fw_superposition:                   0
% 1.52/0.97  sup_bw_superposition:                   0
% 1.52/0.97  sup_immediate_simplified:               0
% 1.52/0.97  sup_given_eliminated:                   0
% 1.52/0.97  comparisons_done:                       0
% 1.52/0.97  comparisons_avoided:                    0
% 1.52/0.97  
% 1.52/0.97  ------ Simplifications
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  sim_fw_subset_subsumed:                 0
% 1.52/0.97  sim_bw_subset_subsumed:                 0
% 1.52/0.97  sim_fw_subsumed:                        0
% 1.52/0.97  sim_bw_subsumed:                        0
% 1.52/0.97  sim_fw_subsumption_res:                 0
% 1.52/0.97  sim_bw_subsumption_res:                 0
% 1.52/0.97  sim_tautology_del:                      0
% 1.52/0.97  sim_eq_tautology_del:                   0
% 1.52/0.97  sim_eq_res_simp:                        0
% 1.52/0.97  sim_fw_demodulated:                     0
% 1.52/0.97  sim_bw_demodulated:                     0
% 1.52/0.97  sim_light_normalised:                   0
% 1.52/0.97  sim_joinable_taut:                      0
% 1.52/0.97  sim_joinable_simp:                      0
% 1.52/0.97  sim_ac_normalised:                      0
% 1.52/0.97  sim_smt_subsumption:                    0
% 1.52/0.97  
%------------------------------------------------------------------------------
