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
% DateTime   : Thu Dec  3 11:46:49 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 204 expanded)
%              Number of clauses        :   50 (  86 expanded)
%              Number of leaves         :   12 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 515 expanded)
%              Number of equality atoms :   84 ( 187 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
     => ( k2_relat_1(k5_relat_1(X0,sK2)) != k9_relat_1(sK2,k2_relat_1(X0))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK1,X1)) != k9_relat_1(X1,k2_relat_1(sK1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f22,f21])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_163,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_400,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_171,plain,
    ( r2_hidden(sK0(X0_40,X1_40),X0_40)
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_393,plain,
    ( r2_hidden(sK0(X0_40,X1_40),X0_40) = iProver_top
    | r1_tarski(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_172,plain,
    ( ~ r2_hidden(sK0(X0_40,X1_40),X1_40)
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_392,plain,
    ( r2_hidden(sK0(X0_40,X1_40),X1_40) != iProver_top
    | r1_tarski(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_723,plain,
    ( r1_tarski(X0_40,X0_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_393,c_392])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_166,plain,
    ( ~ r1_tarski(k1_relat_1(X0_39),X0_40)
    | ~ v1_relat_1(X0_39)
    | k7_relat_1(X0_39,X0_40) = X0_39 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_398,plain,
    ( k7_relat_1(X0_39,X0_40) = X0_39
    | r1_tarski(k1_relat_1(X0_39),X0_40) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_920,plain,
    ( k7_relat_1(X0_39,k1_relat_1(X0_39)) = X0_39
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_723,c_398])).

cnf(c_1480,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_400,c_920])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_164,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_399,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_170,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_394,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_168,plain,
    ( ~ v1_relat_1(X0_39)
    | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_396,plain,
    ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_611,plain,
    ( k2_relat_1(k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40)) = k9_relat_1(k5_relat_1(X0_39,X1_39),X0_40)
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_394,c_396])).

cnf(c_1362,plain,
    ( k2_relat_1(k7_relat_1(k5_relat_1(sK1,X0_39),X0_40)) = k9_relat_1(k5_relat_1(sK1,X0_39),X0_40)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_400,c_611])).

cnf(c_1975,plain,
    ( k2_relat_1(k7_relat_1(k5_relat_1(sK1,sK2),X0_40)) = k9_relat_1(k5_relat_1(sK1,sK2),X0_40) ),
    inference(superposition,[status(thm)],[c_399,c_1362])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_169,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_395,plain,
    ( k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39)
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_695,plain,
    ( k7_relat_1(k5_relat_1(sK1,X0_39),X0_40) = k5_relat_1(k7_relat_1(sK1,X0_40),X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_400,c_395])).

cnf(c_1130,plain,
    ( k7_relat_1(k5_relat_1(sK1,sK2),X0_40) = k5_relat_1(k7_relat_1(sK1,X0_40),sK2) ),
    inference(superposition,[status(thm)],[c_399,c_695])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_167,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | k9_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k9_relat_1(X1_39,k9_relat_1(X0_39,X0_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_397,plain,
    ( k9_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k9_relat_1(X1_39,k9_relat_1(X0_39,X0_40))
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_805,plain,
    ( k9_relat_1(X0_39,k9_relat_1(sK1,X0_40)) = k9_relat_1(k5_relat_1(sK1,X0_39),X0_40)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_400,c_397])).

cnf(c_1759,plain,
    ( k9_relat_1(k5_relat_1(sK1,sK2),X0_40) = k9_relat_1(sK2,k9_relat_1(sK1,X0_40)) ),
    inference(superposition,[status(thm)],[c_399,c_805])).

cnf(c_1988,plain,
    ( k2_relat_1(k5_relat_1(k7_relat_1(sK1,X0_40),sK2)) = k9_relat_1(sK2,k9_relat_1(sK1,X0_40)) ),
    inference(light_normalisation,[status(thm)],[c_1975,c_1130,c_1759])).

cnf(c_3278,plain,
    ( k9_relat_1(sK2,k9_relat_1(sK1,k1_relat_1(sK1))) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1480,c_1988])).

cnf(c_533,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0_40)) = k9_relat_1(sK1,X0_40) ),
    inference(superposition,[status(thm)],[c_400,c_396])).

cnf(c_1619,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1480,c_533])).

cnf(c_3279,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK1)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3278,c_1619])).

cnf(c_175,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_520,plain,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_178,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_483,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK1)) != X0_40
    | k2_relat_1(k5_relat_1(sK1,sK2)) != X0_40
    | k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_519,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK1)) != k2_relat_1(k5_relat_1(sK1,sK2))
    | k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1))
    | k2_relat_1(k5_relat_1(sK1,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_7,negated_conjecture,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_165,negated_conjecture,
    ( k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3279,c_520,c_519,c_165])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.01/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.99  
% 3.01/0.99  ------  iProver source info
% 3.01/0.99  
% 3.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.99  git: non_committed_changes: false
% 3.01/0.99  git: last_make_outside_of_git: false
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  ------ Parsing...
% 3.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.99  ------ Proving...
% 3.01/0.99  ------ Problem Properties 
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  clauses                                 10
% 3.01/0.99  conjectures                             3
% 3.01/0.99  EPR                                     2
% 3.01/0.99  Horn                                    9
% 3.01/0.99  unary                                   3
% 3.01/0.99  binary                                  3
% 3.01/0.99  lits                                    21
% 3.01/0.99  lits eq                                 5
% 3.01/0.99  fd_pure                                 0
% 3.01/0.99  fd_pseudo                               0
% 3.01/0.99  fd_cond                                 0
% 3.01/0.99  fd_pseudo_cond                          0
% 3.01/0.99  AC symbols                              0
% 3.01/0.99  
% 3.01/0.99  ------ Input Options Time Limit: Unbounded
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  Current options:
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ Proving...
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS status Theorem for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  fof(f7,conjecture,(
% 3.01/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f8,negated_conjecture,(
% 3.01/0.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.01/0.99    inference(negated_conjecture,[],[f7])).
% 3.01/0.99  
% 3.01/0.99  fof(f18,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f8])).
% 3.01/0.99  
% 3.01/0.99  fof(f22,plain,(
% 3.01/0.99    ( ! [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(X0,sK2)) != k9_relat_1(sK2,k2_relat_1(X0)) & v1_relat_1(sK2))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f21,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK1,X1)) != k9_relat_1(X1,k2_relat_1(sK1)) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f23,plain,(
% 3.01/0.99    (k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f22,f21])).
% 3.01/0.99  
% 3.01/0.99  fof(f31,plain,(
% 3.01/0.99    v1_relat_1(sK1)),
% 3.01/0.99    inference(cnf_transformation,[],[f23])).
% 3.01/0.99  
% 3.01/0.99  fof(f1,axiom,(
% 3.01/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f9,plain,(
% 3.01/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.01/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.01/0.99  
% 3.01/0.99  fof(f10,plain,(
% 3.01/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f9])).
% 3.01/0.99  
% 3.01/0.99  fof(f19,plain,(
% 3.01/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f20,plain,(
% 3.01/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).
% 3.01/0.99  
% 3.01/0.99  fof(f24,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f25,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f6,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f16,plain,(
% 3.01/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f6])).
% 3.01/0.99  
% 3.01/0.99  fof(f17,plain,(
% 3.01/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(flattening,[],[f16])).
% 3.01/0.99  
% 3.01/0.99  fof(f30,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f17])).
% 3.01/0.99  
% 3.01/0.99  fof(f32,plain,(
% 3.01/0.99    v1_relat_1(sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f23])).
% 3.01/0.99  
% 3.01/0.99  fof(f2,axiom,(
% 3.01/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f11,plain,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f2])).
% 3.01/0.99  
% 3.01/0.99  fof(f12,plain,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.01/0.99    inference(flattening,[],[f11])).
% 3.01/0.99  
% 3.01/0.99  fof(f26,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f12])).
% 3.01/0.99  
% 3.01/0.99  fof(f4,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f14,plain,(
% 3.01/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f4])).
% 3.01/0.99  
% 3.01/0.99  fof(f28,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f14])).
% 3.01/0.99  
% 3.01/0.99  fof(f3,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f13,plain,(
% 3.01/0.99    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f3])).
% 3.01/0.99  
% 3.01/0.99  fof(f27,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f13])).
% 3.01/0.99  
% 3.01/0.99  fof(f5,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)))),
% 3.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f15,plain,(
% 3.01/0.99    ! [X0,X1] : (! [X2] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f5])).
% 3.01/0.99  
% 3.01/0.99  fof(f29,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f15])).
% 3.01/0.99  
% 3.01/0.99  fof(f33,plain,(
% 3.01/0.99    k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1))),
% 3.01/0.99    inference(cnf_transformation,[],[f23])).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9,negated_conjecture,
% 3.01/0.99      ( v1_relat_1(sK1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_163,negated_conjecture,
% 3.01/0.99      ( v1_relat_1(sK1) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_400,plain,
% 3.01/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_171,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0_40,X1_40),X0_40) | r1_tarski(X0_40,X1_40) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_393,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0_40,X1_40),X0_40) = iProver_top
% 3.01/0.99      | r1_tarski(X0_40,X1_40) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_0,plain,
% 3.01/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_172,plain,
% 3.01/0.99      ( ~ r2_hidden(sK0(X0_40,X1_40),X1_40) | r1_tarski(X0_40,X1_40) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_392,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0_40,X1_40),X1_40) != iProver_top
% 3.01/0.99      | r1_tarski(X0_40,X1_40) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_172]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_723,plain,
% 3.01/0.99      ( r1_tarski(X0_40,X0_40) = iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_393,c_392]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6,plain,
% 3.01/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.01/0.99      | ~ v1_relat_1(X0)
% 3.01/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_166,plain,
% 3.01/0.99      ( ~ r1_tarski(k1_relat_1(X0_39),X0_40)
% 3.01/0.99      | ~ v1_relat_1(X0_39)
% 3.01/0.99      | k7_relat_1(X0_39,X0_40) = X0_39 ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_398,plain,
% 3.01/0.99      ( k7_relat_1(X0_39,X0_40) = X0_39
% 3.01/0.99      | r1_tarski(k1_relat_1(X0_39),X0_40) != iProver_top
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_166]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_920,plain,
% 3.01/0.99      ( k7_relat_1(X0_39,k1_relat_1(X0_39)) = X0_39
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_723,c_398]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1480,plain,
% 3.01/0.99      ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_400,c_920]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_8,negated_conjecture,
% 3.01/0.99      ( v1_relat_1(sK2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_164,negated_conjecture,
% 3.01/0.99      ( v1_relat_1(sK2) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_399,plain,
% 3.01/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0)
% 3.01/0.99      | ~ v1_relat_1(X1)
% 3.01/0.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_170,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0_39)
% 3.01/0.99      | ~ v1_relat_1(X1_39)
% 3.01/0.99      | v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_394,plain,
% 3.01/0.99      ( v1_relat_1(X0_39) != iProver_top
% 3.01/0.99      | v1_relat_1(X1_39) != iProver_top
% 3.01/0.99      | v1_relat_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0)
% 3.01/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_168,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0_39)
% 3.01/0.99      | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_396,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_611,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40)) = k9_relat_1(k5_relat_1(X0_39,X1_39),X0_40)
% 3.01/0.99      | v1_relat_1(X1_39) != iProver_top
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_394,c_396]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1362,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(k5_relat_1(sK1,X0_39),X0_40)) = k9_relat_1(k5_relat_1(sK1,X0_39),X0_40)
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_400,c_611]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1975,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(k5_relat_1(sK1,sK2),X0_40)) = k9_relat_1(k5_relat_1(sK1,sK2),X0_40) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_399,c_1362]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0)
% 3.01/0.99      | ~ v1_relat_1(X1)
% 3.01/0.99      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_169,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0_39)
% 3.01/0.99      | ~ v1_relat_1(X1_39)
% 3.01/0.99      | k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_395,plain,
% 3.01/0.99      ( k7_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k5_relat_1(k7_relat_1(X0_39,X0_40),X1_39)
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top
% 3.01/0.99      | v1_relat_1(X1_39) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_695,plain,
% 3.01/0.99      ( k7_relat_1(k5_relat_1(sK1,X0_39),X0_40) = k5_relat_1(k7_relat_1(sK1,X0_40),X0_39)
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_400,c_395]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1130,plain,
% 3.01/0.99      ( k7_relat_1(k5_relat_1(sK1,sK2),X0_40) = k5_relat_1(k7_relat_1(sK1,X0_40),sK2) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_399,c_695]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0)
% 3.01/0.99      | ~ v1_relat_1(X1)
% 3.01/0.99      | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_167,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0_39)
% 3.01/0.99      | ~ v1_relat_1(X1_39)
% 3.01/0.99      | k9_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k9_relat_1(X1_39,k9_relat_1(X0_39,X0_40)) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_397,plain,
% 3.01/0.99      ( k9_relat_1(k5_relat_1(X0_39,X1_39),X0_40) = k9_relat_1(X1_39,k9_relat_1(X0_39,X0_40))
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top
% 3.01/0.99      | v1_relat_1(X1_39) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_805,plain,
% 3.01/0.99      ( k9_relat_1(X0_39,k9_relat_1(sK1,X0_40)) = k9_relat_1(k5_relat_1(sK1,X0_39),X0_40)
% 3.01/0.99      | v1_relat_1(X0_39) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_400,c_397]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1759,plain,
% 3.01/0.99      ( k9_relat_1(k5_relat_1(sK1,sK2),X0_40) = k9_relat_1(sK2,k9_relat_1(sK1,X0_40)) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_399,c_805]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1988,plain,
% 3.01/0.99      ( k2_relat_1(k5_relat_1(k7_relat_1(sK1,X0_40),sK2)) = k9_relat_1(sK2,k9_relat_1(sK1,X0_40)) ),
% 3.01/0.99      inference(light_normalisation,[status(thm)],[c_1975,c_1130,c_1759]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3278,plain,
% 3.01/0.99      ( k9_relat_1(sK2,k9_relat_1(sK1,k1_relat_1(sK1))) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1480,c_1988]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_533,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(sK1,X0_40)) = k9_relat_1(sK1,X0_40) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_400,c_396]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1619,plain,
% 3.01/0.99      ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1480,c_533]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3279,plain,
% 3.01/0.99      ( k9_relat_1(sK2,k2_relat_1(sK1)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
% 3.01/0.99      inference(light_normalisation,[status(thm)],[c_3278,c_1619]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_175,plain,( X0_40 = X0_40 ),theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_520,plain,
% 3.01/0.99      ( k2_relat_1(k5_relat_1(sK1,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_175]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_178,plain,
% 3.01/0.99      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_483,plain,
% 3.01/0.99      ( k9_relat_1(sK2,k2_relat_1(sK1)) != X0_40
% 3.01/0.99      | k2_relat_1(k5_relat_1(sK1,sK2)) != X0_40
% 3.01/0.99      | k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_178]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_519,plain,
% 3.01/0.99      ( k9_relat_1(sK2,k2_relat_1(sK1)) != k2_relat_1(k5_relat_1(sK1,sK2))
% 3.01/0.99      | k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1))
% 3.01/0.99      | k2_relat_1(k5_relat_1(sK1,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_483]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7,negated_conjecture,
% 3.01/0.99      ( k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_165,negated_conjecture,
% 3.01/0.99      ( k2_relat_1(k5_relat_1(sK1,sK2)) != k9_relat_1(sK2,k2_relat_1(sK1)) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(contradiction,plain,
% 3.01/0.99      ( $false ),
% 3.01/0.99      inference(minisat,[status(thm)],[c_3279,c_520,c_519,c_165]) ).
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  ------                               Statistics
% 3.01/0.99  
% 3.01/0.99  ------ Selected
% 3.01/0.99  
% 3.01/0.99  total_time:                             0.143
% 3.01/0.99  
%------------------------------------------------------------------------------
