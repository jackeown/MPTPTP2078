%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0487+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:41 EST 2020

% Result     : Theorem 55.06s
% Output     : CNFRefutation 55.06s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 141 expanded)
%              Number of clauses        :   32 (  37 expanded)
%              Number of leaves         :    9 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 826 expanded)
%              Number of equality atoms :   90 ( 393 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f726,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f727,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                    & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
                    & r1_tarski(k2_relat_1(X1),X0) )
                 => X1 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f726])).

fof(f1260,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f727])).

fof(f1261,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1260])).

fof(f1692,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X1 != X3
          & k6_relat_1(X0) = k5_relat_1(X2,X3)
          & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
          & r1_tarski(k2_relat_1(X1),X0)
          & v1_relat_1(X3) )
     => ( sK155 != X1
        & k6_relat_1(X0) = k5_relat_1(X2,sK155)
        & k6_relat_1(k1_relat_1(sK155)) = k5_relat_1(X1,X2)
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(sK155) ) ) ),
    introduced(choice_axiom,[])).

fof(f1691,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( X1 != X3
            & k6_relat_1(X0) = k5_relat_1(sK154,X3)
            & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,sK154)
            & r1_tarski(k2_relat_1(X1),X0)
            & v1_relat_1(X3) )
        & v1_relat_1(sK154) ) ) ),
    introduced(choice_axiom,[])).

fof(f1690,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X1 != X3
                & k6_relat_1(X0) = k5_relat_1(X2,X3)
                & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
                & r1_tarski(k2_relat_1(X1),X0)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK153 != X3
              & k6_relat_1(sK152) = k5_relat_1(X2,X3)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK153,X2)
              & r1_tarski(k2_relat_1(sK153),sK152)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK153) ) ),
    introduced(choice_axiom,[])).

fof(f1693,plain,
    ( sK153 != sK155
    & k6_relat_1(sK152) = k5_relat_1(sK154,sK155)
    & k6_relat_1(k1_relat_1(sK155)) = k5_relat_1(sK153,sK154)
    & r1_tarski(k2_relat_1(sK153),sK152)
    & v1_relat_1(sK155)
    & v1_relat_1(sK154)
    & v1_relat_1(sK153) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK152,sK153,sK154,sK155])],[f1261,f1692,f1691,f1690])).

fof(f2832,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1693])).

fof(f2831,plain,(
    v1_relat_1(sK154) ),
    inference(cnf_transformation,[],[f1693])).

fof(f2830,plain,(
    v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f1693])).

fof(f706,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1240,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f2799,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1240])).

fof(f2834,plain,(
    k6_relat_1(k1_relat_1(sK155)) = k5_relat_1(sK153,sK154) ),
    inference(cnf_transformation,[],[f1693])).

fof(f2835,plain,(
    k6_relat_1(sK152) = k5_relat_1(sK154,sK155) ),
    inference(cnf_transformation,[],[f1693])).

fof(f2833,plain,(
    r1_tarski(k2_relat_1(sK153),sK152) ),
    inference(cnf_transformation,[],[f1693])).

fof(f723,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1257,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f1258,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1257])).

fof(f2827,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1258])).

fof(f722,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1256,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f722])).

fof(f2826,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1256])).

fof(f2836,plain,(
    sK153 != sK155 ),
    inference(cnf_transformation,[],[f1693])).

cnf(c_1126,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f2832])).

cnf(c_46813,plain,
    ( v1_relat_1(sK155) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_1127,negated_conjecture,
    ( v1_relat_1(sK154) ),
    inference(cnf_transformation,[],[f2831])).

cnf(c_46812,plain,
    ( v1_relat_1(sK154) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_1128,negated_conjecture,
    ( v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f2830])).

cnf(c_46811,plain,
    ( v1_relat_1(sK153) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_1091,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f2799])).

cnf(c_46837,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_140447,plain,
    ( k5_relat_1(sK153,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK153,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_46811,c_46837])).

cnf(c_225532,plain,
    ( k5_relat_1(k5_relat_1(sK153,sK154),X0) = k5_relat_1(sK153,k5_relat_1(sK154,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_46812,c_140447])).

cnf(c_1124,negated_conjecture,
    ( k6_relat_1(k1_relat_1(sK155)) = k5_relat_1(sK153,sK154) ),
    inference(cnf_transformation,[],[f2834])).

cnf(c_225637,plain,
    ( k5_relat_1(sK153,k5_relat_1(sK154,X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK155)),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_225532,c_1124])).

cnf(c_225959,plain,
    ( k5_relat_1(sK153,k5_relat_1(sK154,sK155)) = k5_relat_1(k6_relat_1(k1_relat_1(sK155)),sK155) ),
    inference(superposition,[status(thm)],[c_46813,c_225637])).

cnf(c_1123,negated_conjecture,
    ( k6_relat_1(sK152) = k5_relat_1(sK154,sK155) ),
    inference(cnf_transformation,[],[f2835])).

cnf(c_1125,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK153),sK152) ),
    inference(cnf_transformation,[],[f2833])).

cnf(c_46814,plain,
    ( r1_tarski(k2_relat_1(sK153),sK152) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_1119,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f2827])).

cnf(c_46816,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_63504,plain,
    ( k5_relat_1(sK153,k6_relat_1(sK152)) = sK153
    | v1_relat_1(sK153) != iProver_top ),
    inference(superposition,[status(thm)],[c_46814,c_46816])).

cnf(c_56353,plain,
    ( ~ r1_tarski(k2_relat_1(sK153),sK152)
    | ~ v1_relat_1(sK153)
    | k5_relat_1(sK153,k6_relat_1(sK152)) = sK153 ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_65113,plain,
    ( k5_relat_1(sK153,k6_relat_1(sK152)) = sK153 ),
    inference(global_propositional_subsumption,[status(thm)],[c_63504,c_1128,c_1125,c_56353])).

cnf(c_1118,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f2826])).

cnf(c_46817,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_68328,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK155)),sK155) = sK155 ),
    inference(superposition,[status(thm)],[c_46813,c_46817])).

cnf(c_226038,plain,
    ( sK155 = sK153 ),
    inference(light_normalisation,[status(thm)],[c_225959,c_1123,c_65113,c_68328])).

cnf(c_30887,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_96431,plain,
    ( sK153 = sK153 ),
    inference(instantiation,[status(thm)],[c_30887])).

cnf(c_30888,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_56529,plain,
    ( sK155 != X0
    | sK153 != X0
    | sK153 = sK155 ),
    inference(instantiation,[status(thm)],[c_30888])).

cnf(c_96430,plain,
    ( sK155 != sK153
    | sK153 = sK155
    | sK153 != sK153 ),
    inference(instantiation,[status(thm)],[c_56529])).

cnf(c_1122,negated_conjecture,
    ( sK153 != sK155 ),
    inference(cnf_transformation,[],[f2836])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_226038,c_96431,c_96430,c_1122])).

%------------------------------------------------------------------------------
