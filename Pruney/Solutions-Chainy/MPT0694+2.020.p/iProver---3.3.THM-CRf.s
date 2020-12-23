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
% DateTime   : Thu Dec  3 11:51:59 EST 2020

% Result     : Theorem 13.91s
% Output     : CNFRefutation 13.91s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 121 expanded)
%              Number of clauses        :   58 (  62 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  256 ( 313 expanded)
%              Number of equality atoms :   77 (  90 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f47,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f47,f34,f34])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_239,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_9047,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X2_41)
    | X1_41 != X2_41
    | X0_41 != k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_41154,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1_41)
    | X0_41 != X1_41
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_9047])).

cnf(c_41162,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_41154])).

cnf(c_235,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_13805,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_237,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_1058,plain,
    ( X0_41 != X1_41
    | X0_41 = k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != X1_41 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_2368,plain,
    ( X0_41 != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | X0_41 = k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_7326,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ v1_relat_1(X0_40)
    | k9_relat_1(k7_relat_1(X0_40,X1_41),X0_41) = k9_relat_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3592,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
    | ~ v1_relat_1(X0_40)
    | k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_3594,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_3592])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_223,plain,
    ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41)
    | ~ v1_funct_1(X0_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_786,plain,
    ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
    | ~ v1_funct_1(X0_40)
    | ~ v1_relat_1(X0_40) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_3018,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | ~ v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_503,plain,
    ( X0_41 != X1_41
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X1_41
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = X0_41 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_524,plain,
    ( X0_41 != k9_relat_1(X0_40,X1_41)
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = X0_41
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,X1_41) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_1910,plain,
    ( X0_41 != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = X0_41
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_2973,plain,
    ( k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_2974,plain,
    ( k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_2973])).

cnf(c_493,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_41
    | sK1 != X1_41 ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_515,plain,
    ( ~ r1_tarski(X0_41,sK1)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_41
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_629,plain,
    ( ~ r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,k10_relat_1(X0_40,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_1914,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_224,plain,
    ( ~ v1_relat_1(X0_40)
    | k4_xboole_0(X0_41,k4_xboole_0(X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_960,plain,
    ( ~ v1_relat_1(sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_230,plain,
    ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_899,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_242,plain,
    ( X0_41 != X1_41
    | k9_relat_1(X0_40,X0_41) = k9_relat_1(X1_40,X1_41)
    | X0_40 != X1_40 ),
    theory(equality)).

cnf(c_601,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0_40,X0_41)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != X0_41
    | sK2 != X0_40 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_765,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | sK2 != X0_40 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_766,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k9_relat_1(X0_40,X0_41),k9_relat_1(X0_40,X1_41))
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_574,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,X0_41))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0_41)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_576,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_564,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_231,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X0_41,X2_41)
    | r1_tarski(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_485,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_225,plain,
    ( ~ v1_funct_1(X0_40)
    | v1_funct_1(k7_relat_1(X0_40,X0_41))
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_274,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_228,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k7_relat_1(X0_40,X0_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_265,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_254,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_234,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_253,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41162,c_13805,c_7326,c_3594,c_3018,c_2974,c_1914,c_960,c_899,c_766,c_576,c_564,c_485,c_274,c_265,c_254,c_253,c_11,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 13.91/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.91/2.50  
% 13.91/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 13.91/2.50  
% 13.91/2.50  ------  iProver source info
% 13.91/2.50  
% 13.91/2.50  git: date: 2020-06-30 10:37:57 +0100
% 13.91/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 13.91/2.50  git: non_committed_changes: false
% 13.91/2.50  git: last_make_outside_of_git: false
% 13.91/2.50  
% 13.91/2.50  ------ 
% 13.91/2.50  
% 13.91/2.50  ------ Input Options
% 13.91/2.50  
% 13.91/2.50  --out_options                           all
% 13.91/2.50  --tptp_safe_out                         true
% 13.91/2.50  --problem_path                          ""
% 13.91/2.50  --include_path                          ""
% 13.91/2.50  --clausifier                            res/vclausify_rel
% 13.91/2.50  --clausifier_options                    ""
% 13.91/2.50  --stdin                                 false
% 13.91/2.50  --stats_out                             all
% 13.91/2.50  
% 13.91/2.50  ------ General Options
% 13.91/2.50  
% 13.91/2.50  --fof                                   false
% 13.91/2.50  --time_out_real                         305.
% 13.91/2.50  --time_out_virtual                      -1.
% 13.91/2.50  --symbol_type_check                     false
% 13.91/2.50  --clausify_out                          false
% 13.91/2.50  --sig_cnt_out                           false
% 13.91/2.50  --trig_cnt_out                          false
% 13.91/2.50  --trig_cnt_out_tolerance                1.
% 13.91/2.50  --trig_cnt_out_sk_spl                   false
% 13.91/2.50  --abstr_cl_out                          false
% 13.91/2.50  
% 13.91/2.50  ------ Global Options
% 13.91/2.50  
% 13.91/2.50  --schedule                              default
% 13.91/2.50  --add_important_lit                     false
% 13.91/2.50  --prop_solver_per_cl                    1000
% 13.91/2.50  --min_unsat_core                        false
% 13.91/2.50  --soft_assumptions                      false
% 13.91/2.50  --soft_lemma_size                       3
% 13.91/2.50  --prop_impl_unit_size                   0
% 13.91/2.50  --prop_impl_unit                        []
% 13.91/2.50  --share_sel_clauses                     true
% 13.91/2.50  --reset_solvers                         false
% 13.91/2.50  --bc_imp_inh                            [conj_cone]
% 13.91/2.50  --conj_cone_tolerance                   3.
% 13.91/2.50  --extra_neg_conj                        none
% 13.91/2.50  --large_theory_mode                     true
% 13.91/2.50  --prolific_symb_bound                   200
% 13.91/2.50  --lt_threshold                          2000
% 13.91/2.50  --clause_weak_htbl                      true
% 13.91/2.50  --gc_record_bc_elim                     false
% 13.91/2.50  
% 13.91/2.50  ------ Preprocessing Options
% 13.91/2.50  
% 13.91/2.50  --preprocessing_flag                    true
% 13.91/2.50  --time_out_prep_mult                    0.1
% 13.91/2.50  --splitting_mode                        input
% 13.91/2.50  --splitting_grd                         true
% 13.91/2.50  --splitting_cvd                         false
% 13.91/2.50  --splitting_cvd_svl                     false
% 13.91/2.50  --splitting_nvd                         32
% 13.91/2.50  --sub_typing                            true
% 13.91/2.50  --prep_gs_sim                           true
% 13.91/2.50  --prep_unflatten                        true
% 13.91/2.50  --prep_res_sim                          true
% 13.91/2.50  --prep_upred                            true
% 13.91/2.50  --prep_sem_filter                       exhaustive
% 13.91/2.50  --prep_sem_filter_out                   false
% 13.91/2.50  --pred_elim                             true
% 13.91/2.50  --res_sim_input                         true
% 13.91/2.50  --eq_ax_congr_red                       true
% 13.91/2.50  --pure_diseq_elim                       true
% 13.91/2.50  --brand_transform                       false
% 13.91/2.50  --non_eq_to_eq                          false
% 13.91/2.50  --prep_def_merge                        true
% 13.91/2.50  --prep_def_merge_prop_impl              false
% 13.91/2.50  --prep_def_merge_mbd                    true
% 13.91/2.50  --prep_def_merge_tr_red                 false
% 13.91/2.50  --prep_def_merge_tr_cl                  false
% 13.91/2.50  --smt_preprocessing                     true
% 13.91/2.50  --smt_ac_axioms                         fast
% 13.91/2.50  --preprocessed_out                      false
% 13.91/2.50  --preprocessed_stats                    false
% 13.91/2.50  
% 13.91/2.50  ------ Abstraction refinement Options
% 13.91/2.50  
% 13.91/2.50  --abstr_ref                             []
% 13.91/2.50  --abstr_ref_prep                        false
% 13.91/2.50  --abstr_ref_until_sat                   false
% 13.91/2.50  --abstr_ref_sig_restrict                funpre
% 13.91/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 13.91/2.50  --abstr_ref_under                       []
% 13.91/2.50  
% 13.91/2.50  ------ SAT Options
% 13.91/2.50  
% 13.91/2.50  --sat_mode                              false
% 13.91/2.50  --sat_fm_restart_options                ""
% 13.91/2.50  --sat_gr_def                            false
% 13.91/2.50  --sat_epr_types                         true
% 13.91/2.50  --sat_non_cyclic_types                  false
% 13.91/2.50  --sat_finite_models                     false
% 13.91/2.50  --sat_fm_lemmas                         false
% 13.91/2.50  --sat_fm_prep                           false
% 13.91/2.50  --sat_fm_uc_incr                        true
% 13.91/2.50  --sat_out_model                         small
% 13.91/2.50  --sat_out_clauses                       false
% 13.91/2.50  
% 13.91/2.50  ------ QBF Options
% 13.91/2.50  
% 13.91/2.50  --qbf_mode                              false
% 13.91/2.50  --qbf_elim_univ                         false
% 13.91/2.50  --qbf_dom_inst                          none
% 13.91/2.50  --qbf_dom_pre_inst                      false
% 13.91/2.50  --qbf_sk_in                             false
% 13.91/2.50  --qbf_pred_elim                         true
% 13.91/2.50  --qbf_split                             512
% 13.91/2.50  
% 13.91/2.50  ------ BMC1 Options
% 13.91/2.50  
% 13.91/2.50  --bmc1_incremental                      false
% 13.91/2.50  --bmc1_axioms                           reachable_all
% 13.91/2.50  --bmc1_min_bound                        0
% 13.91/2.50  --bmc1_max_bound                        -1
% 13.91/2.50  --bmc1_max_bound_default                -1
% 13.91/2.50  --bmc1_symbol_reachability              true
% 13.91/2.50  --bmc1_property_lemmas                  false
% 13.91/2.50  --bmc1_k_induction                      false
% 13.91/2.50  --bmc1_non_equiv_states                 false
% 13.91/2.50  --bmc1_deadlock                         false
% 13.91/2.50  --bmc1_ucm                              false
% 13.91/2.50  --bmc1_add_unsat_core                   none
% 13.91/2.50  --bmc1_unsat_core_children              false
% 13.91/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 13.91/2.50  --bmc1_out_stat                         full
% 13.91/2.50  --bmc1_ground_init                      false
% 13.91/2.50  --bmc1_pre_inst_next_state              false
% 13.91/2.50  --bmc1_pre_inst_state                   false
% 13.91/2.50  --bmc1_pre_inst_reach_state             false
% 13.91/2.50  --bmc1_out_unsat_core                   false
% 13.91/2.50  --bmc1_aig_witness_out                  false
% 13.91/2.50  --bmc1_verbose                          false
% 13.91/2.50  --bmc1_dump_clauses_tptp                false
% 13.91/2.50  --bmc1_dump_unsat_core_tptp             false
% 13.91/2.50  --bmc1_dump_file                        -
% 13.91/2.50  --bmc1_ucm_expand_uc_limit              128
% 13.91/2.50  --bmc1_ucm_n_expand_iterations          6
% 13.91/2.50  --bmc1_ucm_extend_mode                  1
% 13.91/2.50  --bmc1_ucm_init_mode                    2
% 13.91/2.50  --bmc1_ucm_cone_mode                    none
% 13.91/2.50  --bmc1_ucm_reduced_relation_type        0
% 13.91/2.50  --bmc1_ucm_relax_model                  4
% 13.91/2.50  --bmc1_ucm_full_tr_after_sat            true
% 13.91/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 13.91/2.50  --bmc1_ucm_layered_model                none
% 13.91/2.50  --bmc1_ucm_max_lemma_size               10
% 13.91/2.50  
% 13.91/2.50  ------ AIG Options
% 13.91/2.50  
% 13.91/2.50  --aig_mode                              false
% 13.91/2.50  
% 13.91/2.50  ------ Instantiation Options
% 13.91/2.50  
% 13.91/2.50  --instantiation_flag                    true
% 13.91/2.50  --inst_sos_flag                         true
% 13.91/2.50  --inst_sos_phase                        true
% 13.91/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 13.91/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 13.91/2.50  --inst_lit_sel_side                     num_symb
% 13.91/2.50  --inst_solver_per_active                1400
% 13.91/2.50  --inst_solver_calls_frac                1.
% 13.91/2.50  --inst_passive_queue_type               priority_queues
% 13.91/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 13.91/2.50  --inst_passive_queues_freq              [25;2]
% 13.91/2.50  --inst_dismatching                      true
% 13.91/2.50  --inst_eager_unprocessed_to_passive     true
% 13.91/2.50  --inst_prop_sim_given                   true
% 13.91/2.50  --inst_prop_sim_new                     false
% 13.91/2.50  --inst_subs_new                         false
% 13.91/2.50  --inst_eq_res_simp                      false
% 13.91/2.50  --inst_subs_given                       false
% 13.91/2.50  --inst_orphan_elimination               true
% 13.91/2.50  --inst_learning_loop_flag               true
% 13.91/2.50  --inst_learning_start                   3000
% 13.91/2.50  --inst_learning_factor                  2
% 13.91/2.50  --inst_start_prop_sim_after_learn       3
% 13.91/2.50  --inst_sel_renew                        solver
% 13.91/2.50  --inst_lit_activity_flag                true
% 13.91/2.50  --inst_restr_to_given                   false
% 13.91/2.50  --inst_activity_threshold               500
% 13.91/2.50  --inst_out_proof                        true
% 13.91/2.50  
% 13.91/2.50  ------ Resolution Options
% 13.91/2.50  
% 13.91/2.50  --resolution_flag                       true
% 13.91/2.50  --res_lit_sel                           adaptive
% 13.91/2.50  --res_lit_sel_side                      none
% 13.91/2.50  --res_ordering                          kbo
% 13.91/2.50  --res_to_prop_solver                    active
% 13.91/2.50  --res_prop_simpl_new                    false
% 13.91/2.50  --res_prop_simpl_given                  true
% 13.91/2.50  --res_passive_queue_type                priority_queues
% 13.91/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 13.91/2.50  --res_passive_queues_freq               [15;5]
% 13.91/2.50  --res_forward_subs                      full
% 13.91/2.50  --res_backward_subs                     full
% 13.91/2.50  --res_forward_subs_resolution           true
% 13.91/2.50  --res_backward_subs_resolution          true
% 13.91/2.50  --res_orphan_elimination                true
% 13.91/2.50  --res_time_limit                        2.
% 13.91/2.50  --res_out_proof                         true
% 13.91/2.50  
% 13.91/2.50  ------ Superposition Options
% 13.91/2.50  
% 13.91/2.50  --superposition_flag                    true
% 13.91/2.50  --sup_passive_queue_type                priority_queues
% 13.91/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 13.91/2.50  --sup_passive_queues_freq               [8;1;4]
% 13.91/2.50  --demod_completeness_check              fast
% 13.91/2.50  --demod_use_ground                      true
% 13.91/2.50  --sup_to_prop_solver                    passive
% 13.91/2.50  --sup_prop_simpl_new                    true
% 13.91/2.50  --sup_prop_simpl_given                  true
% 13.91/2.50  --sup_fun_splitting                     true
% 13.91/2.50  --sup_smt_interval                      50000
% 13.91/2.50  
% 13.91/2.50  ------ Superposition Simplification Setup
% 13.91/2.50  
% 13.91/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 13.91/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 13.91/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 13.91/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 13.91/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 13.91/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 13.91/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 13.91/2.50  --sup_immed_triv                        [TrivRules]
% 13.91/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 13.91/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 13.91/2.50  --sup_immed_bw_main                     []
% 13.91/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 13.91/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 13.91/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 13.91/2.50  --sup_input_bw                          []
% 13.91/2.50  
% 13.91/2.50  ------ Combination Options
% 13.91/2.50  
% 13.91/2.50  --comb_res_mult                         3
% 13.91/2.50  --comb_sup_mult                         2
% 13.91/2.50  --comb_inst_mult                        10
% 13.91/2.50  
% 13.91/2.50  ------ Debug Options
% 13.91/2.50  
% 13.91/2.50  --dbg_backtrace                         false
% 13.91/2.50  --dbg_dump_prop_clauses                 false
% 13.91/2.50  --dbg_dump_prop_clauses_file            -
% 13.91/2.50  --dbg_out_stat                          false
% 13.91/2.50  ------ Parsing...
% 13.91/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 13.91/2.50  
% 13.91/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 13.91/2.50  
% 13.91/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 13.91/2.50  
% 13.91/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 13.91/2.50  ------ Proving...
% 13.91/2.50  ------ Problem Properties 
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  clauses                                 13
% 13.91/2.50  conjectures                             3
% 13.91/2.50  EPR                                     2
% 13.91/2.50  Horn                                    13
% 13.91/2.50  unary                                   6
% 13.91/2.50  binary                                  2
% 13.91/2.50  lits                                    25
% 13.91/2.50  lits eq                                 4
% 13.91/2.50  fd_pure                                 0
% 13.91/2.50  fd_pseudo                               0
% 13.91/2.50  fd_cond                                 0
% 13.91/2.50  fd_pseudo_cond                          0
% 13.91/2.50  AC symbols                              0
% 13.91/2.50  
% 13.91/2.50  ------ Schedule dynamic 5 is on 
% 13.91/2.50  
% 13.91/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  ------ 
% 13.91/2.50  Current options:
% 13.91/2.50  ------ 
% 13.91/2.50  
% 13.91/2.50  ------ Input Options
% 13.91/2.50  
% 13.91/2.50  --out_options                           all
% 13.91/2.50  --tptp_safe_out                         true
% 13.91/2.50  --problem_path                          ""
% 13.91/2.50  --include_path                          ""
% 13.91/2.50  --clausifier                            res/vclausify_rel
% 13.91/2.50  --clausifier_options                    ""
% 13.91/2.50  --stdin                                 false
% 13.91/2.50  --stats_out                             all
% 13.91/2.50  
% 13.91/2.50  ------ General Options
% 13.91/2.50  
% 13.91/2.50  --fof                                   false
% 13.91/2.50  --time_out_real                         305.
% 13.91/2.50  --time_out_virtual                      -1.
% 13.91/2.50  --symbol_type_check                     false
% 13.91/2.50  --clausify_out                          false
% 13.91/2.50  --sig_cnt_out                           false
% 13.91/2.50  --trig_cnt_out                          false
% 13.91/2.50  --trig_cnt_out_tolerance                1.
% 13.91/2.50  --trig_cnt_out_sk_spl                   false
% 13.91/2.50  --abstr_cl_out                          false
% 13.91/2.50  
% 13.91/2.50  ------ Global Options
% 13.91/2.50  
% 13.91/2.50  --schedule                              default
% 13.91/2.50  --add_important_lit                     false
% 13.91/2.50  --prop_solver_per_cl                    1000
% 13.91/2.50  --min_unsat_core                        false
% 13.91/2.50  --soft_assumptions                      false
% 13.91/2.50  --soft_lemma_size                       3
% 13.91/2.50  --prop_impl_unit_size                   0
% 13.91/2.50  --prop_impl_unit                        []
% 13.91/2.50  --share_sel_clauses                     true
% 13.91/2.50  --reset_solvers                         false
% 13.91/2.50  --bc_imp_inh                            [conj_cone]
% 13.91/2.50  --conj_cone_tolerance                   3.
% 13.91/2.50  --extra_neg_conj                        none
% 13.91/2.50  --large_theory_mode                     true
% 13.91/2.50  --prolific_symb_bound                   200
% 13.91/2.50  --lt_threshold                          2000
% 13.91/2.50  --clause_weak_htbl                      true
% 13.91/2.50  --gc_record_bc_elim                     false
% 13.91/2.50  
% 13.91/2.50  ------ Preprocessing Options
% 13.91/2.50  
% 13.91/2.50  --preprocessing_flag                    true
% 13.91/2.50  --time_out_prep_mult                    0.1
% 13.91/2.50  --splitting_mode                        input
% 13.91/2.50  --splitting_grd                         true
% 13.91/2.50  --splitting_cvd                         false
% 13.91/2.50  --splitting_cvd_svl                     false
% 13.91/2.50  --splitting_nvd                         32
% 13.91/2.50  --sub_typing                            true
% 13.91/2.50  --prep_gs_sim                           true
% 13.91/2.50  --prep_unflatten                        true
% 13.91/2.50  --prep_res_sim                          true
% 13.91/2.50  --prep_upred                            true
% 13.91/2.50  --prep_sem_filter                       exhaustive
% 13.91/2.50  --prep_sem_filter_out                   false
% 13.91/2.50  --pred_elim                             true
% 13.91/2.50  --res_sim_input                         true
% 13.91/2.50  --eq_ax_congr_red                       true
% 13.91/2.50  --pure_diseq_elim                       true
% 13.91/2.50  --brand_transform                       false
% 13.91/2.50  --non_eq_to_eq                          false
% 13.91/2.50  --prep_def_merge                        true
% 13.91/2.50  --prep_def_merge_prop_impl              false
% 13.91/2.50  --prep_def_merge_mbd                    true
% 13.91/2.50  --prep_def_merge_tr_red                 false
% 13.91/2.50  --prep_def_merge_tr_cl                  false
% 13.91/2.50  --smt_preprocessing                     true
% 13.91/2.50  --smt_ac_axioms                         fast
% 13.91/2.50  --preprocessed_out                      false
% 13.91/2.50  --preprocessed_stats                    false
% 13.91/2.50  
% 13.91/2.50  ------ Abstraction refinement Options
% 13.91/2.50  
% 13.91/2.50  --abstr_ref                             []
% 13.91/2.50  --abstr_ref_prep                        false
% 13.91/2.50  --abstr_ref_until_sat                   false
% 13.91/2.50  --abstr_ref_sig_restrict                funpre
% 13.91/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 13.91/2.50  --abstr_ref_under                       []
% 13.91/2.50  
% 13.91/2.50  ------ SAT Options
% 13.91/2.50  
% 13.91/2.50  --sat_mode                              false
% 13.91/2.50  --sat_fm_restart_options                ""
% 13.91/2.50  --sat_gr_def                            false
% 13.91/2.50  --sat_epr_types                         true
% 13.91/2.50  --sat_non_cyclic_types                  false
% 13.91/2.50  --sat_finite_models                     false
% 13.91/2.50  --sat_fm_lemmas                         false
% 13.91/2.50  --sat_fm_prep                           false
% 13.91/2.50  --sat_fm_uc_incr                        true
% 13.91/2.50  --sat_out_model                         small
% 13.91/2.50  --sat_out_clauses                       false
% 13.91/2.50  
% 13.91/2.50  ------ QBF Options
% 13.91/2.50  
% 13.91/2.50  --qbf_mode                              false
% 13.91/2.50  --qbf_elim_univ                         false
% 13.91/2.50  --qbf_dom_inst                          none
% 13.91/2.50  --qbf_dom_pre_inst                      false
% 13.91/2.50  --qbf_sk_in                             false
% 13.91/2.50  --qbf_pred_elim                         true
% 13.91/2.50  --qbf_split                             512
% 13.91/2.50  
% 13.91/2.50  ------ BMC1 Options
% 13.91/2.50  
% 13.91/2.50  --bmc1_incremental                      false
% 13.91/2.50  --bmc1_axioms                           reachable_all
% 13.91/2.50  --bmc1_min_bound                        0
% 13.91/2.50  --bmc1_max_bound                        -1
% 13.91/2.50  --bmc1_max_bound_default                -1
% 13.91/2.50  --bmc1_symbol_reachability              true
% 13.91/2.50  --bmc1_property_lemmas                  false
% 13.91/2.50  --bmc1_k_induction                      false
% 13.91/2.50  --bmc1_non_equiv_states                 false
% 13.91/2.50  --bmc1_deadlock                         false
% 13.91/2.50  --bmc1_ucm                              false
% 13.91/2.50  --bmc1_add_unsat_core                   none
% 13.91/2.50  --bmc1_unsat_core_children              false
% 13.91/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 13.91/2.50  --bmc1_out_stat                         full
% 13.91/2.50  --bmc1_ground_init                      false
% 13.91/2.50  --bmc1_pre_inst_next_state              false
% 13.91/2.50  --bmc1_pre_inst_state                   false
% 13.91/2.50  --bmc1_pre_inst_reach_state             false
% 13.91/2.50  --bmc1_out_unsat_core                   false
% 13.91/2.50  --bmc1_aig_witness_out                  false
% 13.91/2.50  --bmc1_verbose                          false
% 13.91/2.50  --bmc1_dump_clauses_tptp                false
% 13.91/2.50  --bmc1_dump_unsat_core_tptp             false
% 13.91/2.50  --bmc1_dump_file                        -
% 13.91/2.50  --bmc1_ucm_expand_uc_limit              128
% 13.91/2.50  --bmc1_ucm_n_expand_iterations          6
% 13.91/2.50  --bmc1_ucm_extend_mode                  1
% 13.91/2.50  --bmc1_ucm_init_mode                    2
% 13.91/2.50  --bmc1_ucm_cone_mode                    none
% 13.91/2.50  --bmc1_ucm_reduced_relation_type        0
% 13.91/2.50  --bmc1_ucm_relax_model                  4
% 13.91/2.50  --bmc1_ucm_full_tr_after_sat            true
% 13.91/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 13.91/2.50  --bmc1_ucm_layered_model                none
% 13.91/2.50  --bmc1_ucm_max_lemma_size               10
% 13.91/2.50  
% 13.91/2.50  ------ AIG Options
% 13.91/2.50  
% 13.91/2.50  --aig_mode                              false
% 13.91/2.50  
% 13.91/2.50  ------ Instantiation Options
% 13.91/2.50  
% 13.91/2.50  --instantiation_flag                    true
% 13.91/2.50  --inst_sos_flag                         true
% 13.91/2.50  --inst_sos_phase                        true
% 13.91/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 13.91/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 13.91/2.50  --inst_lit_sel_side                     none
% 13.91/2.50  --inst_solver_per_active                1400
% 13.91/2.50  --inst_solver_calls_frac                1.
% 13.91/2.50  --inst_passive_queue_type               priority_queues
% 13.91/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 13.91/2.50  --inst_passive_queues_freq              [25;2]
% 13.91/2.50  --inst_dismatching                      true
% 13.91/2.50  --inst_eager_unprocessed_to_passive     true
% 13.91/2.50  --inst_prop_sim_given                   true
% 13.91/2.50  --inst_prop_sim_new                     false
% 13.91/2.50  --inst_subs_new                         false
% 13.91/2.50  --inst_eq_res_simp                      false
% 13.91/2.50  --inst_subs_given                       false
% 13.91/2.50  --inst_orphan_elimination               true
% 13.91/2.50  --inst_learning_loop_flag               true
% 13.91/2.50  --inst_learning_start                   3000
% 13.91/2.50  --inst_learning_factor                  2
% 13.91/2.50  --inst_start_prop_sim_after_learn       3
% 13.91/2.50  --inst_sel_renew                        solver
% 13.91/2.50  --inst_lit_activity_flag                true
% 13.91/2.50  --inst_restr_to_given                   false
% 13.91/2.50  --inst_activity_threshold               500
% 13.91/2.50  --inst_out_proof                        true
% 13.91/2.50  
% 13.91/2.50  ------ Resolution Options
% 13.91/2.50  
% 13.91/2.50  --resolution_flag                       false
% 13.91/2.50  --res_lit_sel                           adaptive
% 13.91/2.50  --res_lit_sel_side                      none
% 13.91/2.50  --res_ordering                          kbo
% 13.91/2.50  --res_to_prop_solver                    active
% 13.91/2.50  --res_prop_simpl_new                    false
% 13.91/2.50  --res_prop_simpl_given                  true
% 13.91/2.50  --res_passive_queue_type                priority_queues
% 13.91/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 13.91/2.50  --res_passive_queues_freq               [15;5]
% 13.91/2.50  --res_forward_subs                      full
% 13.91/2.50  --res_backward_subs                     full
% 13.91/2.50  --res_forward_subs_resolution           true
% 13.91/2.50  --res_backward_subs_resolution          true
% 13.91/2.50  --res_orphan_elimination                true
% 13.91/2.50  --res_time_limit                        2.
% 13.91/2.50  --res_out_proof                         true
% 13.91/2.50  
% 13.91/2.50  ------ Superposition Options
% 13.91/2.50  
% 13.91/2.50  --superposition_flag                    true
% 13.91/2.50  --sup_passive_queue_type                priority_queues
% 13.91/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 13.91/2.50  --sup_passive_queues_freq               [8;1;4]
% 13.91/2.50  --demod_completeness_check              fast
% 13.91/2.50  --demod_use_ground                      true
% 13.91/2.50  --sup_to_prop_solver                    passive
% 13.91/2.50  --sup_prop_simpl_new                    true
% 13.91/2.50  --sup_prop_simpl_given                  true
% 13.91/2.50  --sup_fun_splitting                     true
% 13.91/2.50  --sup_smt_interval                      50000
% 13.91/2.50  
% 13.91/2.50  ------ Superposition Simplification Setup
% 13.91/2.50  
% 13.91/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 13.91/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 13.91/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 13.91/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 13.91/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 13.91/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 13.91/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 13.91/2.50  --sup_immed_triv                        [TrivRules]
% 13.91/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 13.91/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 13.91/2.50  --sup_immed_bw_main                     []
% 13.91/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 13.91/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 13.91/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 13.91/2.50  --sup_input_bw                          []
% 13.91/2.50  
% 13.91/2.50  ------ Combination Options
% 13.91/2.50  
% 13.91/2.50  --comb_res_mult                         3
% 13.91/2.50  --comb_sup_mult                         2
% 13.91/2.50  --comb_inst_mult                        10
% 13.91/2.50  
% 13.91/2.50  ------ Debug Options
% 13.91/2.50  
% 13.91/2.50  --dbg_backtrace                         false
% 13.91/2.50  --dbg_dump_prop_clauses                 false
% 13.91/2.50  --dbg_dump_prop_clauses_file            -
% 13.91/2.50  --dbg_out_stat                          false
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  ------ Proving...
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  % SZS status Theorem for theBenchmark.p
% 13.91/2.50  
% 13.91/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 13.91/2.50  
% 13.91/2.50  fof(f10,axiom,(
% 13.91/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f21,plain,(
% 13.91/2.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 13.91/2.50    inference(ennf_transformation,[],[f10])).
% 13.91/2.50  
% 13.91/2.50  fof(f40,plain,(
% 13.91/2.50    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f21])).
% 13.91/2.50  
% 13.91/2.50  fof(f13,axiom,(
% 13.91/2.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f25,plain,(
% 13.91/2.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 13.91/2.50    inference(ennf_transformation,[],[f13])).
% 13.91/2.50  
% 13.91/2.50  fof(f26,plain,(
% 13.91/2.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 13.91/2.50    inference(flattening,[],[f25])).
% 13.91/2.50  
% 13.91/2.50  fof(f44,plain,(
% 13.91/2.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f26])).
% 13.91/2.50  
% 13.91/2.50  fof(f12,axiom,(
% 13.91/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f24,plain,(
% 13.91/2.50    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 13.91/2.50    inference(ennf_transformation,[],[f12])).
% 13.91/2.50  
% 13.91/2.50  fof(f43,plain,(
% 13.91/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f24])).
% 13.91/2.50  
% 13.91/2.50  fof(f4,axiom,(
% 13.91/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f34,plain,(
% 13.91/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 13.91/2.50    inference(cnf_transformation,[],[f4])).
% 13.91/2.50  
% 13.91/2.50  fof(f52,plain,(
% 13.91/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 13.91/2.50    inference(definition_unfolding,[],[f43,f34])).
% 13.91/2.50  
% 13.91/2.50  fof(f3,axiom,(
% 13.91/2.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f33,plain,(
% 13.91/2.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f3])).
% 13.91/2.50  
% 13.91/2.50  fof(f9,axiom,(
% 13.91/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f19,plain,(
% 13.91/2.50    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 13.91/2.50    inference(ennf_transformation,[],[f9])).
% 13.91/2.50  
% 13.91/2.50  fof(f20,plain,(
% 13.91/2.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 13.91/2.50    inference(flattening,[],[f19])).
% 13.91/2.50  
% 13.91/2.50  fof(f39,plain,(
% 13.91/2.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f20])).
% 13.91/2.50  
% 13.91/2.50  fof(f2,axiom,(
% 13.91/2.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f16,plain,(
% 13.91/2.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 13.91/2.50    inference(ennf_transformation,[],[f2])).
% 13.91/2.50  
% 13.91/2.50  fof(f17,plain,(
% 13.91/2.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 13.91/2.50    inference(flattening,[],[f16])).
% 13.91/2.50  
% 13.91/2.50  fof(f32,plain,(
% 13.91/2.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f17])).
% 13.91/2.50  
% 13.91/2.50  fof(f50,plain,(
% 13.91/2.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 13.91/2.50    inference(definition_unfolding,[],[f32,f34])).
% 13.91/2.50  
% 13.91/2.50  fof(f11,axiom,(
% 13.91/2.50    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f22,plain,(
% 13.91/2.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 13.91/2.50    inference(ennf_transformation,[],[f11])).
% 13.91/2.50  
% 13.91/2.50  fof(f23,plain,(
% 13.91/2.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 13.91/2.50    inference(flattening,[],[f22])).
% 13.91/2.50  
% 13.91/2.50  fof(f42,plain,(
% 13.91/2.50    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f23])).
% 13.91/2.50  
% 13.91/2.50  fof(f8,axiom,(
% 13.91/2.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f18,plain,(
% 13.91/2.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 13.91/2.50    inference(ennf_transformation,[],[f8])).
% 13.91/2.50  
% 13.91/2.50  fof(f38,plain,(
% 13.91/2.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 13.91/2.50    inference(cnf_transformation,[],[f18])).
% 13.91/2.50  
% 13.91/2.50  fof(f14,conjecture,(
% 13.91/2.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 13.91/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.91/2.50  
% 13.91/2.50  fof(f15,negated_conjecture,(
% 13.91/2.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 13.91/2.50    inference(negated_conjecture,[],[f14])).
% 13.91/2.50  
% 13.91/2.50  fof(f27,plain,(
% 13.91/2.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 13.91/2.50    inference(ennf_transformation,[],[f15])).
% 13.91/2.50  
% 13.91/2.50  fof(f28,plain,(
% 13.91/2.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 13.91/2.50    inference(flattening,[],[f27])).
% 13.91/2.50  
% 13.91/2.50  fof(f29,plain,(
% 13.91/2.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 13.91/2.50    introduced(choice_axiom,[])).
% 13.91/2.50  
% 13.91/2.50  fof(f30,plain,(
% 13.91/2.50    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 13.91/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 13.91/2.50  
% 13.91/2.50  fof(f47,plain,(
% 13.91/2.50    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 13.91/2.50    inference(cnf_transformation,[],[f30])).
% 13.91/2.50  
% 13.91/2.50  fof(f53,plain,(
% 13.91/2.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 13.91/2.50    inference(definition_unfolding,[],[f47,f34,f34])).
% 13.91/2.50  
% 13.91/2.50  fof(f46,plain,(
% 13.91/2.50    v1_funct_1(sK2)),
% 13.91/2.50    inference(cnf_transformation,[],[f30])).
% 13.91/2.50  
% 13.91/2.50  fof(f45,plain,(
% 13.91/2.50    v1_relat_1(sK2)),
% 13.91/2.50    inference(cnf_transformation,[],[f30])).
% 13.91/2.50  
% 13.91/2.50  cnf(c_239,plain,
% 13.91/2.50      ( ~ r1_tarski(X0_41,X1_41)
% 13.91/2.50      | r1_tarski(X2_41,X3_41)
% 13.91/2.50      | X2_41 != X0_41
% 13.91/2.50      | X3_41 != X1_41 ),
% 13.91/2.50      theory(equality) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_9047,plain,
% 13.91/2.50      ( r1_tarski(X0_41,X1_41)
% 13.91/2.50      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X2_41)
% 13.91/2.50      | X1_41 != X2_41
% 13.91/2.50      | X0_41 != k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_239]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_41154,plain,
% 13.91/2.50      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
% 13.91/2.50      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1_41)
% 13.91/2.50      | X0_41 != X1_41
% 13.91/2.50      | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_9047]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_41162,plain,
% 13.91/2.50      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
% 13.91/2.50      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
% 13.91/2.50      | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
% 13.91/2.50      | sK0 != sK0 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_41154]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_235,plain,( X0_41 = X0_41 ),theory(equality) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_13805,plain,
% 13.91/2.50      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_235]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_237,plain,
% 13.91/2.50      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 13.91/2.50      theory(equality) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_1058,plain,
% 13.91/2.50      ( X0_41 != X1_41
% 13.91/2.50      | X0_41 = k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
% 13.91/2.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != X1_41 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_237]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_2368,plain,
% 13.91/2.50      ( X0_41 != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 13.91/2.50      | X0_41 = k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
% 13.91/2.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_1058]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_7326,plain,
% 13.91/2.50      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 13.91/2.50      | k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))
% 13.91/2.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_2368]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_6,plain,
% 13.91/2.50      ( ~ r1_tarski(X0,X1)
% 13.91/2.50      | ~ v1_relat_1(X2)
% 13.91/2.50      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 13.91/2.50      inference(cnf_transformation,[],[f40]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_226,plain,
% 13.91/2.50      ( ~ r1_tarski(X0_41,X1_41)
% 13.91/2.50      | ~ v1_relat_1(X0_40)
% 13.91/2.50      | k9_relat_1(k7_relat_1(X0_40,X1_41),X0_41) = k9_relat_1(X0_40,X0_41) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_6]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_3592,plain,
% 13.91/2.50      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
% 13.91/2.50      | ~ v1_relat_1(X0_40)
% 13.91/2.50      | k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_226]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_3594,plain,
% 13.91/2.50      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
% 13.91/2.50      | ~ v1_relat_1(sK2)
% 13.91/2.50      | k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_3592]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_10,plain,
% 13.91/2.50      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 13.91/2.50      | ~ v1_funct_1(X0)
% 13.91/2.50      | ~ v1_relat_1(X0) ),
% 13.91/2.50      inference(cnf_transformation,[],[f44]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_223,plain,
% 13.91/2.50      ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41)
% 13.91/2.50      | ~ v1_funct_1(X0_40)
% 13.91/2.50      | ~ v1_relat_1(X0_40) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_10]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_786,plain,
% 13.91/2.50      ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
% 13.91/2.50      | ~ v1_funct_1(X0_40)
% 13.91/2.50      | ~ v1_relat_1(X0_40) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_223]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_3018,plain,
% 13.91/2.50      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
% 13.91/2.50      | ~ v1_funct_1(k7_relat_1(sK2,sK0))
% 13.91/2.50      | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_786]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_503,plain,
% 13.91/2.50      ( X0_41 != X1_41
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X1_41
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = X0_41 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_237]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_524,plain,
% 13.91/2.50      ( X0_41 != k9_relat_1(X0_40,X1_41)
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = X0_41
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,X1_41) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_503]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_1910,plain,
% 13.91/2.50      ( X0_41 != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = X0_41
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_524]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_2973,plain,
% 13.91/2.50      ( k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_1910]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_2974,plain,
% 13.91/2.50      ( k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_2973]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_493,plain,
% 13.91/2.50      ( ~ r1_tarski(X0_41,X1_41)
% 13.91/2.50      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_41
% 13.91/2.50      | sK1 != X1_41 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_239]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_515,plain,
% 13.91/2.50      ( ~ r1_tarski(X0_41,sK1)
% 13.91/2.50      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_41
% 13.91/2.50      | sK1 != sK1 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_493]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_629,plain,
% 13.91/2.50      ( ~ r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
% 13.91/2.50      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(X0_40,k10_relat_1(X0_40,sK1))
% 13.91/2.50      | sK1 != sK1 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_515]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_1914,plain,
% 13.91/2.50      ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
% 13.91/2.50      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
% 13.91/2.50      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | sK1 != sK1 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_629]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_9,plain,
% 13.91/2.50      ( ~ v1_relat_1(X0)
% 13.91/2.50      | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 13.91/2.50      inference(cnf_transformation,[],[f52]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_224,plain,
% 13.91/2.50      ( ~ v1_relat_1(X0_40)
% 13.91/2.50      | k4_xboole_0(X0_41,k4_xboole_0(X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_9]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_960,plain,
% 13.91/2.50      ( ~ v1_relat_1(sK2)
% 13.91/2.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_224]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_2,plain,
% 13.91/2.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 13.91/2.50      inference(cnf_transformation,[],[f33]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_230,plain,
% 13.91/2.50      ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_2]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_899,plain,
% 13.91/2.50      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_230]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_242,plain,
% 13.91/2.50      ( X0_41 != X1_41
% 13.91/2.50      | k9_relat_1(X0_40,X0_41) = k9_relat_1(X1_40,X1_41)
% 13.91/2.50      | X0_40 != X1_40 ),
% 13.91/2.50      theory(equality) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_601,plain,
% 13.91/2.50      ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0_40,X0_41)
% 13.91/2.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != X0_41
% 13.91/2.50      | sK2 != X0_40 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_242]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_765,plain,
% 13.91/2.50      ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 13.91/2.50      | sK2 != X0_40 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_601]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_766,plain,
% 13.91/2.50      ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 13.91/2.50      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 13.91/2.50      | sK2 != sK2 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_765]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_5,plain,
% 13.91/2.50      ( ~ r1_tarski(X0,X1)
% 13.91/2.50      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 13.91/2.50      | ~ v1_relat_1(X2) ),
% 13.91/2.50      inference(cnf_transformation,[],[f39]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_227,plain,
% 13.91/2.50      ( ~ r1_tarski(X0_41,X1_41)
% 13.91/2.50      | r1_tarski(k9_relat_1(X0_40,X0_41),k9_relat_1(X0_40,X1_41))
% 13.91/2.50      | ~ v1_relat_1(X0_40) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_5]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_574,plain,
% 13.91/2.50      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,X0_41))
% 13.91/2.50      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0_41)
% 13.91/2.50      | ~ v1_relat_1(sK2) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_227]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_576,plain,
% 13.91/2.50      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 13.91/2.50      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
% 13.91/2.50      | ~ v1_relat_1(sK2) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_574]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_564,plain,
% 13.91/2.50      ( sK1 = sK1 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_235]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_1,plain,
% 13.91/2.50      ( ~ r1_tarski(X0,X1)
% 13.91/2.50      | ~ r1_tarski(X0,X2)
% 13.91/2.50      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 13.91/2.50      inference(cnf_transformation,[],[f50]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_231,plain,
% 13.91/2.50      ( ~ r1_tarski(X0_41,X1_41)
% 13.91/2.50      | ~ r1_tarski(X0_41,X2_41)
% 13.91/2.50      | r1_tarski(X0_41,k4_xboole_0(X2_41,k4_xboole_0(X2_41,X1_41))) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_1]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_485,plain,
% 13.91/2.50      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 13.91/2.50      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))
% 13.91/2.50      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_231]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_7,plain,
% 13.91/2.50      ( ~ v1_funct_1(X0)
% 13.91/2.50      | v1_funct_1(k7_relat_1(X0,X1))
% 13.91/2.50      | ~ v1_relat_1(X0) ),
% 13.91/2.50      inference(cnf_transformation,[],[f42]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_225,plain,
% 13.91/2.50      ( ~ v1_funct_1(X0_40)
% 13.91/2.50      | v1_funct_1(k7_relat_1(X0_40,X0_41))
% 13.91/2.50      | ~ v1_relat_1(X0_40) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_7]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_274,plain,
% 13.91/2.50      ( v1_funct_1(k7_relat_1(sK2,sK0))
% 13.91/2.50      | ~ v1_funct_1(sK2)
% 13.91/2.50      | ~ v1_relat_1(sK2) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_225]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_4,plain,
% 13.91/2.50      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 13.91/2.50      inference(cnf_transformation,[],[f38]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_228,plain,
% 13.91/2.50      ( ~ v1_relat_1(X0_40) | v1_relat_1(k7_relat_1(X0_40,X0_41)) ),
% 13.91/2.50      inference(subtyping,[status(esa)],[c_4]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_265,plain,
% 13.91/2.50      ( v1_relat_1(k7_relat_1(sK2,sK0)) | ~ v1_relat_1(sK2) ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_228]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_254,plain,
% 13.91/2.50      ( sK0 = sK0 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_235]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_234,plain,( X0_40 = X0_40 ),theory(equality) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_253,plain,
% 13.91/2.50      ( sK2 = sK2 ),
% 13.91/2.50      inference(instantiation,[status(thm)],[c_234]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_11,negated_conjecture,
% 13.91/2.50      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
% 13.91/2.50      inference(cnf_transformation,[],[f53]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_12,negated_conjecture,
% 13.91/2.50      ( v1_funct_1(sK2) ),
% 13.91/2.50      inference(cnf_transformation,[],[f46]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(c_13,negated_conjecture,
% 13.91/2.50      ( v1_relat_1(sK2) ),
% 13.91/2.50      inference(cnf_transformation,[],[f45]) ).
% 13.91/2.50  
% 13.91/2.50  cnf(contradiction,plain,
% 13.91/2.50      ( $false ),
% 13.91/2.50      inference(minisat,
% 13.91/2.50                [status(thm)],
% 13.91/2.50                [c_41162,c_13805,c_7326,c_3594,c_3018,c_2974,c_1914,
% 13.91/2.50                 c_960,c_899,c_766,c_576,c_564,c_485,c_274,c_265,c_254,
% 13.91/2.50                 c_253,c_11,c_12,c_13]) ).
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 13.91/2.50  
% 13.91/2.50  ------                               Statistics
% 13.91/2.50  
% 13.91/2.50  ------ General
% 13.91/2.50  
% 13.91/2.50  abstr_ref_over_cycles:                  0
% 13.91/2.50  abstr_ref_under_cycles:                 0
% 13.91/2.50  gc_basic_clause_elim:                   0
% 13.91/2.50  forced_gc_time:                         0
% 13.91/2.50  parsing_time:                           0.02
% 13.91/2.50  unif_index_cands_time:                  0.
% 13.91/2.50  unif_index_add_time:                    0.
% 13.91/2.50  orderings_time:                         0.
% 13.91/2.50  out_proof_time:                         0.01
% 13.91/2.50  total_time:                             1.707
% 13.91/2.50  num_of_symbols:                         46
% 13.91/2.50  num_of_terms:                           64266
% 13.91/2.50  
% 13.91/2.50  ------ Preprocessing
% 13.91/2.50  
% 13.91/2.50  num_of_splits:                          0
% 13.91/2.50  num_of_split_atoms:                     0
% 13.91/2.50  num_of_reused_defs:                     0
% 13.91/2.50  num_eq_ax_congr_red:                    18
% 13.91/2.50  num_of_sem_filtered_clauses:            1
% 13.91/2.50  num_of_subtypes:                        3
% 13.91/2.50  monotx_restored_types:                  0
% 13.91/2.50  sat_num_of_epr_types:                   0
% 13.91/2.50  sat_num_of_non_cyclic_types:            0
% 13.91/2.50  sat_guarded_non_collapsed_types:        0
% 13.91/2.50  num_pure_diseq_elim:                    0
% 13.91/2.50  simp_replaced_by:                       0
% 13.91/2.50  res_preprocessed:                       75
% 13.91/2.50  prep_upred:                             0
% 13.91/2.50  prep_unflattend:                        0
% 13.91/2.50  smt_new_axioms:                         0
% 13.91/2.50  pred_elim_cands:                        3
% 13.91/2.50  pred_elim:                              0
% 13.91/2.50  pred_elim_cl:                           0
% 13.91/2.50  pred_elim_cycles:                       2
% 13.91/2.50  merged_defs:                            0
% 13.91/2.50  merged_defs_ncl:                        0
% 13.91/2.50  bin_hyper_res:                          0
% 13.91/2.50  prep_cycles:                            4
% 13.91/2.50  pred_elim_time:                         0.
% 13.91/2.50  splitting_time:                         0.
% 13.91/2.50  sem_filter_time:                        0.
% 13.91/2.50  monotx_time:                            0.
% 13.91/2.50  subtype_inf_time:                       0.
% 13.91/2.50  
% 13.91/2.50  ------ Problem properties
% 13.91/2.50  
% 13.91/2.50  clauses:                                13
% 13.91/2.50  conjectures:                            3
% 13.91/2.50  epr:                                    2
% 13.91/2.50  horn:                                   13
% 13.91/2.50  ground:                                 3
% 13.91/2.50  unary:                                  6
% 13.91/2.50  binary:                                 2
% 13.91/2.50  lits:                                   25
% 13.91/2.50  lits_eq:                                4
% 13.91/2.50  fd_pure:                                0
% 13.91/2.50  fd_pseudo:                              0
% 13.91/2.50  fd_cond:                                0
% 13.91/2.50  fd_pseudo_cond:                         0
% 13.91/2.50  ac_symbols:                             0
% 13.91/2.50  
% 13.91/2.50  ------ Propositional Solver
% 13.91/2.50  
% 13.91/2.50  prop_solver_calls:                      36
% 13.91/2.50  prop_fast_solver_calls:                 595
% 13.91/2.50  smt_solver_calls:                       0
% 13.91/2.50  smt_fast_solver_calls:                  0
% 13.91/2.50  prop_num_of_clauses:                    14685
% 13.91/2.50  prop_preprocess_simplified:             14335
% 13.91/2.50  prop_fo_subsumed:                       3
% 13.91/2.50  prop_solver_time:                       0.
% 13.91/2.50  smt_solver_time:                        0.
% 13.91/2.50  smt_fast_solver_time:                   0.
% 13.91/2.50  prop_fast_solver_time:                  0.
% 13.91/2.50  prop_unsat_core_time:                   0.001
% 13.91/2.50  
% 13.91/2.50  ------ QBF
% 13.91/2.50  
% 13.91/2.50  qbf_q_res:                              0
% 13.91/2.50  qbf_num_tautologies:                    0
% 13.91/2.50  qbf_prep_cycles:                        0
% 13.91/2.50  
% 13.91/2.50  ------ BMC1
% 13.91/2.50  
% 13.91/2.50  bmc1_current_bound:                     -1
% 13.91/2.50  bmc1_last_solved_bound:                 -1
% 13.91/2.50  bmc1_unsat_core_size:                   -1
% 13.91/2.50  bmc1_unsat_core_parents_size:           -1
% 13.91/2.50  bmc1_merge_next_fun:                    0
% 13.91/2.50  bmc1_unsat_core_clauses_time:           0.
% 13.91/2.50  
% 13.91/2.50  ------ Instantiation
% 13.91/2.50  
% 13.91/2.50  inst_num_of_clauses:                    2094
% 13.91/2.50  inst_num_in_passive:                    573
% 13.91/2.50  inst_num_in_active:                     957
% 13.91/2.50  inst_num_in_unprocessed:                563
% 13.91/2.50  inst_num_of_loops:                      1005
% 13.91/2.50  inst_num_of_learning_restarts:          0
% 13.91/2.50  inst_num_moves_active_passive:          41
% 13.91/2.50  inst_lit_activity:                      0
% 13.91/2.50  inst_lit_activity_moves:                0
% 13.91/2.50  inst_num_tautologies:                   0
% 13.91/2.50  inst_num_prop_implied:                  0
% 13.91/2.50  inst_num_existing_simplified:           0
% 13.91/2.50  inst_num_eq_res_simplified:             0
% 13.91/2.50  inst_num_child_elim:                    0
% 13.91/2.50  inst_num_of_dismatching_blockings:      2396
% 13.91/2.50  inst_num_of_non_proper_insts:           3480
% 13.91/2.50  inst_num_of_duplicates:                 0
% 13.91/2.50  inst_inst_num_from_inst_to_res:         0
% 13.91/2.50  inst_dismatching_checking_time:         0.
% 13.91/2.50  
% 13.91/2.50  ------ Resolution
% 13.91/2.50  
% 13.91/2.50  res_num_of_clauses:                     0
% 13.91/2.50  res_num_in_passive:                     0
% 13.91/2.50  res_num_in_active:                      0
% 13.91/2.50  res_num_of_loops:                       79
% 13.91/2.50  res_forward_subset_subsumed:            520
% 13.91/2.50  res_backward_subset_subsumed:           0
% 13.91/2.50  res_forward_subsumed:                   0
% 13.91/2.50  res_backward_subsumed:                  0
% 13.91/2.50  res_forward_subsumption_resolution:     0
% 13.91/2.50  res_backward_subsumption_resolution:    0
% 13.91/2.50  res_clause_to_clause_subsumption:       46497
% 13.91/2.50  res_orphan_elimination:                 0
% 13.91/2.50  res_tautology_del:                      381
% 13.91/2.50  res_num_eq_res_simplified:              0
% 13.91/2.50  res_num_sel_changes:                    0
% 13.91/2.50  res_moves_from_active_to_pass:          0
% 13.91/2.50  
% 13.91/2.50  ------ Superposition
% 13.91/2.50  
% 13.91/2.50  sup_time_total:                         0.
% 13.91/2.50  sup_time_generating:                    0.
% 13.91/2.50  sup_time_sim_full:                      0.
% 13.91/2.50  sup_time_sim_immed:                     0.
% 13.91/2.50  
% 13.91/2.50  sup_num_of_clauses:                     2502
% 13.91/2.50  sup_num_in_active:                      193
% 13.91/2.50  sup_num_in_passive:                     2309
% 13.91/2.50  sup_num_of_loops:                       200
% 13.91/2.50  sup_fw_superposition:                   8626
% 13.91/2.50  sup_bw_superposition:                   1370
% 13.91/2.50  sup_immediate_simplified:               3068
% 13.91/2.50  sup_given_eliminated:                   0
% 13.91/2.50  comparisons_done:                       0
% 13.91/2.50  comparisons_avoided:                    0
% 13.91/2.50  
% 13.91/2.50  ------ Simplifications
% 13.91/2.50  
% 13.91/2.50  
% 13.91/2.50  sim_fw_subset_subsumed:                 0
% 13.91/2.50  sim_bw_subset_subsumed:                 0
% 13.91/2.50  sim_fw_subsumed:                        1359
% 13.91/2.50  sim_bw_subsumed:                        7
% 13.91/2.50  sim_fw_subsumption_res:                 0
% 13.91/2.50  sim_bw_subsumption_res:                 0
% 13.91/2.50  sim_tautology_del:                      0
% 13.91/2.50  sim_eq_tautology_del:                   6
% 13.91/2.50  sim_eq_res_simp:                        0
% 13.91/2.50  sim_fw_demodulated:                     7035
% 13.91/2.50  sim_bw_demodulated:                     44
% 13.91/2.50  sim_light_normalised:                   1676
% 13.91/2.50  sim_joinable_taut:                      0
% 13.91/2.50  sim_joinable_simp:                      0
% 13.91/2.50  sim_ac_normalised:                      0
% 13.91/2.50  sim_smt_subsumption:                    0
% 13.91/2.50  
%------------------------------------------------------------------------------
