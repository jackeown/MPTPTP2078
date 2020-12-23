%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:50 EST 2020

% Result     : Timeout 59.57s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  110 ( 160 expanded)
%              Number of clauses        :   65 (  72 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  264 ( 436 expanded)
%              Number of equality atoms :  101 ( 133 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).

fof(f51,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f52,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_197987,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))),k10_relat_1(X1,k2_relat_1(k7_relat_1(X0,sK0))))
    | ~ r1_tarski(k7_relat_1(X0,sK0),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k7_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_197990,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))
    | ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_197987])).

cnf(c_327,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1524,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k10_relat_1(X3,k9_relat_1(sK1,sK0)))
    | X2 != X0
    | k10_relat_1(X3,k9_relat_1(sK1,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_2833,plain,
    ( ~ r1_tarski(X0,k10_relat_1(X1,X2))
    | r1_tarski(X3,k10_relat_1(X4,k9_relat_1(sK1,sK0)))
    | X3 != X0
    | k10_relat_1(X4,k9_relat_1(sK1,sK0)) != k10_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_10751,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(sK1,sK0)))
    | ~ r1_tarski(k10_relat_1(X2,X3),k10_relat_1(X4,X3))
    | X0 != k10_relat_1(X2,X3)
    | k10_relat_1(X1,k9_relat_1(sK1,sK0)) != k10_relat_1(X4,X3) ),
    inference(instantiation,[status(thm)],[c_2833])).

cnf(c_45039,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))),k10_relat_1(X1,k2_relat_1(k7_relat_1(X0,sK0))))
    | r1_tarski(sK0,k10_relat_1(X2,k9_relat_1(sK1,sK0)))
    | k10_relat_1(X2,k9_relat_1(sK1,sK0)) != k10_relat_1(X1,k2_relat_1(k7_relat_1(X0,sK0)))
    | sK0 != k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))) ),
    inference(instantiation,[status(thm)],[c_10751])).

cnf(c_45046,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))
    | sK0 != k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_45039])).

cnf(c_13,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_40626,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_332,plain,
    ( X0 != X1
    | X2 != X3
    | k10_relat_1(X0,X2) = k10_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_961,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(X0,X1)
    | k9_relat_1(sK1,sK0) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_19604,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(X0,k2_relat_1(k7_relat_1(sK1,sK0)))
    | k9_relat_1(sK1,sK0) != k2_relat_1(k7_relat_1(sK1,sK0))
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_19605,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))
    | k9_relat_1(sK1,sK0) != k2_relat_1(k7_relat_1(sK1,sK0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_19604])).

cnf(c_326,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_661,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_6989,plain,
    ( X0 != k1_relat_1(k7_relat_1(X1,sK0))
    | sK0 = X0
    | sK0 != k1_relat_1(k7_relat_1(X1,sK0)) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_13117,plain,
    ( k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))) != k1_relat_1(k7_relat_1(X0,sK0))
    | sK0 = k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0)))
    | sK0 != k1_relat_1(k7_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_6989])).

cnf(c_13118,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k7_relat_1(sK1,sK0))
    | sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))
    | sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_13117])).

cnf(c_1355,plain,
    ( X0 != X1
    | k9_relat_1(sK1,sK0) != X1
    | k9_relat_1(sK1,sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_2327,plain,
    ( X0 != k9_relat_1(sK1,sK0)
    | k9_relat_1(sK1,sK0) = X0
    | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1355])).

cnf(c_7120,plain,
    ( k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0)
    | k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_2327])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5655,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5657,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5655])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5309,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3544,plain,
    ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2366,plain,
    ( ~ v1_relat_1(k7_relat_1(X0,sK0))
    | k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))) = k1_relat_1(k7_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2368,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1348,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
    | ~ r1_tarski(k9_relat_1(sK1,sK0),X0)
    | k9_relat_1(sK1,sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2285,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | k9_relat_1(sK1,sK0) = k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_610,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_622,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_966,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_610,c_622])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_609,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_616,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1188,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_609,c_616])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_612,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1076,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_609,c_612])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_617,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1456,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_617])).

cnf(c_1461,plain,
    ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1456])).

cnf(c_1594,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_1461])).

cnf(c_1596,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1594])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_749,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_751,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_651,plain,
    ( ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,X0)
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_684,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(X0,sK0)))
    | sK0 = k1_relat_1(k7_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_686,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_60,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_56,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_197990,c_45046,c_40626,c_19605,c_13118,c_7120,c_5657,c_5309,c_3544,c_2368,c_2285,c_1596,c_751,c_686,c_60,c_56,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 59.57/8.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.57/8.01  
% 59.57/8.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.57/8.01  
% 59.57/8.01  ------  iProver source info
% 59.57/8.01  
% 59.57/8.01  git: date: 2020-06-30 10:37:57 +0100
% 59.57/8.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.57/8.01  git: non_committed_changes: false
% 59.57/8.01  git: last_make_outside_of_git: false
% 59.57/8.01  
% 59.57/8.01  ------ 
% 59.57/8.01  
% 59.57/8.01  ------ Input Options
% 59.57/8.01  
% 59.57/8.01  --out_options                           all
% 59.57/8.01  --tptp_safe_out                         true
% 59.57/8.01  --problem_path                          ""
% 59.57/8.01  --include_path                          ""
% 59.57/8.01  --clausifier                            res/vclausify_rel
% 59.57/8.01  --clausifier_options                    ""
% 59.57/8.01  --stdin                                 false
% 59.57/8.01  --stats_out                             all
% 59.57/8.01  
% 59.57/8.01  ------ General Options
% 59.57/8.01  
% 59.57/8.01  --fof                                   false
% 59.57/8.01  --time_out_real                         305.
% 59.57/8.01  --time_out_virtual                      -1.
% 59.57/8.01  --symbol_type_check                     false
% 59.57/8.01  --clausify_out                          false
% 59.57/8.01  --sig_cnt_out                           false
% 59.57/8.01  --trig_cnt_out                          false
% 59.57/8.01  --trig_cnt_out_tolerance                1.
% 59.57/8.01  --trig_cnt_out_sk_spl                   false
% 59.57/8.01  --abstr_cl_out                          false
% 59.57/8.01  
% 59.57/8.01  ------ Global Options
% 59.57/8.01  
% 59.57/8.01  --schedule                              default
% 59.57/8.01  --add_important_lit                     false
% 59.57/8.01  --prop_solver_per_cl                    1000
% 59.57/8.01  --min_unsat_core                        false
% 59.57/8.01  --soft_assumptions                      false
% 59.57/8.01  --soft_lemma_size                       3
% 59.57/8.01  --prop_impl_unit_size                   0
% 59.57/8.01  --prop_impl_unit                        []
% 59.57/8.01  --share_sel_clauses                     true
% 59.57/8.01  --reset_solvers                         false
% 59.57/8.01  --bc_imp_inh                            [conj_cone]
% 59.57/8.01  --conj_cone_tolerance                   3.
% 59.57/8.01  --extra_neg_conj                        none
% 59.57/8.01  --large_theory_mode                     true
% 59.57/8.01  --prolific_symb_bound                   200
% 59.57/8.01  --lt_threshold                          2000
% 59.57/8.01  --clause_weak_htbl                      true
% 59.57/8.01  --gc_record_bc_elim                     false
% 59.57/8.01  
% 59.57/8.01  ------ Preprocessing Options
% 59.57/8.01  
% 59.57/8.01  --preprocessing_flag                    true
% 59.57/8.01  --time_out_prep_mult                    0.1
% 59.57/8.01  --splitting_mode                        input
% 59.57/8.01  --splitting_grd                         true
% 59.57/8.01  --splitting_cvd                         false
% 59.57/8.01  --splitting_cvd_svl                     false
% 59.57/8.01  --splitting_nvd                         32
% 59.57/8.01  --sub_typing                            true
% 59.57/8.01  --prep_gs_sim                           true
% 59.57/8.01  --prep_unflatten                        true
% 59.57/8.01  --prep_res_sim                          true
% 59.57/8.01  --prep_upred                            true
% 59.57/8.01  --prep_sem_filter                       exhaustive
% 59.57/8.01  --prep_sem_filter_out                   false
% 59.57/8.01  --pred_elim                             true
% 59.57/8.01  --res_sim_input                         true
% 59.57/8.01  --eq_ax_congr_red                       true
% 59.57/8.01  --pure_diseq_elim                       true
% 59.57/8.01  --brand_transform                       false
% 59.57/8.01  --non_eq_to_eq                          false
% 59.57/8.01  --prep_def_merge                        true
% 59.57/8.01  --prep_def_merge_prop_impl              false
% 59.57/8.01  --prep_def_merge_mbd                    true
% 59.57/8.01  --prep_def_merge_tr_red                 false
% 59.57/8.01  --prep_def_merge_tr_cl                  false
% 59.57/8.01  --smt_preprocessing                     true
% 59.57/8.01  --smt_ac_axioms                         fast
% 59.57/8.01  --preprocessed_out                      false
% 59.57/8.01  --preprocessed_stats                    false
% 59.57/8.01  
% 59.57/8.01  ------ Abstraction refinement Options
% 59.57/8.01  
% 59.57/8.01  --abstr_ref                             []
% 59.57/8.01  --abstr_ref_prep                        false
% 59.57/8.01  --abstr_ref_until_sat                   false
% 59.57/8.01  --abstr_ref_sig_restrict                funpre
% 59.57/8.01  --abstr_ref_af_restrict_to_split_sk     false
% 59.57/8.01  --abstr_ref_under                       []
% 59.57/8.01  
% 59.57/8.01  ------ SAT Options
% 59.57/8.01  
% 59.57/8.01  --sat_mode                              false
% 59.57/8.01  --sat_fm_restart_options                ""
% 59.57/8.01  --sat_gr_def                            false
% 59.57/8.01  --sat_epr_types                         true
% 59.57/8.01  --sat_non_cyclic_types                  false
% 59.57/8.01  --sat_finite_models                     false
% 59.57/8.01  --sat_fm_lemmas                         false
% 59.57/8.01  --sat_fm_prep                           false
% 59.57/8.01  --sat_fm_uc_incr                        true
% 59.57/8.01  --sat_out_model                         small
% 59.57/8.01  --sat_out_clauses                       false
% 59.57/8.01  
% 59.57/8.01  ------ QBF Options
% 59.57/8.01  
% 59.57/8.01  --qbf_mode                              false
% 59.57/8.01  --qbf_elim_univ                         false
% 59.57/8.01  --qbf_dom_inst                          none
% 59.57/8.01  --qbf_dom_pre_inst                      false
% 59.57/8.01  --qbf_sk_in                             false
% 59.57/8.01  --qbf_pred_elim                         true
% 59.57/8.01  --qbf_split                             512
% 59.57/8.01  
% 59.57/8.01  ------ BMC1 Options
% 59.57/8.01  
% 59.57/8.01  --bmc1_incremental                      false
% 59.57/8.01  --bmc1_axioms                           reachable_all
% 59.57/8.01  --bmc1_min_bound                        0
% 59.57/8.01  --bmc1_max_bound                        -1
% 59.57/8.01  --bmc1_max_bound_default                -1
% 59.57/8.01  --bmc1_symbol_reachability              true
% 59.57/8.01  --bmc1_property_lemmas                  false
% 59.57/8.01  --bmc1_k_induction                      false
% 59.57/8.01  --bmc1_non_equiv_states                 false
% 59.57/8.01  --bmc1_deadlock                         false
% 59.57/8.01  --bmc1_ucm                              false
% 59.57/8.01  --bmc1_add_unsat_core                   none
% 59.57/8.01  --bmc1_unsat_core_children              false
% 59.57/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.57/8.01  --bmc1_out_stat                         full
% 59.57/8.01  --bmc1_ground_init                      false
% 59.57/8.01  --bmc1_pre_inst_next_state              false
% 59.57/8.01  --bmc1_pre_inst_state                   false
% 59.57/8.01  --bmc1_pre_inst_reach_state             false
% 59.57/8.01  --bmc1_out_unsat_core                   false
% 59.57/8.01  --bmc1_aig_witness_out                  false
% 59.57/8.01  --bmc1_verbose                          false
% 59.57/8.01  --bmc1_dump_clauses_tptp                false
% 59.57/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.57/8.01  --bmc1_dump_file                        -
% 59.57/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.57/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.57/8.01  --bmc1_ucm_extend_mode                  1
% 59.57/8.01  --bmc1_ucm_init_mode                    2
% 59.57/8.01  --bmc1_ucm_cone_mode                    none
% 59.57/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.57/8.01  --bmc1_ucm_relax_model                  4
% 59.57/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.57/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.57/8.01  --bmc1_ucm_layered_model                none
% 59.57/8.01  --bmc1_ucm_max_lemma_size               10
% 59.57/8.01  
% 59.57/8.01  ------ AIG Options
% 59.57/8.01  
% 59.57/8.01  --aig_mode                              false
% 59.57/8.01  
% 59.57/8.01  ------ Instantiation Options
% 59.57/8.01  
% 59.57/8.01  --instantiation_flag                    true
% 59.57/8.01  --inst_sos_flag                         true
% 59.57/8.01  --inst_sos_phase                        true
% 59.57/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.57/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.57/8.01  --inst_lit_sel_side                     num_symb
% 59.57/8.01  --inst_solver_per_active                1400
% 59.57/8.01  --inst_solver_calls_frac                1.
% 59.57/8.01  --inst_passive_queue_type               priority_queues
% 59.57/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.57/8.01  --inst_passive_queues_freq              [25;2]
% 59.57/8.01  --inst_dismatching                      true
% 59.57/8.01  --inst_eager_unprocessed_to_passive     true
% 59.57/8.01  --inst_prop_sim_given                   true
% 59.57/8.01  --inst_prop_sim_new                     false
% 59.57/8.01  --inst_subs_new                         false
% 59.57/8.01  --inst_eq_res_simp                      false
% 59.57/8.01  --inst_subs_given                       false
% 59.57/8.01  --inst_orphan_elimination               true
% 59.57/8.01  --inst_learning_loop_flag               true
% 59.57/8.01  --inst_learning_start                   3000
% 59.57/8.01  --inst_learning_factor                  2
% 59.57/8.01  --inst_start_prop_sim_after_learn       3
% 59.57/8.01  --inst_sel_renew                        solver
% 59.57/8.01  --inst_lit_activity_flag                true
% 59.57/8.01  --inst_restr_to_given                   false
% 59.57/8.01  --inst_activity_threshold               500
% 59.57/8.01  --inst_out_proof                        true
% 59.57/8.01  
% 59.57/8.01  ------ Resolution Options
% 59.57/8.01  
% 59.57/8.01  --resolution_flag                       true
% 59.57/8.01  --res_lit_sel                           adaptive
% 59.57/8.01  --res_lit_sel_side                      none
% 59.57/8.01  --res_ordering                          kbo
% 59.57/8.01  --res_to_prop_solver                    active
% 59.57/8.01  --res_prop_simpl_new                    false
% 59.57/8.01  --res_prop_simpl_given                  true
% 59.57/8.01  --res_passive_queue_type                priority_queues
% 59.57/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.57/8.01  --res_passive_queues_freq               [15;5]
% 59.57/8.01  --res_forward_subs                      full
% 59.57/8.01  --res_backward_subs                     full
% 59.57/8.01  --res_forward_subs_resolution           true
% 59.57/8.01  --res_backward_subs_resolution          true
% 59.57/8.01  --res_orphan_elimination                true
% 59.57/8.01  --res_time_limit                        2.
% 59.57/8.01  --res_out_proof                         true
% 59.57/8.01  
% 59.57/8.01  ------ Superposition Options
% 59.57/8.01  
% 59.57/8.01  --superposition_flag                    true
% 59.57/8.01  --sup_passive_queue_type                priority_queues
% 59.57/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.57/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.57/8.01  --demod_completeness_check              fast
% 59.57/8.01  --demod_use_ground                      true
% 59.57/8.01  --sup_to_prop_solver                    passive
% 59.57/8.01  --sup_prop_simpl_new                    true
% 59.57/8.01  --sup_prop_simpl_given                  true
% 59.57/8.01  --sup_fun_splitting                     true
% 59.57/8.01  --sup_smt_interval                      50000
% 59.57/8.01  
% 59.57/8.01  ------ Superposition Simplification Setup
% 59.57/8.01  
% 59.57/8.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.57/8.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.57/8.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.57/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.57/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.57/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.57/8.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.57/8.01  --sup_immed_triv                        [TrivRules]
% 59.57/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.57/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.57/8.01  --sup_immed_bw_main                     []
% 59.57/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.57/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.57/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.57/8.01  --sup_input_bw                          []
% 59.57/8.01  
% 59.57/8.01  ------ Combination Options
% 59.57/8.01  
% 59.57/8.01  --comb_res_mult                         3
% 59.57/8.01  --comb_sup_mult                         2
% 59.57/8.01  --comb_inst_mult                        10
% 59.57/8.01  
% 59.57/8.01  ------ Debug Options
% 59.57/8.01  
% 59.57/8.01  --dbg_backtrace                         false
% 59.57/8.01  --dbg_dump_prop_clauses                 false
% 59.57/8.01  --dbg_dump_prop_clauses_file            -
% 59.57/8.01  --dbg_out_stat                          false
% 59.57/8.01  ------ Parsing...
% 59.57/8.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.57/8.01  
% 59.57/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.57/8.01  
% 59.57/8.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.57/8.01  
% 59.57/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.57/8.01  ------ Proving...
% 59.57/8.01  ------ Problem Properties 
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  clauses                                 17
% 59.57/8.01  conjectures                             3
% 59.57/8.01  EPR                                     3
% 59.57/8.01  Horn                                    17
% 59.57/8.01  unary                                   5
% 59.57/8.01  binary                                  9
% 59.57/8.01  lits                                    33
% 59.57/8.01  lits eq                                 5
% 59.57/8.01  fd_pure                                 0
% 59.57/8.01  fd_pseudo                               0
% 59.57/8.01  fd_cond                                 0
% 59.57/8.01  fd_pseudo_cond                          1
% 59.57/8.01  AC symbols                              0
% 59.57/8.01  
% 59.57/8.01  ------ Schedule dynamic 5 is on 
% 59.57/8.01  
% 59.57/8.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  ------ 
% 59.57/8.01  Current options:
% 59.57/8.01  ------ 
% 59.57/8.01  
% 59.57/8.01  ------ Input Options
% 59.57/8.01  
% 59.57/8.01  --out_options                           all
% 59.57/8.01  --tptp_safe_out                         true
% 59.57/8.01  --problem_path                          ""
% 59.57/8.01  --include_path                          ""
% 59.57/8.01  --clausifier                            res/vclausify_rel
% 59.57/8.01  --clausifier_options                    ""
% 59.57/8.01  --stdin                                 false
% 59.57/8.01  --stats_out                             all
% 59.57/8.01  
% 59.57/8.01  ------ General Options
% 59.57/8.01  
% 59.57/8.01  --fof                                   false
% 59.57/8.01  --time_out_real                         305.
% 59.57/8.01  --time_out_virtual                      -1.
% 59.57/8.01  --symbol_type_check                     false
% 59.57/8.01  --clausify_out                          false
% 59.57/8.01  --sig_cnt_out                           false
% 59.57/8.01  --trig_cnt_out                          false
% 59.57/8.01  --trig_cnt_out_tolerance                1.
% 59.57/8.01  --trig_cnt_out_sk_spl                   false
% 59.57/8.01  --abstr_cl_out                          false
% 59.57/8.01  
% 59.57/8.01  ------ Global Options
% 59.57/8.01  
% 59.57/8.01  --schedule                              default
% 59.57/8.01  --add_important_lit                     false
% 59.57/8.01  --prop_solver_per_cl                    1000
% 59.57/8.01  --min_unsat_core                        false
% 59.57/8.01  --soft_assumptions                      false
% 59.57/8.01  --soft_lemma_size                       3
% 59.57/8.01  --prop_impl_unit_size                   0
% 59.57/8.01  --prop_impl_unit                        []
% 59.57/8.01  --share_sel_clauses                     true
% 59.57/8.01  --reset_solvers                         false
% 59.57/8.01  --bc_imp_inh                            [conj_cone]
% 59.57/8.01  --conj_cone_tolerance                   3.
% 59.57/8.01  --extra_neg_conj                        none
% 59.57/8.01  --large_theory_mode                     true
% 59.57/8.01  --prolific_symb_bound                   200
% 59.57/8.01  --lt_threshold                          2000
% 59.57/8.01  --clause_weak_htbl                      true
% 59.57/8.01  --gc_record_bc_elim                     false
% 59.57/8.01  
% 59.57/8.01  ------ Preprocessing Options
% 59.57/8.01  
% 59.57/8.01  --preprocessing_flag                    true
% 59.57/8.01  --time_out_prep_mult                    0.1
% 59.57/8.01  --splitting_mode                        input
% 59.57/8.01  --splitting_grd                         true
% 59.57/8.01  --splitting_cvd                         false
% 59.57/8.01  --splitting_cvd_svl                     false
% 59.57/8.01  --splitting_nvd                         32
% 59.57/8.01  --sub_typing                            true
% 59.57/8.01  --prep_gs_sim                           true
% 59.57/8.01  --prep_unflatten                        true
% 59.57/8.01  --prep_res_sim                          true
% 59.57/8.01  --prep_upred                            true
% 59.57/8.01  --prep_sem_filter                       exhaustive
% 59.57/8.01  --prep_sem_filter_out                   false
% 59.57/8.01  --pred_elim                             true
% 59.57/8.01  --res_sim_input                         true
% 59.57/8.01  --eq_ax_congr_red                       true
% 59.57/8.01  --pure_diseq_elim                       true
% 59.57/8.01  --brand_transform                       false
% 59.57/8.01  --non_eq_to_eq                          false
% 59.57/8.01  --prep_def_merge                        true
% 59.57/8.01  --prep_def_merge_prop_impl              false
% 59.57/8.01  --prep_def_merge_mbd                    true
% 59.57/8.01  --prep_def_merge_tr_red                 false
% 59.57/8.01  --prep_def_merge_tr_cl                  false
% 59.57/8.01  --smt_preprocessing                     true
% 59.57/8.01  --smt_ac_axioms                         fast
% 59.57/8.01  --preprocessed_out                      false
% 59.57/8.01  --preprocessed_stats                    false
% 59.57/8.01  
% 59.57/8.01  ------ Abstraction refinement Options
% 59.57/8.01  
% 59.57/8.01  --abstr_ref                             []
% 59.57/8.01  --abstr_ref_prep                        false
% 59.57/8.01  --abstr_ref_until_sat                   false
% 59.57/8.01  --abstr_ref_sig_restrict                funpre
% 59.57/8.01  --abstr_ref_af_restrict_to_split_sk     false
% 59.57/8.01  --abstr_ref_under                       []
% 59.57/8.01  
% 59.57/8.01  ------ SAT Options
% 59.57/8.01  
% 59.57/8.01  --sat_mode                              false
% 59.57/8.01  --sat_fm_restart_options                ""
% 59.57/8.01  --sat_gr_def                            false
% 59.57/8.01  --sat_epr_types                         true
% 59.57/8.01  --sat_non_cyclic_types                  false
% 59.57/8.01  --sat_finite_models                     false
% 59.57/8.01  --sat_fm_lemmas                         false
% 59.57/8.01  --sat_fm_prep                           false
% 59.57/8.01  --sat_fm_uc_incr                        true
% 59.57/8.01  --sat_out_model                         small
% 59.57/8.01  --sat_out_clauses                       false
% 59.57/8.01  
% 59.57/8.01  ------ QBF Options
% 59.57/8.01  
% 59.57/8.01  --qbf_mode                              false
% 59.57/8.01  --qbf_elim_univ                         false
% 59.57/8.01  --qbf_dom_inst                          none
% 59.57/8.01  --qbf_dom_pre_inst                      false
% 59.57/8.01  --qbf_sk_in                             false
% 59.57/8.01  --qbf_pred_elim                         true
% 59.57/8.01  --qbf_split                             512
% 59.57/8.01  
% 59.57/8.01  ------ BMC1 Options
% 59.57/8.01  
% 59.57/8.01  --bmc1_incremental                      false
% 59.57/8.01  --bmc1_axioms                           reachable_all
% 59.57/8.01  --bmc1_min_bound                        0
% 59.57/8.01  --bmc1_max_bound                        -1
% 59.57/8.01  --bmc1_max_bound_default                -1
% 59.57/8.01  --bmc1_symbol_reachability              true
% 59.57/8.01  --bmc1_property_lemmas                  false
% 59.57/8.01  --bmc1_k_induction                      false
% 59.57/8.01  --bmc1_non_equiv_states                 false
% 59.57/8.01  --bmc1_deadlock                         false
% 59.57/8.01  --bmc1_ucm                              false
% 59.57/8.01  --bmc1_add_unsat_core                   none
% 59.57/8.01  --bmc1_unsat_core_children              false
% 59.57/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.57/8.01  --bmc1_out_stat                         full
% 59.57/8.01  --bmc1_ground_init                      false
% 59.57/8.01  --bmc1_pre_inst_next_state              false
% 59.57/8.01  --bmc1_pre_inst_state                   false
% 59.57/8.01  --bmc1_pre_inst_reach_state             false
% 59.57/8.01  --bmc1_out_unsat_core                   false
% 59.57/8.01  --bmc1_aig_witness_out                  false
% 59.57/8.01  --bmc1_verbose                          false
% 59.57/8.01  --bmc1_dump_clauses_tptp                false
% 59.57/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.57/8.01  --bmc1_dump_file                        -
% 59.57/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.57/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.57/8.01  --bmc1_ucm_extend_mode                  1
% 59.57/8.01  --bmc1_ucm_init_mode                    2
% 59.57/8.01  --bmc1_ucm_cone_mode                    none
% 59.57/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.57/8.01  --bmc1_ucm_relax_model                  4
% 59.57/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.57/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.57/8.01  --bmc1_ucm_layered_model                none
% 59.57/8.01  --bmc1_ucm_max_lemma_size               10
% 59.57/8.01  
% 59.57/8.01  ------ AIG Options
% 59.57/8.01  
% 59.57/8.01  --aig_mode                              false
% 59.57/8.01  
% 59.57/8.01  ------ Instantiation Options
% 59.57/8.01  
% 59.57/8.01  --instantiation_flag                    true
% 59.57/8.01  --inst_sos_flag                         true
% 59.57/8.01  --inst_sos_phase                        true
% 59.57/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.57/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.57/8.01  --inst_lit_sel_side                     none
% 59.57/8.01  --inst_solver_per_active                1400
% 59.57/8.01  --inst_solver_calls_frac                1.
% 59.57/8.01  --inst_passive_queue_type               priority_queues
% 59.57/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.57/8.01  --inst_passive_queues_freq              [25;2]
% 59.57/8.01  --inst_dismatching                      true
% 59.57/8.01  --inst_eager_unprocessed_to_passive     true
% 59.57/8.01  --inst_prop_sim_given                   true
% 59.57/8.01  --inst_prop_sim_new                     false
% 59.57/8.01  --inst_subs_new                         false
% 59.57/8.01  --inst_eq_res_simp                      false
% 59.57/8.01  --inst_subs_given                       false
% 59.57/8.01  --inst_orphan_elimination               true
% 59.57/8.01  --inst_learning_loop_flag               true
% 59.57/8.01  --inst_learning_start                   3000
% 59.57/8.01  --inst_learning_factor                  2
% 59.57/8.01  --inst_start_prop_sim_after_learn       3
% 59.57/8.01  --inst_sel_renew                        solver
% 59.57/8.01  --inst_lit_activity_flag                true
% 59.57/8.01  --inst_restr_to_given                   false
% 59.57/8.01  --inst_activity_threshold               500
% 59.57/8.01  --inst_out_proof                        true
% 59.57/8.01  
% 59.57/8.01  ------ Resolution Options
% 59.57/8.01  
% 59.57/8.01  --resolution_flag                       false
% 59.57/8.01  --res_lit_sel                           adaptive
% 59.57/8.01  --res_lit_sel_side                      none
% 59.57/8.01  --res_ordering                          kbo
% 59.57/8.01  --res_to_prop_solver                    active
% 59.57/8.01  --res_prop_simpl_new                    false
% 59.57/8.01  --res_prop_simpl_given                  true
% 59.57/8.01  --res_passive_queue_type                priority_queues
% 59.57/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.57/8.01  --res_passive_queues_freq               [15;5]
% 59.57/8.01  --res_forward_subs                      full
% 59.57/8.01  --res_backward_subs                     full
% 59.57/8.01  --res_forward_subs_resolution           true
% 59.57/8.01  --res_backward_subs_resolution          true
% 59.57/8.01  --res_orphan_elimination                true
% 59.57/8.01  --res_time_limit                        2.
% 59.57/8.01  --res_out_proof                         true
% 59.57/8.01  
% 59.57/8.01  ------ Superposition Options
% 59.57/8.01  
% 59.57/8.01  --superposition_flag                    true
% 59.57/8.01  --sup_passive_queue_type                priority_queues
% 59.57/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.57/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.57/8.01  --demod_completeness_check              fast
% 59.57/8.01  --demod_use_ground                      true
% 59.57/8.01  --sup_to_prop_solver                    passive
% 59.57/8.01  --sup_prop_simpl_new                    true
% 59.57/8.01  --sup_prop_simpl_given                  true
% 59.57/8.01  --sup_fun_splitting                     true
% 59.57/8.01  --sup_smt_interval                      50000
% 59.57/8.01  
% 59.57/8.01  ------ Superposition Simplification Setup
% 59.57/8.01  
% 59.57/8.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.57/8.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.57/8.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.57/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.57/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.57/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.57/8.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.57/8.01  --sup_immed_triv                        [TrivRules]
% 59.57/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.57/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.57/8.01  --sup_immed_bw_main                     []
% 59.57/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.57/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.57/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.57/8.01  --sup_input_bw                          []
% 59.57/8.01  
% 59.57/8.01  ------ Combination Options
% 59.57/8.01  
% 59.57/8.01  --comb_res_mult                         3
% 59.57/8.01  --comb_sup_mult                         2
% 59.57/8.01  --comb_inst_mult                        10
% 59.57/8.01  
% 59.57/8.01  ------ Debug Options
% 59.57/8.01  
% 59.57/8.01  --dbg_backtrace                         false
% 59.57/8.01  --dbg_dump_prop_clauses                 false
% 59.57/8.01  --dbg_dump_prop_clauses_file            -
% 59.57/8.01  --dbg_out_stat                          false
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  ------ Proving...
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  % SZS status Theorem for theBenchmark.p
% 59.57/8.01  
% 59.57/8.01  % SZS output start CNFRefutation for theBenchmark.p
% 59.57/8.01  
% 59.57/8.01  fof(f10,axiom,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f24,plain,(
% 59.57/8.01    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 59.57/8.01    inference(ennf_transformation,[],[f10])).
% 59.57/8.01  
% 59.57/8.01  fof(f25,plain,(
% 59.57/8.01    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 59.57/8.01    inference(flattening,[],[f24])).
% 59.57/8.01  
% 59.57/8.01  fof(f46,plain,(
% 59.57/8.01    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f25])).
% 59.57/8.01  
% 59.57/8.01  fof(f12,axiom,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f27,plain,(
% 59.57/8.01    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 59.57/8.01    inference(ennf_transformation,[],[f12])).
% 59.57/8.01  
% 59.57/8.01  fof(f48,plain,(
% 59.57/8.01    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f27])).
% 59.57/8.01  
% 59.57/8.01  fof(f6,axiom,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f20,plain,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 59.57/8.01    inference(ennf_transformation,[],[f6])).
% 59.57/8.01  
% 59.57/8.01  fof(f42,plain,(
% 59.57/8.01    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f20])).
% 59.57/8.01  
% 59.57/8.01  fof(f7,axiom,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f21,plain,(
% 59.57/8.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 59.57/8.01    inference(ennf_transformation,[],[f7])).
% 59.57/8.01  
% 59.57/8.01  fof(f43,plain,(
% 59.57/8.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f21])).
% 59.57/8.01  
% 59.57/8.01  fof(f1,axiom,(
% 59.57/8.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f31,plain,(
% 59.57/8.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.57/8.01    inference(nnf_transformation,[],[f1])).
% 59.57/8.01  
% 59.57/8.01  fof(f32,plain,(
% 59.57/8.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.57/8.01    inference(flattening,[],[f31])).
% 59.57/8.01  
% 59.57/8.01  fof(f36,plain,(
% 59.57/8.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 59.57/8.01    inference(cnf_transformation,[],[f32])).
% 59.57/8.01  
% 59.57/8.01  fof(f53,plain,(
% 59.57/8.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 59.57/8.01    inference(equality_resolution,[],[f36])).
% 59.57/8.01  
% 59.57/8.01  fof(f9,axiom,(
% 59.57/8.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f23,plain,(
% 59.57/8.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 59.57/8.01    inference(ennf_transformation,[],[f9])).
% 59.57/8.01  
% 59.57/8.01  fof(f45,plain,(
% 59.57/8.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f23])).
% 59.57/8.01  
% 59.57/8.01  fof(f37,plain,(
% 59.57/8.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f32])).
% 59.57/8.01  
% 59.57/8.01  fof(f14,conjecture,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f15,negated_conjecture,(
% 59.57/8.01    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 59.57/8.01    inference(negated_conjecture,[],[f14])).
% 59.57/8.01  
% 59.57/8.01  fof(f29,plain,(
% 59.57/8.01    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 59.57/8.01    inference(ennf_transformation,[],[f15])).
% 59.57/8.01  
% 59.57/8.01  fof(f30,plain,(
% 59.57/8.01    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 59.57/8.01    inference(flattening,[],[f29])).
% 59.57/8.01  
% 59.57/8.01  fof(f33,plain,(
% 59.57/8.01    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 59.57/8.01    introduced(choice_axiom,[])).
% 59.57/8.01  
% 59.57/8.01  fof(f34,plain,(
% 59.57/8.01    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 59.57/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).
% 59.57/8.01  
% 59.57/8.01  fof(f51,plain,(
% 59.57/8.01    r1_tarski(sK0,k1_relat_1(sK1))),
% 59.57/8.01    inference(cnf_transformation,[],[f34])).
% 59.57/8.01  
% 59.57/8.01  fof(f3,axiom,(
% 59.57/8.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f17,plain,(
% 59.57/8.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 59.57/8.01    inference(ennf_transformation,[],[f3])).
% 59.57/8.01  
% 59.57/8.01  fof(f39,plain,(
% 59.57/8.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f17])).
% 59.57/8.01  
% 59.57/8.01  fof(f50,plain,(
% 59.57/8.01    v1_relat_1(sK1)),
% 59.57/8.01    inference(cnf_transformation,[],[f34])).
% 59.57/8.01  
% 59.57/8.01  fof(f13,axiom,(
% 59.57/8.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f28,plain,(
% 59.57/8.01    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 59.57/8.01    inference(ennf_transformation,[],[f13])).
% 59.57/8.01  
% 59.57/8.01  fof(f49,plain,(
% 59.57/8.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f28])).
% 59.57/8.01  
% 59.57/8.01  fof(f8,axiom,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f22,plain,(
% 59.57/8.01    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 59.57/8.01    inference(ennf_transformation,[],[f8])).
% 59.57/8.01  
% 59.57/8.01  fof(f44,plain,(
% 59.57/8.01    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f22])).
% 59.57/8.01  
% 59.57/8.01  fof(f11,axiom,(
% 59.57/8.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 59.57/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.57/8.01  
% 59.57/8.01  fof(f26,plain,(
% 59.57/8.01    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 59.57/8.01    inference(ennf_transformation,[],[f11])).
% 59.57/8.01  
% 59.57/8.01  fof(f47,plain,(
% 59.57/8.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 59.57/8.01    inference(cnf_transformation,[],[f26])).
% 59.57/8.01  
% 59.57/8.01  fof(f35,plain,(
% 59.57/8.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 59.57/8.01    inference(cnf_transformation,[],[f32])).
% 59.57/8.01  
% 59.57/8.01  fof(f54,plain,(
% 59.57/8.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 59.57/8.01    inference(equality_resolution,[],[f35])).
% 59.57/8.01  
% 59.57/8.01  fof(f52,plain,(
% 59.57/8.01    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 59.57/8.01    inference(cnf_transformation,[],[f34])).
% 59.57/8.01  
% 59.57/8.01  cnf(c_11,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,X1)
% 59.57/8.01      | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
% 59.57/8.01      | ~ v1_relat_1(X0)
% 59.57/8.01      | ~ v1_relat_1(X1) ),
% 59.57/8.01      inference(cnf_transformation,[],[f46]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_197987,plain,
% 59.57/8.01      ( r1_tarski(k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))),k10_relat_1(X1,k2_relat_1(k7_relat_1(X0,sK0))))
% 59.57/8.01      | ~ r1_tarski(k7_relat_1(X0,sK0),X1)
% 59.57/8.01      | ~ v1_relat_1(X1)
% 59.57/8.01      | ~ v1_relat_1(k7_relat_1(X0,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_11]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_197990,plain,
% 59.57/8.01      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))
% 59.57/8.01      | ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
% 59.57/8.01      | ~ v1_relat_1(k7_relat_1(sK1,sK0))
% 59.57/8.01      | ~ v1_relat_1(sK1) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_197987]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_327,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 59.57/8.01      theory(equality) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1524,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,X1)
% 59.57/8.01      | r1_tarski(X2,k10_relat_1(X3,k9_relat_1(sK1,sK0)))
% 59.57/8.01      | X2 != X0
% 59.57/8.01      | k10_relat_1(X3,k9_relat_1(sK1,sK0)) != X1 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_327]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_2833,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,k10_relat_1(X1,X2))
% 59.57/8.01      | r1_tarski(X3,k10_relat_1(X4,k9_relat_1(sK1,sK0)))
% 59.57/8.01      | X3 != X0
% 59.57/8.01      | k10_relat_1(X4,k9_relat_1(sK1,sK0)) != k10_relat_1(X1,X2) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_1524]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_10751,plain,
% 59.57/8.01      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(sK1,sK0)))
% 59.57/8.01      | ~ r1_tarski(k10_relat_1(X2,X3),k10_relat_1(X4,X3))
% 59.57/8.01      | X0 != k10_relat_1(X2,X3)
% 59.57/8.01      | k10_relat_1(X1,k9_relat_1(sK1,sK0)) != k10_relat_1(X4,X3) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_2833]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_45039,plain,
% 59.57/8.01      ( ~ r1_tarski(k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))),k10_relat_1(X1,k2_relat_1(k7_relat_1(X0,sK0))))
% 59.57/8.01      | r1_tarski(sK0,k10_relat_1(X2,k9_relat_1(sK1,sK0)))
% 59.57/8.01      | k10_relat_1(X2,k9_relat_1(sK1,sK0)) != k10_relat_1(X1,k2_relat_1(k7_relat_1(X0,sK0)))
% 59.57/8.01      | sK0 != k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_10751]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_45046,plain,
% 59.57/8.01      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))
% 59.57/8.01      | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 59.57/8.01      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))
% 59.57/8.01      | sK0 != k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_45039]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_13,plain,
% 59.57/8.01      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 59.57/8.01      inference(cnf_transformation,[],[f48]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_40626,plain,
% 59.57/8.01      ( r1_tarski(k7_relat_1(sK1,sK0),sK1) | ~ v1_relat_1(sK1) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_13]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_332,plain,
% 59.57/8.01      ( X0 != X1 | X2 != X3 | k10_relat_1(X0,X2) = k10_relat_1(X1,X3) ),
% 59.57/8.01      theory(equality) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_961,plain,
% 59.57/8.01      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(X0,X1)
% 59.57/8.01      | k9_relat_1(sK1,sK0) != X1
% 59.57/8.01      | sK1 != X0 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_332]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_19604,plain,
% 59.57/8.01      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(X0,k2_relat_1(k7_relat_1(sK1,sK0)))
% 59.57/8.01      | k9_relat_1(sK1,sK0) != k2_relat_1(k7_relat_1(sK1,sK0))
% 59.57/8.01      | sK1 != X0 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_961]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_19605,plain,
% 59.57/8.01      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))
% 59.57/8.01      | k9_relat_1(sK1,sK0) != k2_relat_1(k7_relat_1(sK1,sK0))
% 59.57/8.01      | sK1 != sK1 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_19604]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_326,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_661,plain,
% 59.57/8.01      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_326]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_6989,plain,
% 59.57/8.01      ( X0 != k1_relat_1(k7_relat_1(X1,sK0))
% 59.57/8.01      | sK0 = X0
% 59.57/8.01      | sK0 != k1_relat_1(k7_relat_1(X1,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_661]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_13117,plain,
% 59.57/8.01      ( k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))) != k1_relat_1(k7_relat_1(X0,sK0))
% 59.57/8.01      | sK0 = k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0)))
% 59.57/8.01      | sK0 != k1_relat_1(k7_relat_1(X0,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_6989]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_13118,plain,
% 59.57/8.01      ( k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k7_relat_1(sK1,sK0))
% 59.57/8.01      | sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))
% 59.57/8.01      | sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_13117]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1355,plain,
% 59.57/8.01      ( X0 != X1 | k9_relat_1(sK1,sK0) != X1 | k9_relat_1(sK1,sK0) = X0 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_326]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_2327,plain,
% 59.57/8.01      ( X0 != k9_relat_1(sK1,sK0)
% 59.57/8.01      | k9_relat_1(sK1,sK0) = X0
% 59.57/8.01      | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_1355]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_7120,plain,
% 59.57/8.01      ( k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0)
% 59.57/8.01      | k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
% 59.57/8.01      | k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_2327]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_7,plain,
% 59.57/8.01      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 59.57/8.01      inference(cnf_transformation,[],[f42]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_5655,plain,
% 59.57/8.01      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_7]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_5657,plain,
% 59.57/8.01      ( v1_relat_1(k7_relat_1(sK1,sK0)) | ~ v1_relat_1(sK1) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_5655]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_8,plain,
% 59.57/8.01      ( ~ v1_relat_1(X0)
% 59.57/8.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 59.57/8.01      inference(cnf_transformation,[],[f43]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_5309,plain,
% 59.57/8.01      ( ~ v1_relat_1(sK1)
% 59.57/8.01      | k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(sK1,sK0) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_8]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1,plain,
% 59.57/8.01      ( r1_tarski(X0,X0) ),
% 59.57/8.01      inference(cnf_transformation,[],[f53]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_3544,plain,
% 59.57/8.01      ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_1]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_10,plain,
% 59.57/8.01      ( ~ v1_relat_1(X0)
% 59.57/8.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 59.57/8.01      inference(cnf_transformation,[],[f45]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_2366,plain,
% 59.57/8.01      ( ~ v1_relat_1(k7_relat_1(X0,sK0))
% 59.57/8.01      | k10_relat_1(k7_relat_1(X0,sK0),k2_relat_1(k7_relat_1(X0,sK0))) = k1_relat_1(k7_relat_1(X0,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_10]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_2368,plain,
% 59.57/8.01      ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
% 59.57/8.01      | k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_2366]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_0,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 59.57/8.01      inference(cnf_transformation,[],[f37]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1348,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
% 59.57/8.01      | ~ r1_tarski(k9_relat_1(sK1,sK0),X0)
% 59.57/8.01      | k9_relat_1(sK1,sK0) = X0 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_0]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_2285,plain,
% 59.57/8.01      ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
% 59.57/8.01      | k9_relat_1(sK1,sK0) = k9_relat_1(sK1,sK0) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_1348]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_16,negated_conjecture,
% 59.57/8.01      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 59.57/8.01      inference(cnf_transformation,[],[f51]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_610,plain,
% 59.57/8.01      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 59.57/8.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_4,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 59.57/8.01      inference(cnf_transformation,[],[f39]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_622,plain,
% 59.57/8.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 59.57/8.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_966,plain,
% 59.57/8.01      ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
% 59.57/8.01      inference(superposition,[status(thm)],[c_610,c_622]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_17,negated_conjecture,
% 59.57/8.01      ( v1_relat_1(sK1) ),
% 59.57/8.01      inference(cnf_transformation,[],[f50]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_609,plain,
% 59.57/8.01      ( v1_relat_1(sK1) = iProver_top ),
% 59.57/8.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_616,plain,
% 59.57/8.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 59.57/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.57/8.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1188,plain,
% 59.57/8.01      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 59.57/8.01      inference(superposition,[status(thm)],[c_609,c_616]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_14,plain,
% 59.57/8.01      ( ~ v1_relat_1(X0)
% 59.57/8.01      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 59.57/8.01      inference(cnf_transformation,[],[f49]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_612,plain,
% 59.57/8.01      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 59.57/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.57/8.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1076,plain,
% 59.57/8.01      ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 59.57/8.01      inference(superposition,[status(thm)],[c_609,c_612]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_9,plain,
% 59.57/8.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 59.57/8.01      inference(cnf_transformation,[],[f44]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_617,plain,
% 59.57/8.01      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 59.57/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.57/8.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1456,plain,
% 59.57/8.01      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 59.57/8.01      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 59.57/8.01      inference(superposition,[status(thm)],[c_1076,c_617]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1461,plain,
% 59.57/8.01      ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 59.57/8.01      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 59.57/8.01      inference(superposition,[status(thm)],[c_1188,c_1456]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1594,plain,
% 59.57/8.01      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top
% 59.57/8.01      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 59.57/8.01      inference(superposition,[status(thm)],[c_966,c_1461]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_1596,plain,
% 59.57/8.01      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
% 59.57/8.01      | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
% 59.57/8.01      inference(predicate_to_equality_rev,[status(thm)],[c_1594]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_12,plain,
% 59.57/8.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 59.57/8.01      inference(cnf_transformation,[],[f47]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_749,plain,
% 59.57/8.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
% 59.57/8.01      | ~ v1_relat_1(X0) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_12]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_751,plain,
% 59.57/8.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)
% 59.57/8.01      | ~ v1_relat_1(sK1) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_749]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_651,plain,
% 59.57/8.01      ( ~ r1_tarski(X0,sK0) | ~ r1_tarski(sK0,X0) | sK0 = X0 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_0]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_684,plain,
% 59.57/8.01      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
% 59.57/8.01      | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(X0,sK0)))
% 59.57/8.01      | sK0 = k1_relat_1(k7_relat_1(X0,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_651]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_686,plain,
% 59.57/8.01      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)
% 59.57/8.01      | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
% 59.57/8.01      | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_684]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_60,plain,
% 59.57/8.01      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_0]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_2,plain,
% 59.57/8.01      ( r1_tarski(X0,X0) ),
% 59.57/8.01      inference(cnf_transformation,[],[f54]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_56,plain,
% 59.57/8.01      ( r1_tarski(sK1,sK1) ),
% 59.57/8.01      inference(instantiation,[status(thm)],[c_2]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(c_15,negated_conjecture,
% 59.57/8.01      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 59.57/8.01      inference(cnf_transformation,[],[f52]) ).
% 59.57/8.01  
% 59.57/8.01  cnf(contradiction,plain,
% 59.57/8.01      ( $false ),
% 59.57/8.01      inference(minisat,
% 59.57/8.01                [status(thm)],
% 59.57/8.01                [c_197990,c_45046,c_40626,c_19605,c_13118,c_7120,c_5657,
% 59.57/8.01                 c_5309,c_3544,c_2368,c_2285,c_1596,c_751,c_686,c_60,
% 59.57/8.01                 c_56,c_15,c_17]) ).
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  % SZS output end CNFRefutation for theBenchmark.p
% 59.57/8.01  
% 59.57/8.01  ------                               Statistics
% 59.57/8.01  
% 59.57/8.01  ------ General
% 59.57/8.01  
% 59.57/8.01  abstr_ref_over_cycles:                  0
% 59.57/8.01  abstr_ref_under_cycles:                 0
% 59.57/8.01  gc_basic_clause_elim:                   0
% 59.57/8.01  forced_gc_time:                         0
% 59.57/8.01  parsing_time:                           0.007
% 59.57/8.01  unif_index_cands_time:                  0.
% 59.57/8.01  unif_index_add_time:                    0.
% 59.57/8.01  orderings_time:                         0.
% 59.57/8.01  out_proof_time:                         0.02
% 59.57/8.01  total_time:                             7.251
% 59.57/8.01  num_of_symbols:                         42
% 59.57/8.01  num_of_terms:                           278309
% 59.57/8.01  
% 59.57/8.01  ------ Preprocessing
% 59.57/8.01  
% 59.57/8.01  num_of_splits:                          0
% 59.57/8.01  num_of_split_atoms:                     0
% 59.57/8.01  num_of_reused_defs:                     0
% 59.57/8.01  num_eq_ax_congr_red:                    15
% 59.57/8.01  num_of_sem_filtered_clauses:            1
% 59.57/8.01  num_of_subtypes:                        0
% 59.57/8.01  monotx_restored_types:                  0
% 59.57/8.01  sat_num_of_epr_types:                   0
% 59.57/8.01  sat_num_of_non_cyclic_types:            0
% 59.57/8.01  sat_guarded_non_collapsed_types:        0
% 59.57/8.01  num_pure_diseq_elim:                    0
% 59.57/8.01  simp_replaced_by:                       0
% 59.57/8.01  res_preprocessed:                       87
% 59.57/8.01  prep_upred:                             0
% 59.57/8.01  prep_unflattend:                        0
% 59.57/8.01  smt_new_axioms:                         0
% 59.57/8.01  pred_elim_cands:                        2
% 59.57/8.01  pred_elim:                              0
% 59.57/8.01  pred_elim_cl:                           0
% 59.57/8.01  pred_elim_cycles:                       2
% 59.57/8.01  merged_defs:                            0
% 59.57/8.01  merged_defs_ncl:                        0
% 59.57/8.01  bin_hyper_res:                          0
% 59.57/8.01  prep_cycles:                            4
% 59.57/8.01  pred_elim_time:                         0.
% 59.57/8.01  splitting_time:                         0.
% 59.57/8.01  sem_filter_time:                        0.
% 59.57/8.01  monotx_time:                            0.
% 59.57/8.01  subtype_inf_time:                       0.
% 59.57/8.01  
% 59.57/8.01  ------ Problem properties
% 59.57/8.01  
% 59.57/8.01  clauses:                                17
% 59.57/8.01  conjectures:                            3
% 59.57/8.01  epr:                                    3
% 59.57/8.01  horn:                                   17
% 59.57/8.01  ground:                                 3
% 59.57/8.01  unary:                                  5
% 59.57/8.01  binary:                                 9
% 59.57/8.01  lits:                                   33
% 59.57/8.01  lits_eq:                                5
% 59.57/8.01  fd_pure:                                0
% 59.57/8.01  fd_pseudo:                              0
% 59.57/8.01  fd_cond:                                0
% 59.57/8.01  fd_pseudo_cond:                         1
% 59.57/8.01  ac_symbols:                             0
% 59.57/8.01  
% 59.57/8.01  ------ Propositional Solver
% 59.57/8.01  
% 59.57/8.01  prop_solver_calls:                      96
% 59.57/8.01  prop_fast_solver_calls:                 2000
% 59.57/8.01  smt_solver_calls:                       0
% 59.57/8.01  smt_fast_solver_calls:                  0
% 59.57/8.01  prop_num_of_clauses:                    95087
% 59.57/8.01  prop_preprocess_simplified:             128119
% 59.57/8.01  prop_fo_subsumed:                       30
% 59.57/8.01  prop_solver_time:                       0.
% 59.57/8.01  smt_solver_time:                        0.
% 59.57/8.01  smt_fast_solver_time:                   0.
% 59.57/8.01  prop_fast_solver_time:                  0.
% 59.57/8.01  prop_unsat_core_time:                   0.012
% 59.57/8.01  
% 59.57/8.01  ------ QBF
% 59.57/8.01  
% 59.57/8.01  qbf_q_res:                              0
% 59.57/8.01  qbf_num_tautologies:                    0
% 59.57/8.01  qbf_prep_cycles:                        0
% 59.57/8.01  
% 59.57/8.01  ------ BMC1
% 59.57/8.01  
% 59.57/8.01  bmc1_current_bound:                     -1
% 59.57/8.01  bmc1_last_solved_bound:                 -1
% 59.57/8.01  bmc1_unsat_core_size:                   -1
% 59.57/8.01  bmc1_unsat_core_parents_size:           -1
% 59.57/8.01  bmc1_merge_next_fun:                    0
% 59.57/8.01  bmc1_unsat_core_clauses_time:           0.
% 59.57/8.01  
% 59.57/8.01  ------ Instantiation
% 59.57/8.01  
% 59.57/8.01  inst_num_of_clauses:                    2988
% 59.57/8.01  inst_num_in_passive:                    469
% 59.57/8.01  inst_num_in_active:                     3619
% 59.57/8.01  inst_num_in_unprocessed:                1267
% 59.57/8.01  inst_num_of_loops:                      4311
% 59.57/8.01  inst_num_of_learning_restarts:          1
% 59.57/8.01  inst_num_moves_active_passive:          684
% 59.57/8.01  inst_lit_activity:                      0
% 59.57/8.01  inst_lit_activity_moves:                5
% 59.57/8.01  inst_num_tautologies:                   0
% 59.57/8.01  inst_num_prop_implied:                  0
% 59.57/8.01  inst_num_existing_simplified:           0
% 59.57/8.01  inst_num_eq_res_simplified:             0
% 59.57/8.01  inst_num_child_elim:                    0
% 59.57/8.01  inst_num_of_dismatching_blockings:      31495
% 59.57/8.01  inst_num_of_non_proper_insts:           20338
% 59.57/8.01  inst_num_of_duplicates:                 0
% 59.57/8.01  inst_inst_num_from_inst_to_res:         0
% 59.57/8.01  inst_dismatching_checking_time:         0.
% 59.57/8.01  
% 59.57/8.01  ------ Resolution
% 59.57/8.01  
% 59.57/8.01  res_num_of_clauses:                     26
% 59.57/8.01  res_num_in_passive:                     26
% 59.57/8.01  res_num_in_active:                      0
% 59.57/8.01  res_num_of_loops:                       91
% 59.57/8.01  res_forward_subset_subsumed:            1019
% 59.57/8.01  res_backward_subset_subsumed:           4
% 59.57/8.01  res_forward_subsumed:                   0
% 59.57/8.01  res_backward_subsumed:                  0
% 59.57/8.01  res_forward_subsumption_resolution:     0
% 59.57/8.01  res_backward_subsumption_resolution:    0
% 59.57/8.01  res_clause_to_clause_subsumption:       123204
% 59.57/8.01  res_orphan_elimination:                 0
% 59.57/8.01  res_tautology_del:                      906
% 59.57/8.01  res_num_eq_res_simplified:              0
% 59.57/8.01  res_num_sel_changes:                    0
% 59.57/8.01  res_moves_from_active_to_pass:          0
% 59.57/8.01  
% 59.57/8.01  ------ Superposition
% 59.57/8.01  
% 59.57/8.01  sup_time_total:                         0.
% 59.57/8.01  sup_time_generating:                    0.
% 59.57/8.01  sup_time_sim_full:                      0.
% 59.57/8.01  sup_time_sim_immed:                     0.
% 59.57/8.01  
% 59.57/8.01  sup_num_of_clauses:                     12658
% 59.57/8.01  sup_num_in_active:                      818
% 59.57/8.01  sup_num_in_passive:                     11840
% 59.57/8.01  sup_num_of_loops:                       862
% 59.57/8.01  sup_fw_superposition:                   11492
% 59.57/8.01  sup_bw_superposition:                   15796
% 59.57/8.01  sup_immediate_simplified:               9527
% 59.57/8.01  sup_given_eliminated:                   3
% 59.57/8.01  comparisons_done:                       0
% 59.57/8.01  comparisons_avoided:                    0
% 59.57/8.01  
% 59.57/8.01  ------ Simplifications
% 59.57/8.01  
% 59.57/8.01  
% 59.57/8.01  sim_fw_subset_subsumed:                 960
% 59.57/8.01  sim_bw_subset_subsumed:                 203
% 59.57/8.01  sim_fw_subsumed:                        2273
% 59.57/8.01  sim_bw_subsumed:                        12
% 59.57/8.01  sim_fw_subsumption_res:                 0
% 59.57/8.01  sim_bw_subsumption_res:                 0
% 59.57/8.01  sim_tautology_del:                      479
% 59.57/8.01  sim_eq_tautology_del:                   1712
% 59.57/8.01  sim_eq_res_simp:                        0
% 59.57/8.01  sim_fw_demodulated:                     5246
% 59.57/8.01  sim_bw_demodulated:                     42
% 59.57/8.01  sim_light_normalised:                   2253
% 59.57/8.01  sim_joinable_taut:                      0
% 59.57/8.01  sim_joinable_simp:                      0
% 59.57/8.01  sim_ac_normalised:                      0
% 59.57/8.01  sim_smt_subsumption:                    0
% 59.57/8.01  
%------------------------------------------------------------------------------
