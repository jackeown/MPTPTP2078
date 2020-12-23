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
% DateTime   : Thu Dec  3 11:52:15 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 222 expanded)
%              Number of clauses        :   78 (  96 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 ( 767 expanded)
%              Number of equality atoms :  123 ( 154 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5440,plain,
    ( r1_tarski(X0,k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1))
    | ~ r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_22240,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1))
    | ~ r1_tarski(k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
    inference(instantiation,[status(thm)],[c_5440])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5462,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15666,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | r1_tarski(k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
    inference(instantiation,[status(thm)],[c_5462])).

cnf(c_326,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2503,plain,
    ( X0 != X1
    | X0 = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != X1 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_6798,plain,
    ( X0 != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | X0 = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_2503])).

cnf(c_13808,plain,
    ( k9_relat_1(X0,k10_relat_1(sK2,sK0)) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k9_relat_1(X0,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_6798])).

cnf(c_13809,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_13808])).

cnf(c_327,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_913,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1138,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_12559,plain,
    ( r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | ~ r1_tarski(sK0,k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))))
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_1060,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,X2)
    | X2 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1991,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),X0)
    | r1_tarski(sK0,X1)
    | X1 != X0
    | sK0 != k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_2720,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK0,k2_relat_1(sK2)))
    | r1_tarski(sK0,X0)
    | X0 != k3_xboole_0(sK0,k2_relat_1(sK2))
    | sK0 != k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_6533,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK0,k2_relat_1(sK2)))
    | r1_tarski(sK0,k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))))
    | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k3_xboole_0(sK0,k2_relat_1(sK2))
    | sK0 != k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2720])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_2906,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),X0)
    | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_5103,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_2906])).

cnf(c_325,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3409,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_330,plain,
    ( X0 != X1
    | X2 != X3
    | k9_relat_1(X0,X2) = k9_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_1432,plain,
    ( X0 != k10_relat_1(sK2,sK0)
    | X1 != sK2
    | k9_relat_1(X1,X0) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_3408,plain,
    ( X0 != sK2
    | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,sK0)
    | k9_relat_1(X0,k10_relat_1(sK2,sK0)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_3410,plain,
    ( k10_relat_1(sK2,sK0) != k10_relat_1(sK2,sK0)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3408])).

cnf(c_328,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X0) = k3_xboole_0(X2,X1) ),
    theory(equality)).

cnf(c_2259,plain,
    ( X0 != k2_relat_1(sK2)
    | k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_3218,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
    | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_666,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,sK1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_813,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),X0)
    | r1_tarski(sK0,sK1)
    | sK1 != X0
    | sK0 != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_2704,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1))
    | r1_tarski(sK0,sK1)
    | sK1 != k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | sK0 != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2215,plain,
    ( r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK0,k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_729,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_945,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1159,plain,
    ( k2_xboole_0(X0,sK1) != sK1
    | sK1 = k2_xboole_0(X0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_2208,plain,
    ( k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) != sK1
    | sK1 = k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1160,plain,
    ( ~ r1_tarski(X0,sK1)
    | k2_xboole_0(X0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1648,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_188,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_189,plain,
    ( ~ v1_relat_1(sK2)
    | k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_193,plain,
    ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_17])).

cnf(c_1428,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_704,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_803,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_835,plain,
    ( k3_xboole_0(sK0,X0) != sK0
    | sK0 = k3_xboole_0(sK0,X0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1078,plain,
    ( k3_xboole_0(sK0,k2_relat_1(sK2)) != sK0
    | sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_836,plain,
    ( ~ r1_tarski(sK0,X0)
    | k3_xboole_0(sK0,X0) = sK0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1057,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK2))
    | k3_xboole_0(sK0,k2_relat_1(sK2)) = sK0 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_11,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_199,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_200,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_204,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_17])).

cnf(c_966,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_807,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_718,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK0) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_693,plain,
    ( ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,X0)
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_717,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK0)
    | ~ r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_699,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_55,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_51,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_33,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22240,c_15666,c_13809,c_12559,c_6533,c_5103,c_3409,c_3410,c_3218,c_2704,c_2215,c_2208,c_1648,c_1428,c_1078,c_1057,c_966,c_807,c_718,c_717,c_699,c_55,c_51,c_33,c_13,c_14,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:24:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.07/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.07/1.48  
% 7.07/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.07/1.48  
% 7.07/1.48  ------  iProver source info
% 7.07/1.48  
% 7.07/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.07/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.07/1.48  git: non_committed_changes: false
% 7.07/1.48  git: last_make_outside_of_git: false
% 7.07/1.48  
% 7.07/1.48  ------ 
% 7.07/1.48  ------ Parsing...
% 7.07/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.07/1.48  
% 7.07/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.07/1.48  
% 7.07/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.07/1.48  
% 7.07/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.07/1.48  ------ Proving...
% 7.07/1.48  ------ Problem Properties 
% 7.07/1.48  
% 7.07/1.48  
% 7.07/1.48  clauses                                 15
% 7.07/1.48  conjectures                             3
% 7.07/1.48  EPR                                     3
% 7.07/1.48  Horn                                    15
% 7.07/1.48  unary                                   9
% 7.07/1.48  binary                                  5
% 7.07/1.48  lits                                    22
% 7.07/1.48  lits eq                                 6
% 7.07/1.48  fd_pure                                 0
% 7.07/1.48  fd_pseudo                               0
% 7.07/1.48  fd_cond                                 0
% 7.07/1.48  fd_pseudo_cond                          1
% 7.07/1.48  AC symbols                              0
% 7.07/1.48  
% 7.07/1.48  ------ Input Options Time Limit: Unbounded
% 7.07/1.48  
% 7.07/1.48  
% 7.07/1.48  ------ 
% 7.07/1.48  Current options:
% 7.07/1.48  ------ 
% 7.07/1.48  
% 7.07/1.48  
% 7.07/1.48  
% 7.07/1.48  
% 7.07/1.48  ------ Proving...
% 7.07/1.48  
% 7.07/1.48  
% 7.07/1.48  % SZS status Theorem for theBenchmark.p
% 7.07/1.48  
% 7.07/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.07/1.48  
% 7.07/1.48  fof(f3,axiom,(
% 7.07/1.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f14,plain,(
% 7.07/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.07/1.48    inference(ennf_transformation,[],[f3])).
% 7.07/1.48  
% 7.07/1.48  fof(f35,plain,(
% 7.07/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f14])).
% 7.07/1.48  
% 7.07/1.48  fof(f7,axiom,(
% 7.07/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f17,plain,(
% 7.07/1.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 7.07/1.48    inference(ennf_transformation,[],[f7])).
% 7.07/1.48  
% 7.07/1.48  fof(f39,plain,(
% 7.07/1.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f17])).
% 7.07/1.48  
% 7.07/1.48  fof(f9,axiom,(
% 7.07/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f19,plain,(
% 7.07/1.48    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.07/1.48    inference(ennf_transformation,[],[f9])).
% 7.07/1.48  
% 7.07/1.48  fof(f20,plain,(
% 7.07/1.48    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.07/1.48    inference(flattening,[],[f19])).
% 7.07/1.48  
% 7.07/1.48  fof(f41,plain,(
% 7.07/1.48    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f20])).
% 7.07/1.48  
% 7.07/1.48  fof(f12,conjecture,(
% 7.07/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f13,negated_conjecture,(
% 7.07/1.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.07/1.48    inference(negated_conjecture,[],[f12])).
% 7.07/1.48  
% 7.07/1.48  fof(f25,plain,(
% 7.07/1.48    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.07/1.48    inference(ennf_transformation,[],[f13])).
% 7.07/1.48  
% 7.07/1.48  fof(f26,plain,(
% 7.07/1.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.07/1.48    inference(flattening,[],[f25])).
% 7.07/1.48  
% 7.07/1.48  fof(f29,plain,(
% 7.07/1.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.07/1.48    introduced(choice_axiom,[])).
% 7.07/1.48  
% 7.07/1.48  fof(f30,plain,(
% 7.07/1.48    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.07/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29])).
% 7.07/1.48  
% 7.07/1.48  fof(f44,plain,(
% 7.07/1.48    v1_relat_1(sK2)),
% 7.07/1.48    inference(cnf_transformation,[],[f30])).
% 7.07/1.48  
% 7.07/1.48  fof(f2,axiom,(
% 7.07/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f27,plain,(
% 7.07/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.07/1.48    inference(nnf_transformation,[],[f2])).
% 7.07/1.48  
% 7.07/1.48  fof(f28,plain,(
% 7.07/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.07/1.48    inference(flattening,[],[f27])).
% 7.07/1.48  
% 7.07/1.48  fof(f32,plain,(
% 7.07/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.07/1.48    inference(cnf_transformation,[],[f28])).
% 7.07/1.48  
% 7.07/1.48  fof(f50,plain,(
% 7.07/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.07/1.48    inference(equality_resolution,[],[f32])).
% 7.07/1.48  
% 7.07/1.48  fof(f4,axiom,(
% 7.07/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f15,plain,(
% 7.07/1.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.07/1.48    inference(ennf_transformation,[],[f4])).
% 7.07/1.48  
% 7.07/1.48  fof(f36,plain,(
% 7.07/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f15])).
% 7.07/1.48  
% 7.07/1.48  fof(f11,axiom,(
% 7.07/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f23,plain,(
% 7.07/1.48    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.07/1.48    inference(ennf_transformation,[],[f11])).
% 7.07/1.48  
% 7.07/1.48  fof(f24,plain,(
% 7.07/1.48    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.07/1.48    inference(flattening,[],[f23])).
% 7.07/1.48  
% 7.07/1.48  fof(f43,plain,(
% 7.07/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f24])).
% 7.07/1.48  
% 7.07/1.48  fof(f45,plain,(
% 7.07/1.48    v1_funct_1(sK2)),
% 7.07/1.48    inference(cnf_transformation,[],[f30])).
% 7.07/1.48  
% 7.07/1.48  fof(f5,axiom,(
% 7.07/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f16,plain,(
% 7.07/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.07/1.48    inference(ennf_transformation,[],[f5])).
% 7.07/1.48  
% 7.07/1.48  fof(f37,plain,(
% 7.07/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f16])).
% 7.07/1.48  
% 7.07/1.48  fof(f10,axiom,(
% 7.07/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f21,plain,(
% 7.07/1.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.07/1.48    inference(ennf_transformation,[],[f10])).
% 7.07/1.48  
% 7.07/1.48  fof(f22,plain,(
% 7.07/1.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.07/1.48    inference(flattening,[],[f21])).
% 7.07/1.48  
% 7.07/1.48  fof(f42,plain,(
% 7.07/1.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f22])).
% 7.07/1.48  
% 7.07/1.48  fof(f34,plain,(
% 7.07/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f28])).
% 7.07/1.48  
% 7.07/1.48  fof(f8,axiom,(
% 7.07/1.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.07/1.48  
% 7.07/1.48  fof(f18,plain,(
% 7.07/1.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.07/1.48    inference(ennf_transformation,[],[f8])).
% 7.07/1.48  
% 7.07/1.48  fof(f40,plain,(
% 7.07/1.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.07/1.48    inference(cnf_transformation,[],[f18])).
% 7.07/1.48  
% 7.07/1.48  fof(f48,plain,(
% 7.07/1.48    ~r1_tarski(sK0,sK1)),
% 7.07/1.48    inference(cnf_transformation,[],[f30])).
% 7.07/1.48  
% 7.07/1.48  fof(f47,plain,(
% 7.07/1.48    r1_tarski(sK0,k2_relat_1(sK2))),
% 7.07/1.48    inference(cnf_transformation,[],[f30])).
% 7.07/1.48  
% 7.07/1.48  fof(f46,plain,(
% 7.07/1.48    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 7.07/1.48    inference(cnf_transformation,[],[f30])).
% 7.07/1.48  
% 7.07/1.48  cnf(c_4,plain,
% 7.07/1.48      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.07/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_5440,plain,
% 7.07/1.48      ( r1_tarski(X0,k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1))
% 7.07/1.48      | ~ r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_22240,plain,
% 7.07/1.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1))
% 7.07/1.48      | ~ r1_tarski(k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_5440]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_8,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1)
% 7.07/1.48      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 7.07/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_5462,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
% 7.07/1.48      | r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_15666,plain,
% 7.07/1.48      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
% 7.07/1.48      | r1_tarski(k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_5462]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_326,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_2503,plain,
% 7.07/1.48      ( X0 != X1
% 7.07/1.48      | X0 = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
% 7.07/1.48      | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != X1 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_326]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_6798,plain,
% 7.07/1.48      ( X0 != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
% 7.07/1.48      | X0 = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
% 7.07/1.48      | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_2503]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_13808,plain,
% 7.07/1.48      ( k9_relat_1(X0,k10_relat_1(sK2,sK0)) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
% 7.07/1.48      | k9_relat_1(X0,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
% 7.07/1.48      | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_6798]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_13809,plain,
% 7.07/1.48      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
% 7.07/1.48      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
% 7.07/1.48      | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_13808]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_327,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.07/1.48      theory(equality) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_913,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1)
% 7.07/1.48      | r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
% 7.07/1.48      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != X1
% 7.07/1.48      | sK0 != X0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_327]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1138,plain,
% 7.07/1.48      ( ~ r1_tarski(sK0,X0)
% 7.07/1.48      | r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
% 7.07/1.48      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != X0
% 7.07/1.48      | sK0 != sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_913]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_12559,plain,
% 7.07/1.48      ( r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
% 7.07/1.48      | ~ r1_tarski(sK0,k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))))
% 7.07/1.48      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2)))
% 7.07/1.48      | sK0 != sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1138]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1060,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,X2) | X2 != X1 | sK0 != X0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_327]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1991,plain,
% 7.07/1.48      ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),X0)
% 7.07/1.48      | r1_tarski(sK0,X1)
% 7.07/1.48      | X1 != X0
% 7.07/1.48      | sK0 != k3_xboole_0(sK0,k2_relat_1(sK2)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1060]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_2720,plain,
% 7.07/1.48      ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK0,k2_relat_1(sK2)))
% 7.07/1.48      | r1_tarski(sK0,X0)
% 7.07/1.48      | X0 != k3_xboole_0(sK0,k2_relat_1(sK2))
% 7.07/1.48      | sK0 != k3_xboole_0(sK0,k2_relat_1(sK2)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1991]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_6533,plain,
% 7.07/1.48      ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK0,k2_relat_1(sK2)))
% 7.07/1.48      | r1_tarski(sK0,k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))))
% 7.07/1.48      | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) != k3_xboole_0(sK0,k2_relat_1(sK2))
% 7.07/1.48      | sK0 != k3_xboole_0(sK0,k2_relat_1(sK2)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_2720]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_10,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1)
% 7.07/1.48      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.07/1.48      | ~ v1_relat_1(X2) ),
% 7.07/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_17,negated_conjecture,
% 7.07/1.48      ( v1_relat_1(sK2) ),
% 7.07/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_222,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1)
% 7.07/1.48      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.07/1.48      | sK2 != X2 ),
% 7.07/1.48      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_223,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1)
% 7.07/1.48      | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
% 7.07/1.48      inference(unflattening,[status(thm)],[c_222]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_2906,plain,
% 7.07/1.48      ( ~ r1_tarski(k10_relat_1(sK2,sK0),X0)
% 7.07/1.48      | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,X0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_223]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_5103,plain,
% 7.07/1.48      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
% 7.07/1.48      | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_2906]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_325,plain,( X0 = X0 ),theory(equality) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_3409,plain,
% 7.07/1.48      ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK0) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_325]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_330,plain,
% 7.07/1.48      ( X0 != X1 | X2 != X3 | k9_relat_1(X0,X2) = k9_relat_1(X1,X3) ),
% 7.07/1.48      theory(equality) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1432,plain,
% 7.07/1.48      ( X0 != k10_relat_1(sK2,sK0)
% 7.07/1.48      | X1 != sK2
% 7.07/1.48      | k9_relat_1(X1,X0) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_330]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_3408,plain,
% 7.07/1.48      ( X0 != sK2
% 7.07/1.48      | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,sK0)
% 7.07/1.48      | k9_relat_1(X0,k10_relat_1(sK2,sK0)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1432]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_3410,plain,
% 7.07/1.48      ( k10_relat_1(sK2,sK0) != k10_relat_1(sK2,sK0)
% 7.07/1.48      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
% 7.07/1.48      | sK2 != sK2 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_3408]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_328,plain,
% 7.07/1.48      ( X0 != X1 | k3_xboole_0(X2,X0) = k3_xboole_0(X2,X1) ),
% 7.07/1.48      theory(equality) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_2259,plain,
% 7.07/1.48      ( X0 != k2_relat_1(sK2)
% 7.07/1.48      | k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_328]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_3218,plain,
% 7.07/1.48      ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
% 7.07/1.48      | k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_2259]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_666,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,sK1) | sK1 != X1 | sK0 != X0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_327]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_813,plain,
% 7.07/1.48      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),X0)
% 7.07/1.48      | r1_tarski(sK0,sK1)
% 7.07/1.48      | sK1 != X0
% 7.07/1.48      | sK0 != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_666]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_2704,plain,
% 7.07/1.48      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1))
% 7.07/1.48      | r1_tarski(sK0,sK1)
% 7.07/1.48      | sK1 != k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
% 7.07/1.48      | sK0 != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_813]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_3,plain,
% 7.07/1.48      ( r1_tarski(X0,X0) ),
% 7.07/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_2215,plain,
% 7.07/1.48      ( r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK0,k2_relat_1(sK2))) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_729,plain,
% 7.07/1.48      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_326]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_945,plain,
% 7.07/1.48      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_729]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1159,plain,
% 7.07/1.48      ( k2_xboole_0(X0,sK1) != sK1
% 7.07/1.48      | sK1 = k2_xboole_0(X0,sK1)
% 7.07/1.48      | sK1 != sK1 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_945]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_2208,plain,
% 7.07/1.48      ( k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) != sK1
% 7.07/1.48      | sK1 = k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
% 7.07/1.48      | sK1 != sK1 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1159]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_5,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.07/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1160,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,sK1) | k2_xboole_0(X0,sK1) = sK1 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1648,plain,
% 7.07/1.48      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
% 7.07/1.48      | k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) = sK1 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1160]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_12,plain,
% 7.07/1.48      ( ~ v1_funct_1(X0)
% 7.07/1.48      | ~ v1_relat_1(X0)
% 7.07/1.48      | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 7.07/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_16,negated_conjecture,
% 7.07/1.48      ( v1_funct_1(sK2) ),
% 7.07/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_188,plain,
% 7.07/1.48      ( ~ v1_relat_1(X0)
% 7.07/1.48      | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 7.07/1.48      | sK2 != X0 ),
% 7.07/1.48      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_189,plain,
% 7.07/1.48      ( ~ v1_relat_1(sK2)
% 7.07/1.48      | k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 7.07/1.48      inference(unflattening,[status(thm)],[c_188]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_193,plain,
% 7.07/1.48      ( k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 7.07/1.48      inference(global_propositional_subsumption,
% 7.07/1.48                [status(thm)],
% 7.07/1.48                [c_189,c_17]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1428,plain,
% 7.07/1.48      ( k3_xboole_0(sK0,k9_relat_1(sK2,k1_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_193]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_704,plain,
% 7.07/1.48      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_326]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_803,plain,
% 7.07/1.48      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_704]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_835,plain,
% 7.07/1.48      ( k3_xboole_0(sK0,X0) != sK0
% 7.07/1.48      | sK0 = k3_xboole_0(sK0,X0)
% 7.07/1.48      | sK0 != sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_803]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1078,plain,
% 7.07/1.48      ( k3_xboole_0(sK0,k2_relat_1(sK2)) != sK0
% 7.07/1.48      | sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))
% 7.07/1.48      | sK0 != sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_835]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_6,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.07/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_836,plain,
% 7.07/1.48      ( ~ r1_tarski(sK0,X0) | k3_xboole_0(sK0,X0) = sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1057,plain,
% 7.07/1.48      ( ~ r1_tarski(sK0,k2_relat_1(sK2))
% 7.07/1.48      | k3_xboole_0(sK0,k2_relat_1(sK2)) = sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_836]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_11,plain,
% 7.07/1.48      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.07/1.48      | ~ v1_funct_1(X0)
% 7.07/1.48      | ~ v1_relat_1(X0) ),
% 7.07/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_199,plain,
% 7.07/1.48      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.07/1.48      | ~ v1_relat_1(X0)
% 7.07/1.48      | sK2 != X0 ),
% 7.07/1.48      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_200,plain,
% 7.07/1.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 7.07/1.48      | ~ v1_relat_1(sK2) ),
% 7.07/1.48      inference(unflattening,[status(thm)],[c_199]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_204,plain,
% 7.07/1.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
% 7.07/1.48      inference(global_propositional_subsumption,
% 7.07/1.48                [status(thm)],
% 7.07/1.48                [c_200,c_17]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_966,plain,
% 7.07/1.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_204]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_807,plain,
% 7.07/1.48      ( sK1 = sK1 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_325]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_718,plain,
% 7.07/1.48      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK0) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_204]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_1,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.07/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_693,plain,
% 7.07/1.48      ( ~ r1_tarski(X0,sK0) | ~ r1_tarski(sK0,X0) | sK0 = X0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_717,plain,
% 7.07/1.48      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK0)
% 7.07/1.48      | ~ r1_tarski(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
% 7.07/1.48      | sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_693]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_699,plain,
% 7.07/1.48      ( sK0 = sK0 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_325]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_55,plain,
% 7.07/1.48      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_51,plain,
% 7.07/1.48      ( r1_tarski(sK2,sK2) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_9,plain,
% 7.07/1.48      ( ~ v1_relat_1(X0)
% 7.07/1.48      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.07/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_33,plain,
% 7.07/1.48      ( ~ v1_relat_1(sK2)
% 7.07/1.48      | k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 7.07/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_13,negated_conjecture,
% 7.07/1.48      ( ~ r1_tarski(sK0,sK1) ),
% 7.07/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_14,negated_conjecture,
% 7.07/1.48      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 7.07/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(c_15,negated_conjecture,
% 7.07/1.48      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 7.07/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.07/1.48  
% 7.07/1.48  cnf(contradiction,plain,
% 7.07/1.48      ( $false ),
% 7.07/1.48      inference(minisat,
% 7.07/1.48                [status(thm)],
% 7.07/1.48                [c_22240,c_15666,c_13809,c_12559,c_6533,c_5103,c_3409,
% 7.07/1.48                 c_3410,c_3218,c_2704,c_2215,c_2208,c_1648,c_1428,c_1078,
% 7.07/1.48                 c_1057,c_966,c_807,c_718,c_717,c_699,c_55,c_51,c_33,
% 7.07/1.48                 c_13,c_14,c_15,c_17]) ).
% 7.07/1.48  
% 7.07/1.48  
% 7.07/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.07/1.48  
% 7.07/1.48  ------                               Statistics
% 7.07/1.48  
% 7.07/1.48  ------ Selected
% 7.07/1.48  
% 7.07/1.48  total_time:                             0.675
% 7.07/1.48  
%------------------------------------------------------------------------------
