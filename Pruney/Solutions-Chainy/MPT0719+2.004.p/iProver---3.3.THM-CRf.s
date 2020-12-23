%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:01 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   67 (  85 expanded)
%              Number of clauses        :   26 (  28 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  234 ( 282 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK2(X0,X1)),k1_funct_1(X0,sK2(X0,X1)))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK2(X0,X1)),k1_funct_1(X0,sK2(X0,X1)))
                & r2_hidden(sK2(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK3)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f30])).

fof(f47,plain,(
    ~ v5_funct_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1091,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK3,k1_xboole_0),sK1(sK2(sK3,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_980,plain,
    ( ~ r2_hidden(sK2(sK3,k1_xboole_0),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
    | r2_hidden(k4_tarski(sK2(sK3,k1_xboole_0),sK1(sK2(sK3,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_333,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_921,plain,
    ( sK2(sK3,k1_xboole_0) = sK2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_823,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | X0 != sK2(sK3,k1_xboole_0)
    | X1 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_869,plain,
    ( r2_hidden(X0,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
    | ~ r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | X0 != sK2(sK3,k1_xboole_0)
    | k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_920,plain,
    ( r2_hidden(sK2(sK3,k1_xboole_0),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
    | ~ r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | sK2(sK3,k1_xboole_0) != sK2(sK3,k1_xboole_0)
    | k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_870,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( v5_funct_1(X0,X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_294,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_295,plain,
    ( r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_3,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_217,plain,
    ( v1_relat_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_2])).

cnf(c_218,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_9,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_210,plain,
    ( v1_funct_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_2])).

cnf(c_211,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1091,c_980,c_921,c_920,c_870,c_295,c_218,c_211,c_2,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.67/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.04  
% 1.67/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.67/1.04  
% 1.67/1.04  ------  iProver source info
% 1.67/1.04  
% 1.67/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.67/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.67/1.04  git: non_committed_changes: false
% 1.67/1.04  git: last_make_outside_of_git: false
% 1.67/1.04  
% 1.67/1.04  ------ 
% 1.67/1.04  
% 1.67/1.04  ------ Input Options
% 1.67/1.04  
% 1.67/1.04  --out_options                           all
% 1.67/1.04  --tptp_safe_out                         true
% 1.67/1.04  --problem_path                          ""
% 1.67/1.04  --include_path                          ""
% 1.67/1.04  --clausifier                            res/vclausify_rel
% 1.67/1.04  --clausifier_options                    --mode clausify
% 1.67/1.04  --stdin                                 false
% 1.67/1.04  --stats_out                             all
% 1.67/1.04  
% 1.67/1.04  ------ General Options
% 1.67/1.04  
% 1.67/1.04  --fof                                   false
% 1.67/1.04  --time_out_real                         305.
% 1.67/1.04  --time_out_virtual                      -1.
% 1.67/1.04  --symbol_type_check                     false
% 1.67/1.04  --clausify_out                          false
% 1.67/1.04  --sig_cnt_out                           false
% 1.67/1.04  --trig_cnt_out                          false
% 1.67/1.04  --trig_cnt_out_tolerance                1.
% 1.67/1.04  --trig_cnt_out_sk_spl                   false
% 1.67/1.04  --abstr_cl_out                          false
% 1.67/1.04  
% 1.67/1.04  ------ Global Options
% 1.67/1.04  
% 1.67/1.04  --schedule                              default
% 1.67/1.04  --add_important_lit                     false
% 1.67/1.04  --prop_solver_per_cl                    1000
% 1.67/1.04  --min_unsat_core                        false
% 1.67/1.04  --soft_assumptions                      false
% 1.67/1.04  --soft_lemma_size                       3
% 1.67/1.04  --prop_impl_unit_size                   0
% 1.67/1.04  --prop_impl_unit                        []
% 1.67/1.04  --share_sel_clauses                     true
% 1.67/1.04  --reset_solvers                         false
% 1.67/1.04  --bc_imp_inh                            [conj_cone]
% 1.67/1.04  --conj_cone_tolerance                   3.
% 1.67/1.04  --extra_neg_conj                        none
% 1.67/1.04  --large_theory_mode                     true
% 1.67/1.04  --prolific_symb_bound                   200
% 1.67/1.04  --lt_threshold                          2000
% 1.67/1.04  --clause_weak_htbl                      true
% 1.67/1.04  --gc_record_bc_elim                     false
% 1.67/1.04  
% 1.67/1.04  ------ Preprocessing Options
% 1.67/1.04  
% 1.67/1.04  --preprocessing_flag                    true
% 1.67/1.04  --time_out_prep_mult                    0.1
% 1.67/1.04  --splitting_mode                        input
% 1.67/1.04  --splitting_grd                         true
% 1.67/1.04  --splitting_cvd                         false
% 1.67/1.04  --splitting_cvd_svl                     false
% 1.67/1.04  --splitting_nvd                         32
% 1.67/1.04  --sub_typing                            true
% 1.67/1.04  --prep_gs_sim                           true
% 1.67/1.04  --prep_unflatten                        true
% 1.67/1.04  --prep_res_sim                          true
% 1.67/1.04  --prep_upred                            true
% 1.67/1.04  --prep_sem_filter                       exhaustive
% 1.67/1.04  --prep_sem_filter_out                   false
% 1.67/1.04  --pred_elim                             true
% 1.67/1.04  --res_sim_input                         true
% 1.67/1.04  --eq_ax_congr_red                       true
% 1.67/1.04  --pure_diseq_elim                       true
% 1.67/1.04  --brand_transform                       false
% 1.67/1.04  --non_eq_to_eq                          false
% 1.67/1.04  --prep_def_merge                        true
% 1.67/1.04  --prep_def_merge_prop_impl              false
% 1.67/1.04  --prep_def_merge_mbd                    true
% 1.67/1.04  --prep_def_merge_tr_red                 false
% 1.67/1.04  --prep_def_merge_tr_cl                  false
% 1.67/1.04  --smt_preprocessing                     true
% 1.67/1.04  --smt_ac_axioms                         fast
% 1.67/1.04  --preprocessed_out                      false
% 1.67/1.04  --preprocessed_stats                    false
% 1.67/1.04  
% 1.67/1.04  ------ Abstraction refinement Options
% 1.67/1.04  
% 1.67/1.04  --abstr_ref                             []
% 1.67/1.04  --abstr_ref_prep                        false
% 1.67/1.04  --abstr_ref_until_sat                   false
% 1.67/1.04  --abstr_ref_sig_restrict                funpre
% 1.67/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/1.04  --abstr_ref_under                       []
% 1.67/1.04  
% 1.67/1.04  ------ SAT Options
% 1.67/1.04  
% 1.67/1.04  --sat_mode                              false
% 1.67/1.04  --sat_fm_restart_options                ""
% 1.67/1.04  --sat_gr_def                            false
% 1.67/1.04  --sat_epr_types                         true
% 1.67/1.04  --sat_non_cyclic_types                  false
% 1.67/1.04  --sat_finite_models                     false
% 1.67/1.04  --sat_fm_lemmas                         false
% 1.67/1.04  --sat_fm_prep                           false
% 1.67/1.04  --sat_fm_uc_incr                        true
% 1.67/1.04  --sat_out_model                         small
% 1.67/1.04  --sat_out_clauses                       false
% 1.67/1.04  
% 1.67/1.04  ------ QBF Options
% 1.67/1.04  
% 1.67/1.04  --qbf_mode                              false
% 1.67/1.04  --qbf_elim_univ                         false
% 1.67/1.04  --qbf_dom_inst                          none
% 1.67/1.04  --qbf_dom_pre_inst                      false
% 1.67/1.04  --qbf_sk_in                             false
% 1.67/1.04  --qbf_pred_elim                         true
% 1.67/1.04  --qbf_split                             512
% 1.67/1.04  
% 1.67/1.04  ------ BMC1 Options
% 1.67/1.04  
% 1.67/1.04  --bmc1_incremental                      false
% 1.67/1.04  --bmc1_axioms                           reachable_all
% 1.67/1.04  --bmc1_min_bound                        0
% 1.67/1.04  --bmc1_max_bound                        -1
% 1.67/1.04  --bmc1_max_bound_default                -1
% 1.67/1.04  --bmc1_symbol_reachability              true
% 1.67/1.04  --bmc1_property_lemmas                  false
% 1.67/1.04  --bmc1_k_induction                      false
% 1.67/1.04  --bmc1_non_equiv_states                 false
% 1.67/1.04  --bmc1_deadlock                         false
% 1.67/1.04  --bmc1_ucm                              false
% 1.67/1.04  --bmc1_add_unsat_core                   none
% 1.67/1.04  --bmc1_unsat_core_children              false
% 1.67/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/1.04  --bmc1_out_stat                         full
% 1.67/1.04  --bmc1_ground_init                      false
% 1.67/1.04  --bmc1_pre_inst_next_state              false
% 1.67/1.04  --bmc1_pre_inst_state                   false
% 1.67/1.04  --bmc1_pre_inst_reach_state             false
% 1.67/1.04  --bmc1_out_unsat_core                   false
% 1.67/1.04  --bmc1_aig_witness_out                  false
% 1.67/1.04  --bmc1_verbose                          false
% 1.67/1.04  --bmc1_dump_clauses_tptp                false
% 1.67/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.67/1.04  --bmc1_dump_file                        -
% 1.67/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.67/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.67/1.04  --bmc1_ucm_extend_mode                  1
% 1.67/1.04  --bmc1_ucm_init_mode                    2
% 1.67/1.04  --bmc1_ucm_cone_mode                    none
% 1.67/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.67/1.04  --bmc1_ucm_relax_model                  4
% 1.67/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.67/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/1.04  --bmc1_ucm_layered_model                none
% 1.67/1.04  --bmc1_ucm_max_lemma_size               10
% 1.67/1.04  
% 1.67/1.04  ------ AIG Options
% 1.67/1.04  
% 1.67/1.04  --aig_mode                              false
% 1.67/1.04  
% 1.67/1.04  ------ Instantiation Options
% 1.67/1.04  
% 1.67/1.04  --instantiation_flag                    true
% 1.67/1.04  --inst_sos_flag                         false
% 1.67/1.04  --inst_sos_phase                        true
% 1.67/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/1.04  --inst_lit_sel_side                     num_symb
% 1.67/1.04  --inst_solver_per_active                1400
% 1.67/1.04  --inst_solver_calls_frac                1.
% 1.67/1.04  --inst_passive_queue_type               priority_queues
% 1.67/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.67/1.04  --inst_passive_queues_freq              [25;2]
% 1.67/1.04  --inst_dismatching                      true
% 1.67/1.04  --inst_eager_unprocessed_to_passive     true
% 1.67/1.04  --inst_prop_sim_given                   true
% 1.67/1.04  --inst_prop_sim_new                     false
% 1.67/1.04  --inst_subs_new                         false
% 1.67/1.04  --inst_eq_res_simp                      false
% 1.67/1.04  --inst_subs_given                       false
% 1.67/1.04  --inst_orphan_elimination               true
% 1.67/1.04  --inst_learning_loop_flag               true
% 1.67/1.04  --inst_learning_start                   3000
% 1.67/1.04  --inst_learning_factor                  2
% 1.67/1.04  --inst_start_prop_sim_after_learn       3
% 1.67/1.04  --inst_sel_renew                        solver
% 1.67/1.04  --inst_lit_activity_flag                true
% 1.67/1.04  --inst_restr_to_given                   false
% 1.67/1.04  --inst_activity_threshold               500
% 1.67/1.04  --inst_out_proof                        true
% 1.67/1.04  
% 1.67/1.04  ------ Resolution Options
% 1.67/1.04  
% 1.67/1.04  --resolution_flag                       true
% 1.67/1.04  --res_lit_sel                           adaptive
% 1.67/1.04  --res_lit_sel_side                      none
% 1.67/1.04  --res_ordering                          kbo
% 1.67/1.04  --res_to_prop_solver                    active
% 1.67/1.04  --res_prop_simpl_new                    false
% 1.67/1.04  --res_prop_simpl_given                  true
% 1.67/1.04  --res_passive_queue_type                priority_queues
% 1.67/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.67/1.04  --res_passive_queues_freq               [15;5]
% 1.67/1.04  --res_forward_subs                      full
% 1.67/1.04  --res_backward_subs                     full
% 1.67/1.04  --res_forward_subs_resolution           true
% 1.67/1.04  --res_backward_subs_resolution          true
% 1.67/1.04  --res_orphan_elimination                true
% 1.67/1.04  --res_time_limit                        2.
% 1.67/1.04  --res_out_proof                         true
% 1.67/1.04  
% 1.67/1.04  ------ Superposition Options
% 1.67/1.04  
% 1.67/1.04  --superposition_flag                    true
% 1.67/1.04  --sup_passive_queue_type                priority_queues
% 1.67/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.67/1.04  --demod_completeness_check              fast
% 1.67/1.04  --demod_use_ground                      true
% 1.67/1.04  --sup_to_prop_solver                    passive
% 1.67/1.04  --sup_prop_simpl_new                    true
% 1.67/1.04  --sup_prop_simpl_given                  true
% 1.67/1.04  --sup_fun_splitting                     false
% 1.67/1.04  --sup_smt_interval                      50000
% 1.67/1.04  
% 1.67/1.04  ------ Superposition Simplification Setup
% 1.67/1.04  
% 1.67/1.04  --sup_indices_passive                   []
% 1.67/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.04  --sup_full_bw                           [BwDemod]
% 1.67/1.04  --sup_immed_triv                        [TrivRules]
% 1.67/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.04  --sup_immed_bw_main                     []
% 1.67/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.04  
% 1.67/1.04  ------ Combination Options
% 1.67/1.04  
% 1.67/1.04  --comb_res_mult                         3
% 1.67/1.04  --comb_sup_mult                         2
% 1.67/1.04  --comb_inst_mult                        10
% 1.67/1.04  
% 1.67/1.04  ------ Debug Options
% 1.67/1.04  
% 1.67/1.04  --dbg_backtrace                         false
% 1.67/1.04  --dbg_dump_prop_clauses                 false
% 1.67/1.04  --dbg_dump_prop_clauses_file            -
% 1.67/1.04  --dbg_out_stat                          false
% 1.67/1.04  ------ Parsing...
% 1.67/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.67/1.04  
% 1.67/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.67/1.04  
% 1.67/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.67/1.04  
% 1.67/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.67/1.04  ------ Proving...
% 1.67/1.04  ------ Problem Properties 
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  clauses                                 16
% 1.67/1.04  conjectures                             3
% 1.67/1.04  EPR                                     7
% 1.67/1.04  Horn                                    14
% 1.67/1.04  unary                                   4
% 1.67/1.04  binary                                  5
% 1.67/1.04  lits                                    47
% 1.67/1.04  lits eq                                 1
% 1.67/1.04  fd_pure                                 0
% 1.67/1.04  fd_pseudo                               0
% 1.67/1.04  fd_cond                                 0
% 1.67/1.04  fd_pseudo_cond                          0
% 1.67/1.04  AC symbols                              0
% 1.67/1.04  
% 1.67/1.04  ------ Schedule dynamic 5 is on 
% 1.67/1.04  
% 1.67/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  ------ 
% 1.67/1.04  Current options:
% 1.67/1.04  ------ 
% 1.67/1.04  
% 1.67/1.04  ------ Input Options
% 1.67/1.04  
% 1.67/1.04  --out_options                           all
% 1.67/1.04  --tptp_safe_out                         true
% 1.67/1.04  --problem_path                          ""
% 1.67/1.04  --include_path                          ""
% 1.67/1.04  --clausifier                            res/vclausify_rel
% 1.67/1.04  --clausifier_options                    --mode clausify
% 1.67/1.04  --stdin                                 false
% 1.67/1.04  --stats_out                             all
% 1.67/1.04  
% 1.67/1.04  ------ General Options
% 1.67/1.04  
% 1.67/1.04  --fof                                   false
% 1.67/1.04  --time_out_real                         305.
% 1.67/1.04  --time_out_virtual                      -1.
% 1.67/1.04  --symbol_type_check                     false
% 1.67/1.04  --clausify_out                          false
% 1.67/1.04  --sig_cnt_out                           false
% 1.67/1.04  --trig_cnt_out                          false
% 1.67/1.04  --trig_cnt_out_tolerance                1.
% 1.67/1.04  --trig_cnt_out_sk_spl                   false
% 1.67/1.04  --abstr_cl_out                          false
% 1.67/1.04  
% 1.67/1.04  ------ Global Options
% 1.67/1.04  
% 1.67/1.04  --schedule                              default
% 1.67/1.04  --add_important_lit                     false
% 1.67/1.04  --prop_solver_per_cl                    1000
% 1.67/1.04  --min_unsat_core                        false
% 1.67/1.04  --soft_assumptions                      false
% 1.67/1.04  --soft_lemma_size                       3
% 1.67/1.04  --prop_impl_unit_size                   0
% 1.67/1.04  --prop_impl_unit                        []
% 1.67/1.04  --share_sel_clauses                     true
% 1.67/1.04  --reset_solvers                         false
% 1.67/1.04  --bc_imp_inh                            [conj_cone]
% 1.67/1.04  --conj_cone_tolerance                   3.
% 1.67/1.04  --extra_neg_conj                        none
% 1.67/1.04  --large_theory_mode                     true
% 1.67/1.04  --prolific_symb_bound                   200
% 1.67/1.04  --lt_threshold                          2000
% 1.67/1.04  --clause_weak_htbl                      true
% 1.67/1.04  --gc_record_bc_elim                     false
% 1.67/1.04  
% 1.67/1.04  ------ Preprocessing Options
% 1.67/1.04  
% 1.67/1.04  --preprocessing_flag                    true
% 1.67/1.04  --time_out_prep_mult                    0.1
% 1.67/1.04  --splitting_mode                        input
% 1.67/1.04  --splitting_grd                         true
% 1.67/1.04  --splitting_cvd                         false
% 1.67/1.04  --splitting_cvd_svl                     false
% 1.67/1.04  --splitting_nvd                         32
% 1.67/1.04  --sub_typing                            true
% 1.67/1.04  --prep_gs_sim                           true
% 1.67/1.04  --prep_unflatten                        true
% 1.67/1.04  --prep_res_sim                          true
% 1.67/1.04  --prep_upred                            true
% 1.67/1.04  --prep_sem_filter                       exhaustive
% 1.67/1.04  --prep_sem_filter_out                   false
% 1.67/1.04  --pred_elim                             true
% 1.67/1.04  --res_sim_input                         true
% 1.67/1.04  --eq_ax_congr_red                       true
% 1.67/1.04  --pure_diseq_elim                       true
% 1.67/1.04  --brand_transform                       false
% 1.67/1.04  --non_eq_to_eq                          false
% 1.67/1.04  --prep_def_merge                        true
% 1.67/1.04  --prep_def_merge_prop_impl              false
% 1.67/1.04  --prep_def_merge_mbd                    true
% 1.67/1.04  --prep_def_merge_tr_red                 false
% 1.67/1.04  --prep_def_merge_tr_cl                  false
% 1.67/1.04  --smt_preprocessing                     true
% 1.67/1.04  --smt_ac_axioms                         fast
% 1.67/1.04  --preprocessed_out                      false
% 1.67/1.04  --preprocessed_stats                    false
% 1.67/1.04  
% 1.67/1.04  ------ Abstraction refinement Options
% 1.67/1.04  
% 1.67/1.04  --abstr_ref                             []
% 1.67/1.04  --abstr_ref_prep                        false
% 1.67/1.04  --abstr_ref_until_sat                   false
% 1.67/1.04  --abstr_ref_sig_restrict                funpre
% 1.67/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/1.04  --abstr_ref_under                       []
% 1.67/1.04  
% 1.67/1.04  ------ SAT Options
% 1.67/1.04  
% 1.67/1.04  --sat_mode                              false
% 1.67/1.04  --sat_fm_restart_options                ""
% 1.67/1.04  --sat_gr_def                            false
% 1.67/1.04  --sat_epr_types                         true
% 1.67/1.04  --sat_non_cyclic_types                  false
% 1.67/1.04  --sat_finite_models                     false
% 1.67/1.04  --sat_fm_lemmas                         false
% 1.67/1.04  --sat_fm_prep                           false
% 1.67/1.04  --sat_fm_uc_incr                        true
% 1.67/1.04  --sat_out_model                         small
% 1.67/1.04  --sat_out_clauses                       false
% 1.67/1.04  
% 1.67/1.04  ------ QBF Options
% 1.67/1.04  
% 1.67/1.04  --qbf_mode                              false
% 1.67/1.04  --qbf_elim_univ                         false
% 1.67/1.04  --qbf_dom_inst                          none
% 1.67/1.04  --qbf_dom_pre_inst                      false
% 1.67/1.04  --qbf_sk_in                             false
% 1.67/1.04  --qbf_pred_elim                         true
% 1.67/1.04  --qbf_split                             512
% 1.67/1.04  
% 1.67/1.04  ------ BMC1 Options
% 1.67/1.04  
% 1.67/1.04  --bmc1_incremental                      false
% 1.67/1.04  --bmc1_axioms                           reachable_all
% 1.67/1.04  --bmc1_min_bound                        0
% 1.67/1.04  --bmc1_max_bound                        -1
% 1.67/1.04  --bmc1_max_bound_default                -1
% 1.67/1.04  --bmc1_symbol_reachability              true
% 1.67/1.04  --bmc1_property_lemmas                  false
% 1.67/1.04  --bmc1_k_induction                      false
% 1.67/1.04  --bmc1_non_equiv_states                 false
% 1.67/1.04  --bmc1_deadlock                         false
% 1.67/1.04  --bmc1_ucm                              false
% 1.67/1.04  --bmc1_add_unsat_core                   none
% 1.67/1.04  --bmc1_unsat_core_children              false
% 1.67/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/1.04  --bmc1_out_stat                         full
% 1.67/1.04  --bmc1_ground_init                      false
% 1.67/1.04  --bmc1_pre_inst_next_state              false
% 1.67/1.04  --bmc1_pre_inst_state                   false
% 1.67/1.04  --bmc1_pre_inst_reach_state             false
% 1.67/1.04  --bmc1_out_unsat_core                   false
% 1.67/1.04  --bmc1_aig_witness_out                  false
% 1.67/1.04  --bmc1_verbose                          false
% 1.67/1.04  --bmc1_dump_clauses_tptp                false
% 1.67/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.67/1.04  --bmc1_dump_file                        -
% 1.67/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.67/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.67/1.04  --bmc1_ucm_extend_mode                  1
% 1.67/1.04  --bmc1_ucm_init_mode                    2
% 1.67/1.04  --bmc1_ucm_cone_mode                    none
% 1.67/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.67/1.04  --bmc1_ucm_relax_model                  4
% 1.67/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.67/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/1.04  --bmc1_ucm_layered_model                none
% 1.67/1.04  --bmc1_ucm_max_lemma_size               10
% 1.67/1.04  
% 1.67/1.04  ------ AIG Options
% 1.67/1.04  
% 1.67/1.04  --aig_mode                              false
% 1.67/1.04  
% 1.67/1.04  ------ Instantiation Options
% 1.67/1.04  
% 1.67/1.04  --instantiation_flag                    true
% 1.67/1.04  --inst_sos_flag                         false
% 1.67/1.04  --inst_sos_phase                        true
% 1.67/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/1.04  --inst_lit_sel_side                     none
% 1.67/1.04  --inst_solver_per_active                1400
% 1.67/1.04  --inst_solver_calls_frac                1.
% 1.67/1.04  --inst_passive_queue_type               priority_queues
% 1.67/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.67/1.04  --inst_passive_queues_freq              [25;2]
% 1.67/1.04  --inst_dismatching                      true
% 1.67/1.04  --inst_eager_unprocessed_to_passive     true
% 1.67/1.04  --inst_prop_sim_given                   true
% 1.67/1.04  --inst_prop_sim_new                     false
% 1.67/1.04  --inst_subs_new                         false
% 1.67/1.04  --inst_eq_res_simp                      false
% 1.67/1.04  --inst_subs_given                       false
% 1.67/1.04  --inst_orphan_elimination               true
% 1.67/1.04  --inst_learning_loop_flag               true
% 1.67/1.04  --inst_learning_start                   3000
% 1.67/1.04  --inst_learning_factor                  2
% 1.67/1.04  --inst_start_prop_sim_after_learn       3
% 1.67/1.04  --inst_sel_renew                        solver
% 1.67/1.04  --inst_lit_activity_flag                true
% 1.67/1.04  --inst_restr_to_given                   false
% 1.67/1.04  --inst_activity_threshold               500
% 1.67/1.04  --inst_out_proof                        true
% 1.67/1.04  
% 1.67/1.04  ------ Resolution Options
% 1.67/1.04  
% 1.67/1.04  --resolution_flag                       false
% 1.67/1.04  --res_lit_sel                           adaptive
% 1.67/1.04  --res_lit_sel_side                      none
% 1.67/1.04  --res_ordering                          kbo
% 1.67/1.04  --res_to_prop_solver                    active
% 1.67/1.04  --res_prop_simpl_new                    false
% 1.67/1.04  --res_prop_simpl_given                  true
% 1.67/1.04  --res_passive_queue_type                priority_queues
% 1.67/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.67/1.04  --res_passive_queues_freq               [15;5]
% 1.67/1.04  --res_forward_subs                      full
% 1.67/1.04  --res_backward_subs                     full
% 1.67/1.04  --res_forward_subs_resolution           true
% 1.67/1.04  --res_backward_subs_resolution          true
% 1.67/1.04  --res_orphan_elimination                true
% 1.67/1.04  --res_time_limit                        2.
% 1.67/1.04  --res_out_proof                         true
% 1.67/1.04  
% 1.67/1.04  ------ Superposition Options
% 1.67/1.04  
% 1.67/1.04  --superposition_flag                    true
% 1.67/1.04  --sup_passive_queue_type                priority_queues
% 1.67/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.67/1.04  --demod_completeness_check              fast
% 1.67/1.04  --demod_use_ground                      true
% 1.67/1.04  --sup_to_prop_solver                    passive
% 1.67/1.04  --sup_prop_simpl_new                    true
% 1.67/1.04  --sup_prop_simpl_given                  true
% 1.67/1.04  --sup_fun_splitting                     false
% 1.67/1.04  --sup_smt_interval                      50000
% 1.67/1.04  
% 1.67/1.04  ------ Superposition Simplification Setup
% 1.67/1.04  
% 1.67/1.04  --sup_indices_passive                   []
% 1.67/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.04  --sup_full_bw                           [BwDemod]
% 1.67/1.04  --sup_immed_triv                        [TrivRules]
% 1.67/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.04  --sup_immed_bw_main                     []
% 1.67/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/1.04  
% 1.67/1.04  ------ Combination Options
% 1.67/1.04  
% 1.67/1.04  --comb_res_mult                         3
% 1.67/1.04  --comb_sup_mult                         2
% 1.67/1.04  --comb_inst_mult                        10
% 1.67/1.04  
% 1.67/1.04  ------ Debug Options
% 1.67/1.04  
% 1.67/1.04  --dbg_backtrace                         false
% 1.67/1.04  --dbg_dump_prop_clauses                 false
% 1.67/1.04  --dbg_dump_prop_clauses_file            -
% 1.67/1.04  --dbg_out_stat                          false
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  ------ Proving...
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  % SZS status Theorem for theBenchmark.p
% 1.67/1.04  
% 1.67/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.67/1.04  
% 1.67/1.04  fof(f1,axiom,(
% 1.67/1.04    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f18,plain,(
% 1.67/1.04    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.67/1.04    inference(nnf_transformation,[],[f1])).
% 1.67/1.04  
% 1.67/1.04  fof(f19,plain,(
% 1.67/1.04    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.67/1.04    inference(rectify,[],[f18])).
% 1.67/1.04  
% 1.67/1.04  fof(f20,plain,(
% 1.67/1.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.67/1.04    introduced(choice_axiom,[])).
% 1.67/1.04  
% 1.67/1.04  fof(f21,plain,(
% 1.67/1.04    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.67/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 1.67/1.04  
% 1.67/1.04  fof(f32,plain,(
% 1.67/1.04    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.67/1.04    inference(cnf_transformation,[],[f21])).
% 1.67/1.04  
% 1.67/1.04  fof(f4,axiom,(
% 1.67/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f11,plain,(
% 1.67/1.04    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.67/1.04    inference(ennf_transformation,[],[f4])).
% 1.67/1.04  
% 1.67/1.04  fof(f22,plain,(
% 1.67/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.67/1.04    inference(nnf_transformation,[],[f11])).
% 1.67/1.04  
% 1.67/1.04  fof(f23,plain,(
% 1.67/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.67/1.04    inference(rectify,[],[f22])).
% 1.67/1.04  
% 1.67/1.04  fof(f24,plain,(
% 1.67/1.04    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 1.67/1.04    introduced(choice_axiom,[])).
% 1.67/1.04  
% 1.67/1.04  fof(f25,plain,(
% 1.67/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.67/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 1.67/1.04  
% 1.67/1.04  fof(f37,plain,(
% 1.67/1.04    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.67/1.04    inference(cnf_transformation,[],[f25])).
% 1.67/1.04  
% 1.67/1.04  fof(f5,axiom,(
% 1.67/1.04    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f12,plain,(
% 1.67/1.04    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.67/1.04    inference(ennf_transformation,[],[f5])).
% 1.67/1.04  
% 1.67/1.04  fof(f40,plain,(
% 1.67/1.04    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.67/1.04    inference(cnf_transformation,[],[f12])).
% 1.67/1.04  
% 1.67/1.04  fof(f7,axiom,(
% 1.67/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f14,plain,(
% 1.67/1.04    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.67/1.04    inference(ennf_transformation,[],[f7])).
% 1.67/1.04  
% 1.67/1.04  fof(f15,plain,(
% 1.67/1.04    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.67/1.04    inference(flattening,[],[f14])).
% 1.67/1.04  
% 1.67/1.04  fof(f26,plain,(
% 1.67/1.04    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.67/1.04    inference(nnf_transformation,[],[f15])).
% 1.67/1.04  
% 1.67/1.04  fof(f27,plain,(
% 1.67/1.04    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.67/1.04    inference(rectify,[],[f26])).
% 1.67/1.04  
% 1.67/1.04  fof(f28,plain,(
% 1.67/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK2(X0,X1)),k1_funct_1(X0,sK2(X0,X1))) & r2_hidden(sK2(X0,X1),k1_relat_1(X1))))),
% 1.67/1.04    introduced(choice_axiom,[])).
% 1.67/1.04  
% 1.67/1.04  fof(f29,plain,(
% 1.67/1.04    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK2(X0,X1)),k1_funct_1(X0,sK2(X0,X1))) & r2_hidden(sK2(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.67/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.67/1.04  
% 1.67/1.04  fof(f43,plain,(
% 1.67/1.04    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK2(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.67/1.04    inference(cnf_transformation,[],[f29])).
% 1.67/1.04  
% 1.67/1.04  fof(f8,conjecture,(
% 1.67/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f9,negated_conjecture,(
% 1.67/1.04    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.67/1.04    inference(negated_conjecture,[],[f8])).
% 1.67/1.04  
% 1.67/1.04  fof(f16,plain,(
% 1.67/1.04    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.67/1.04    inference(ennf_transformation,[],[f9])).
% 1.67/1.04  
% 1.67/1.04  fof(f17,plain,(
% 1.67/1.04    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.67/1.04    inference(flattening,[],[f16])).
% 1.67/1.04  
% 1.67/1.04  fof(f30,plain,(
% 1.67/1.04    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 1.67/1.04    introduced(choice_axiom,[])).
% 1.67/1.04  
% 1.67/1.04  fof(f31,plain,(
% 1.67/1.04    ~v5_funct_1(k1_xboole_0,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 1.67/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f30])).
% 1.67/1.04  
% 1.67/1.04  fof(f47,plain,(
% 1.67/1.04    ~v5_funct_1(k1_xboole_0,sK3)),
% 1.67/1.04    inference(cnf_transformation,[],[f31])).
% 1.67/1.04  
% 1.67/1.04  fof(f3,axiom,(
% 1.67/1.04    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f10,plain,(
% 1.67/1.04    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.67/1.04    inference(ennf_transformation,[],[f3])).
% 1.67/1.04  
% 1.67/1.04  fof(f35,plain,(
% 1.67/1.04    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.67/1.04    inference(cnf_transformation,[],[f10])).
% 1.67/1.04  
% 1.67/1.04  fof(f2,axiom,(
% 1.67/1.04    v1_xboole_0(k1_xboole_0)),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f34,plain,(
% 1.67/1.04    v1_xboole_0(k1_xboole_0)),
% 1.67/1.04    inference(cnf_transformation,[],[f2])).
% 1.67/1.04  
% 1.67/1.04  fof(f6,axiom,(
% 1.67/1.04    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/1.04  
% 1.67/1.04  fof(f13,plain,(
% 1.67/1.04    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.67/1.04    inference(ennf_transformation,[],[f6])).
% 1.67/1.04  
% 1.67/1.04  fof(f41,plain,(
% 1.67/1.04    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.67/1.04    inference(cnf_transformation,[],[f13])).
% 1.67/1.04  
% 1.67/1.04  fof(f46,plain,(
% 1.67/1.04    v1_funct_1(sK3)),
% 1.67/1.04    inference(cnf_transformation,[],[f31])).
% 1.67/1.04  
% 1.67/1.04  fof(f45,plain,(
% 1.67/1.04    v1_relat_1(sK3)),
% 1.67/1.04    inference(cnf_transformation,[],[f31])).
% 1.67/1.04  
% 1.67/1.04  cnf(c_1,plain,
% 1.67/1.04      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.67/1.04      inference(cnf_transformation,[],[f32]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_1091,plain,
% 1.67/1.04      ( ~ r2_hidden(k4_tarski(sK2(sK3,k1_xboole_0),sK1(sK2(sK3,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
% 1.67/1.04      | ~ v1_xboole_0(k1_xboole_0) ),
% 1.67/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_6,plain,
% 1.67/1.04      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 1.67/1.04      | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
% 1.67/1.04      | ~ v1_relat_1(X1) ),
% 1.67/1.04      inference(cnf_transformation,[],[f37]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_980,plain,
% 1.67/1.04      ( ~ r2_hidden(sK2(sK3,k1_xboole_0),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
% 1.67/1.04      | r2_hidden(k4_tarski(sK2(sK3,k1_xboole_0),sK1(sK2(sK3,k1_xboole_0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
% 1.67/1.04      | ~ v1_relat_1(k1_xboole_0) ),
% 1.67/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_333,plain,( X0 = X0 ),theory(equality) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_921,plain,
% 1.67/1.04      ( sK2(sK3,k1_xboole_0) = sK2(sK3,k1_xboole_0) ),
% 1.67/1.04      inference(instantiation,[status(thm)],[c_333]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_336,plain,
% 1.67/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.67/1.04      theory(equality) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_823,plain,
% 1.67/1.04      ( r2_hidden(X0,X1)
% 1.67/1.04      | ~ r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 1.67/1.04      | X0 != sK2(sK3,k1_xboole_0)
% 1.67/1.04      | X1 != k1_relat_1(k1_xboole_0) ),
% 1.67/1.04      inference(instantiation,[status(thm)],[c_336]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_869,plain,
% 1.67/1.04      ( r2_hidden(X0,k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
% 1.67/1.04      | ~ r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 1.67/1.04      | X0 != sK2(sK3,k1_xboole_0)
% 1.67/1.04      | k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) != k1_relat_1(k1_xboole_0) ),
% 1.67/1.04      inference(instantiation,[status(thm)],[c_823]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_920,plain,
% 1.67/1.04      ( r2_hidden(sK2(sK3,k1_xboole_0),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))
% 1.67/1.04      | ~ r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 1.67/1.04      | sK2(sK3,k1_xboole_0) != sK2(sK3,k1_xboole_0)
% 1.67/1.04      | k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) != k1_relat_1(k1_xboole_0) ),
% 1.67/1.04      inference(instantiation,[status(thm)],[c_869]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_8,plain,
% 1.67/1.04      ( ~ v1_relat_1(X0)
% 1.67/1.04      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 1.67/1.04      inference(cnf_transformation,[],[f40]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_870,plain,
% 1.67/1.04      ( ~ v1_relat_1(k1_xboole_0)
% 1.67/1.04      | k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 1.67/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_11,plain,
% 1.67/1.04      ( v5_funct_1(X0,X1)
% 1.67/1.04      | r2_hidden(sK2(X1,X0),k1_relat_1(X0))
% 1.67/1.04      | ~ v1_funct_1(X0)
% 1.67/1.04      | ~ v1_funct_1(X1)
% 1.67/1.04      | ~ v1_relat_1(X1)
% 1.67/1.04      | ~ v1_relat_1(X0) ),
% 1.67/1.04      inference(cnf_transformation,[],[f43]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_13,negated_conjecture,
% 1.67/1.04      ( ~ v5_funct_1(k1_xboole_0,sK3) ),
% 1.67/1.04      inference(cnf_transformation,[],[f47]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_294,plain,
% 1.67/1.04      ( r2_hidden(sK2(X0,X1),k1_relat_1(X1))
% 1.67/1.04      | ~ v1_funct_1(X1)
% 1.67/1.04      | ~ v1_funct_1(X0)
% 1.67/1.04      | ~ v1_relat_1(X0)
% 1.67/1.04      | ~ v1_relat_1(X1)
% 1.67/1.04      | sK3 != X0
% 1.67/1.04      | k1_xboole_0 != X1 ),
% 1.67/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_295,plain,
% 1.67/1.04      ( r2_hidden(sK2(sK3,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 1.67/1.04      | ~ v1_funct_1(sK3)
% 1.67/1.04      | ~ v1_funct_1(k1_xboole_0)
% 1.67/1.04      | ~ v1_relat_1(sK3)
% 1.67/1.04      | ~ v1_relat_1(k1_xboole_0) ),
% 1.67/1.04      inference(unflattening,[status(thm)],[c_294]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_3,plain,
% 1.67/1.04      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 1.67/1.04      inference(cnf_transformation,[],[f35]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_2,plain,
% 1.67/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 1.67/1.04      inference(cnf_transformation,[],[f34]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_217,plain,
% 1.67/1.04      ( v1_relat_1(X0) | k1_xboole_0 != X0 ),
% 1.67/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_2]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_218,plain,
% 1.67/1.04      ( v1_relat_1(k1_xboole_0) ),
% 1.67/1.04      inference(unflattening,[status(thm)],[c_217]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_9,plain,
% 1.67/1.04      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 1.67/1.04      inference(cnf_transformation,[],[f41]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_210,plain,
% 1.67/1.04      ( v1_funct_1(X0) | k1_xboole_0 != X0 ),
% 1.67/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_2]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_211,plain,
% 1.67/1.04      ( v1_funct_1(k1_xboole_0) ),
% 1.67/1.04      inference(unflattening,[status(thm)],[c_210]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_14,negated_conjecture,
% 1.67/1.04      ( v1_funct_1(sK3) ),
% 1.67/1.04      inference(cnf_transformation,[],[f46]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(c_15,negated_conjecture,
% 1.67/1.04      ( v1_relat_1(sK3) ),
% 1.67/1.04      inference(cnf_transformation,[],[f45]) ).
% 1.67/1.04  
% 1.67/1.04  cnf(contradiction,plain,
% 1.67/1.04      ( $false ),
% 1.67/1.04      inference(minisat,
% 1.67/1.04                [status(thm)],
% 1.67/1.04                [c_1091,c_980,c_921,c_920,c_870,c_295,c_218,c_211,c_2,
% 1.67/1.04                 c_14,c_15]) ).
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.67/1.04  
% 1.67/1.04  ------                               Statistics
% 1.67/1.04  
% 1.67/1.04  ------ General
% 1.67/1.04  
% 1.67/1.04  abstr_ref_over_cycles:                  0
% 1.67/1.04  abstr_ref_under_cycles:                 0
% 1.67/1.04  gc_basic_clause_elim:                   0
% 1.67/1.04  forced_gc_time:                         0
% 1.67/1.04  parsing_time:                           0.009
% 1.67/1.04  unif_index_cands_time:                  0.
% 1.67/1.04  unif_index_add_time:                    0.
% 1.67/1.04  orderings_time:                         0.
% 1.67/1.04  out_proof_time:                         0.009
% 1.67/1.04  total_time:                             0.064
% 1.67/1.04  num_of_symbols:                         46
% 1.67/1.04  num_of_terms:                           724
% 1.67/1.04  
% 1.67/1.04  ------ Preprocessing
% 1.67/1.04  
% 1.67/1.04  num_of_splits:                          0
% 1.67/1.04  num_of_split_atoms:                     0
% 1.67/1.04  num_of_reused_defs:                     0
% 1.67/1.04  num_eq_ax_congr_red:                    22
% 1.67/1.04  num_of_sem_filtered_clauses:            1
% 1.67/1.04  num_of_subtypes:                        1
% 1.67/1.04  monotx_restored_types:                  0
% 1.67/1.04  sat_num_of_epr_types:                   0
% 1.67/1.04  sat_num_of_non_cyclic_types:            0
% 1.67/1.04  sat_guarded_non_collapsed_types:        0
% 1.67/1.04  num_pure_diseq_elim:                    0
% 1.67/1.04  simp_replaced_by:                       0
% 1.67/1.04  res_preprocessed:                       69
% 1.67/1.04  prep_upred:                             0
% 1.67/1.04  prep_unflattend:                        8
% 1.67/1.04  smt_new_axioms:                         0
% 1.67/1.04  pred_elim_cands:                        5
% 1.67/1.04  pred_elim:                              0
% 1.67/1.04  pred_elim_cl:                           0
% 1.67/1.04  pred_elim_cycles:                       2
% 1.67/1.04  merged_defs:                            0
% 1.67/1.04  merged_defs_ncl:                        0
% 1.67/1.04  bin_hyper_res:                          0
% 1.67/1.04  prep_cycles:                            3
% 1.67/1.04  pred_elim_time:                         0.003
% 1.67/1.04  splitting_time:                         0.
% 1.67/1.04  sem_filter_time:                        0.
% 1.67/1.04  monotx_time:                            0.
% 1.67/1.04  subtype_inf_time:                       0.
% 1.67/1.04  
% 1.67/1.04  ------ Problem properties
% 1.67/1.04  
% 1.67/1.04  clauses:                                16
% 1.67/1.04  conjectures:                            3
% 1.67/1.04  epr:                                    7
% 1.67/1.04  horn:                                   14
% 1.67/1.04  ground:                                 4
% 1.67/1.04  unary:                                  4
% 1.67/1.04  binary:                                 5
% 1.67/1.04  lits:                                   47
% 1.67/1.04  lits_eq:                                1
% 1.67/1.04  fd_pure:                                0
% 1.67/1.04  fd_pseudo:                              0
% 1.67/1.04  fd_cond:                                0
% 1.67/1.04  fd_pseudo_cond:                         0
% 1.67/1.04  ac_symbols:                             0
% 1.67/1.04  
% 1.67/1.04  ------ Propositional Solver
% 1.67/1.04  
% 1.67/1.04  prop_solver_calls:                      23
% 1.67/1.04  prop_fast_solver_calls:                 450
% 1.67/1.04  smt_solver_calls:                       0
% 1.67/1.04  smt_fast_solver_calls:                  0
% 1.67/1.04  prop_num_of_clauses:                    233
% 1.67/1.04  prop_preprocess_simplified:             2096
% 1.67/1.04  prop_fo_subsumed:                       8
% 1.67/1.04  prop_solver_time:                       0.
% 1.67/1.04  smt_solver_time:                        0.
% 1.67/1.04  smt_fast_solver_time:                   0.
% 1.67/1.04  prop_fast_solver_time:                  0.
% 1.67/1.04  prop_unsat_core_time:                   0.
% 1.67/1.04  
% 1.67/1.04  ------ QBF
% 1.67/1.04  
% 1.67/1.04  qbf_q_res:                              0
% 1.67/1.04  qbf_num_tautologies:                    0
% 1.67/1.04  qbf_prep_cycles:                        0
% 1.67/1.04  
% 1.67/1.04  ------ BMC1
% 1.67/1.04  
% 1.67/1.04  bmc1_current_bound:                     -1
% 1.67/1.04  bmc1_last_solved_bound:                 -1
% 1.67/1.04  bmc1_unsat_core_size:                   -1
% 1.67/1.04  bmc1_unsat_core_parents_size:           -1
% 1.67/1.04  bmc1_merge_next_fun:                    0
% 1.67/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.67/1.04  
% 1.67/1.04  ------ Instantiation
% 1.67/1.04  
% 1.67/1.04  inst_num_of_clauses:                    79
% 1.67/1.04  inst_num_in_passive:                    4
% 1.67/1.04  inst_num_in_active:                     65
% 1.67/1.04  inst_num_in_unprocessed:                9
% 1.67/1.04  inst_num_of_loops:                      70
% 1.67/1.04  inst_num_of_learning_restarts:          0
% 1.67/1.04  inst_num_moves_active_passive:          0
% 1.67/1.04  inst_lit_activity:                      0
% 1.67/1.04  inst_lit_activity_moves:                0
% 1.67/1.04  inst_num_tautologies:                   0
% 1.67/1.04  inst_num_prop_implied:                  0
% 1.67/1.04  inst_num_existing_simplified:           0
% 1.67/1.04  inst_num_eq_res_simplified:             0
% 1.67/1.04  inst_num_child_elim:                    0
% 1.67/1.04  inst_num_of_dismatching_blockings:      0
% 1.67/1.04  inst_num_of_non_proper_insts:           59
% 1.67/1.04  inst_num_of_duplicates:                 0
% 1.67/1.04  inst_inst_num_from_inst_to_res:         0
% 1.67/1.04  inst_dismatching_checking_time:         0.
% 1.67/1.04  
% 1.67/1.04  ------ Resolution
% 1.67/1.04  
% 1.67/1.04  res_num_of_clauses:                     0
% 1.67/1.04  res_num_in_passive:                     0
% 1.67/1.04  res_num_in_active:                      0
% 1.67/1.04  res_num_of_loops:                       72
% 1.67/1.04  res_forward_subset_subsumed:            4
% 1.67/1.04  res_backward_subset_subsumed:           0
% 1.67/1.04  res_forward_subsumed:                   0
% 1.67/1.04  res_backward_subsumed:                  0
% 1.67/1.04  res_forward_subsumption_resolution:     0
% 1.67/1.04  res_backward_subsumption_resolution:    0
% 1.67/1.04  res_clause_to_clause_subsumption:       27
% 1.67/1.04  res_orphan_elimination:                 0
% 1.67/1.04  res_tautology_del:                      11
% 1.67/1.04  res_num_eq_res_simplified:              0
% 1.67/1.04  res_num_sel_changes:                    0
% 1.67/1.04  res_moves_from_active_to_pass:          0
% 1.67/1.04  
% 1.67/1.04  ------ Superposition
% 1.67/1.04  
% 1.67/1.04  sup_time_total:                         0.
% 1.67/1.04  sup_time_generating:                    0.
% 1.67/1.04  sup_time_sim_full:                      0.
% 1.67/1.04  sup_time_sim_immed:                     0.
% 1.67/1.04  
% 1.67/1.04  sup_num_of_clauses:                     21
% 1.67/1.04  sup_num_in_active:                      12
% 1.67/1.04  sup_num_in_passive:                     9
% 1.67/1.04  sup_num_of_loops:                       12
% 1.67/1.04  sup_fw_superposition:                   6
% 1.67/1.04  sup_bw_superposition:                   0
% 1.67/1.04  sup_immediate_simplified:               0
% 1.67/1.04  sup_given_eliminated:                   0
% 1.67/1.04  comparisons_done:                       0
% 1.67/1.04  comparisons_avoided:                    0
% 1.67/1.04  
% 1.67/1.04  ------ Simplifications
% 1.67/1.04  
% 1.67/1.04  
% 1.67/1.04  sim_fw_subset_subsumed:                 0
% 1.67/1.04  sim_bw_subset_subsumed:                 0
% 1.67/1.04  sim_fw_subsumed:                        0
% 1.67/1.04  sim_bw_subsumed:                        0
% 1.67/1.04  sim_fw_subsumption_res:                 0
% 1.67/1.04  sim_bw_subsumption_res:                 0
% 1.67/1.04  sim_tautology_del:                      1
% 1.67/1.04  sim_eq_tautology_del:                   0
% 1.67/1.04  sim_eq_res_simp:                        0
% 1.67/1.04  sim_fw_demodulated:                     0
% 1.67/1.04  sim_bw_demodulated:                     0
% 1.67/1.04  sim_light_normalised:                   0
% 1.67/1.04  sim_joinable_taut:                      0
% 1.67/1.04  sim_joinable_simp:                      0
% 1.67/1.04  sim_ac_normalised:                      0
% 1.67/1.04  sim_smt_subsumption:                    0
% 1.67/1.04  
%------------------------------------------------------------------------------
