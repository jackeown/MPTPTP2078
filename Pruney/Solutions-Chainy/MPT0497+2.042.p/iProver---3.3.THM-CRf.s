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
% DateTime   : Thu Dec  3 11:44:54 EST 2020

% Result     : Theorem 19.74s
% Output     : CNFRefutation 19.74s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 260 expanded)
%              Number of clauses        :  101 ( 122 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  419 ( 860 expanded)
%              Number of equality atoms :  118 ( 220 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 != k7_relat_1(sK2,sK1) )
      & ( r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 = k7_relat_1(sK2,sK1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 != k7_relat_1(sK2,sK1) )
    & ( r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 = k7_relat_1(sK2,sK1) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f37])).

fof(f59,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_493,plain,
    ( ~ r2_hidden(X0_45,X0_43)
    | r2_hidden(X1_45,X1_43)
    | X1_45 != X0_45
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_63459,plain,
    ( r2_hidden(X0_45,X0_43)
    | ~ r2_hidden(X1_45,k1_relat_1(k7_relat_1(X1_43,X2_43)))
    | X0_45 != X1_45
    | X0_43 != k1_relat_1(k7_relat_1(X1_43,X2_43)) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_67979,plain,
    ( r2_hidden(X0_45,X0_43)
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
    | X0_45 != sK0(k1_relat_1(sK2),sK1)
    | X0_43 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_63459])).

cnf(c_70372,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),X0_43)
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
    | sK0(k1_relat_1(sK2),sK1) != sK0(k1_relat_1(sK2),sK1)
    | X0_43 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_67979])).

cnf(c_70374,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_xboole_0)
    | sK0(k1_relat_1(sK2),sK1) != sK0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_70372])).

cnf(c_489,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_69454,plain,
    ( sK0(k1_relat_1(sK2),sK1) = sK0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_473,plain,
    ( ~ r2_hidden(X0_45,X0_43)
    | ~ r2_hidden(X0_45,k1_relat_1(X1_43))
    | r2_hidden(X0_45,k1_relat_1(k7_relat_1(X1_43,X0_43)))
    | ~ v1_relat_1(X1_43) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_63315,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(X0_43))
    | r2_hidden(X0_45,k1_relat_1(k7_relat_1(X0_43,sK1)))
    | ~ r2_hidden(X0_45,sK1)
    | ~ v1_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_65277,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(X0_43))
    | r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(X0_43,sK1)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | ~ v1_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_63315])).

cnf(c_65908,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_65277])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0_45,X0_43)
    | ~ r2_hidden(X0_45,X1_43)
    | ~ r1_xboole_0(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_65244,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),X0_43)
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r1_xboole_0(X0_43,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_65247,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_65244])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_470,plain,
    ( ~ v1_relat_1(X0_43)
    | k5_relat_1(k6_relat_1(X1_43),X0_43) = k7_relat_1(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_64073,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) = k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_477,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_xboole_0(X1_43)
    | v1_xboole_0(k7_relat_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_64001,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ v1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_491,plain,
    ( ~ v1_xboole_0(X0_43)
    | v1_xboole_0(X1_43)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_63574,plain,
    ( ~ v1_xboole_0(X0_43)
    | v1_xboole_0(k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)))
    | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) != X0_43 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_63742,plain,
    ( v1_xboole_0(k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)))
    | ~ v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))))
    | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) != k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_63574])).

cnf(c_63255,plain,
    ( ~ v1_xboole_0(X0_43)
    | v1_xboole_0(k7_relat_1(sK2,sK1))
    | k7_relat_1(sK2,sK1) != X0_43 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_63453,plain,
    ( ~ v1_xboole_0(k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)))
    | v1_xboole_0(k7_relat_1(sK2,sK1))
    | k7_relat_1(sK2,sK1) != k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_63255])).

cnf(c_490,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1434,plain,
    ( X0_43 != X1_43
    | X0_43 = k1_relat_1(X2_43)
    | k1_relat_1(X2_43) != X1_43 ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_23126,plain,
    ( X0_43 != X1_43
    | X0_43 = k1_relat_1(k7_relat_1(sK2,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) != X1_43 ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_23127,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23126])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_480,plain,
    ( r1_xboole_0(X0_43,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_21268,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_482,plain,
    ( r2_hidden(sK0(X0_43,X1_43),X1_43)
    | r1_xboole_0(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1460,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_15958,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_992,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(sK2))
    | ~ r2_hidden(X0_45,sK1)
    | ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_12041,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),sK1)
    | ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_474,plain,
    ( ~ v1_relat_1(X0_43)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0_43)),X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2484,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,X0_43))
    | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,X0_43))),k7_relat_1(sK2,X0_43)) = k7_relat_1(sK2,X0_43) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_7741,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) = k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2484])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_484,plain,
    ( ~ r1_xboole_0(X0_43,X1_43)
    | r1_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6757,plain,
    ( r1_xboole_0(X0_43,k1_relat_1(sK2))
    | ~ r1_xboole_0(k1_relat_1(sK2),X0_43) ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_6759,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6757])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_276,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X0)
    | k1_relat_1(X2) != X1
    | k1_relat_1(k7_relat_1(X2,X3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_277,plain,
    ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k1_relat_1(k7_relat_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_466,plain,
    ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(X0_43,X1_43)),k1_relat_1(X0_43))
    | ~ v1_relat_1(X0_43)
    | v1_xboole_0(k1_relat_1(k7_relat_1(X0_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_1222,plain,
    ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43))) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_5776,plain,
    ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_1023,plain,
    ( X0_43 != X1_43
    | k7_relat_1(sK2,sK1) != X1_43
    | k7_relat_1(sK2,sK1) = X0_43 ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_1080,plain,
    ( X0_43 != k7_relat_1(sK2,sK1)
    | k7_relat_1(sK2,sK1) = X0_43
    | k7_relat_1(sK2,sK1) != k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_3678,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) != k7_relat_1(sK2,sK1)
    | k7_relat_1(sK2,sK1) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1))
    | k7_relat_1(sK2,sK1) != k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_471,plain,
    ( r2_hidden(X0_45,X0_43)
    | ~ r2_hidden(X0_45,k1_relat_1(k7_relat_1(X1_43,X0_43)))
    | ~ v1_relat_1(X1_43) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1012,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(k7_relat_1(X0_43,sK1)))
    | r2_hidden(X0_45,sK1)
    | ~ v1_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_1045,plain,
    ( ~ r2_hidden(X0_45,k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(X0_45,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_3403,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_481,plain,
    ( r2_hidden(sK0(X0_43,X1_43),X0_43)
    | r1_xboole_0(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1459,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,X0_43)))
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_3399,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_2785,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2786,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_468,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_968,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_954,plain,
    ( r1_xboole_0(X0_43,X1_43) != iProver_top
    | r1_xboole_0(X1_43,X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_1211,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_968,c_954])).

cnf(c_1699,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_954])).

cnf(c_1435,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_478,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k7_relat_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1168,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_43))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_1258,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_497,plain,
    ( X0_43 != X1_43
    | k1_relat_1(X0_43) = k1_relat_1(X1_43) ),
    theory(equality)).

cnf(c_1220,plain,
    ( k7_relat_1(sK2,sK1) != X0_43
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1221,plain,
    ( k7_relat_1(sK2,sK1) != k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_1137,plain,
    ( X0_43 != X1_43
    | k1_relat_1(k7_relat_1(sK2,sK1)) != X1_43
    | k1_relat_1(k7_relat_1(sK2,sK1)) = X0_43 ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_1203,plain,
    ( X0_43 != k1_relat_1(X1_43)
    | k1_relat_1(k7_relat_1(sK2,sK1)) = X0_43
    | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(X1_43) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_1204,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_487,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1189,plain,
    ( k7_relat_1(sK2,sK1) = k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_485,plain,
    ( ~ v1_xboole_0(X0_43)
    | k1_xboole_0 = X0_43 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_997,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK2,sK1))
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_469,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_541,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_475,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_510,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_24,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_70374,c_69454,c_65908,c_65247,c_64073,c_64001,c_63742,c_63453,c_23127,c_21268,c_15958,c_12041,c_7741,c_6759,c_5776,c_3678,c_3403,c_3399,c_2785,c_2786,c_1699,c_1435,c_1258,c_1221,c_1204,c_1189,c_997,c_541,c_475,c_510,c_24,c_19,c_23,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:31:47 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 19.74/2.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.74/2.97  
% 19.74/2.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.74/2.97  
% 19.74/2.97  ------  iProver source info
% 19.74/2.97  
% 19.74/2.97  git: date: 2020-06-30 10:37:57 +0100
% 19.74/2.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.74/2.97  git: non_committed_changes: false
% 19.74/2.97  git: last_make_outside_of_git: false
% 19.74/2.97  
% 19.74/2.97  ------ 
% 19.74/2.97  
% 19.74/2.97  ------ Input Options
% 19.74/2.97  
% 19.74/2.97  --out_options                           all
% 19.74/2.97  --tptp_safe_out                         true
% 19.74/2.97  --problem_path                          ""
% 19.74/2.97  --include_path                          ""
% 19.74/2.97  --clausifier                            res/vclausify_rel
% 19.74/2.97  --clausifier_options                    ""
% 19.74/2.97  --stdin                                 false
% 19.74/2.97  --stats_out                             all
% 19.74/2.97  
% 19.74/2.97  ------ General Options
% 19.74/2.97  
% 19.74/2.97  --fof                                   false
% 19.74/2.97  --time_out_real                         305.
% 19.74/2.97  --time_out_virtual                      -1.
% 19.74/2.97  --symbol_type_check                     false
% 19.74/2.97  --clausify_out                          false
% 19.74/2.97  --sig_cnt_out                           false
% 19.74/2.97  --trig_cnt_out                          false
% 19.74/2.97  --trig_cnt_out_tolerance                1.
% 19.74/2.97  --trig_cnt_out_sk_spl                   false
% 19.74/2.97  --abstr_cl_out                          false
% 19.74/2.97  
% 19.74/2.97  ------ Global Options
% 19.74/2.97  
% 19.74/2.97  --schedule                              default
% 19.74/2.97  --add_important_lit                     false
% 19.74/2.97  --prop_solver_per_cl                    1000
% 19.74/2.97  --min_unsat_core                        false
% 19.74/2.97  --soft_assumptions                      false
% 19.74/2.97  --soft_lemma_size                       3
% 19.74/2.97  --prop_impl_unit_size                   0
% 19.74/2.97  --prop_impl_unit                        []
% 19.74/2.97  --share_sel_clauses                     true
% 19.74/2.97  --reset_solvers                         false
% 19.74/2.97  --bc_imp_inh                            [conj_cone]
% 19.74/2.97  --conj_cone_tolerance                   3.
% 19.74/2.97  --extra_neg_conj                        none
% 19.74/2.97  --large_theory_mode                     true
% 19.74/2.97  --prolific_symb_bound                   200
% 19.74/2.97  --lt_threshold                          2000
% 19.74/2.97  --clause_weak_htbl                      true
% 19.74/2.97  --gc_record_bc_elim                     false
% 19.74/2.97  
% 19.74/2.97  ------ Preprocessing Options
% 19.74/2.97  
% 19.74/2.97  --preprocessing_flag                    true
% 19.74/2.97  --time_out_prep_mult                    0.1
% 19.74/2.97  --splitting_mode                        input
% 19.74/2.97  --splitting_grd                         true
% 19.74/2.97  --splitting_cvd                         false
% 19.74/2.97  --splitting_cvd_svl                     false
% 19.74/2.97  --splitting_nvd                         32
% 19.74/2.97  --sub_typing                            true
% 19.74/2.97  --prep_gs_sim                           true
% 19.74/2.97  --prep_unflatten                        true
% 19.74/2.97  --prep_res_sim                          true
% 19.74/2.97  --prep_upred                            true
% 19.74/2.97  --prep_sem_filter                       exhaustive
% 19.74/2.97  --prep_sem_filter_out                   false
% 19.74/2.97  --pred_elim                             true
% 19.74/2.97  --res_sim_input                         true
% 19.74/2.97  --eq_ax_congr_red                       true
% 19.74/2.97  --pure_diseq_elim                       true
% 19.74/2.97  --brand_transform                       false
% 19.74/2.97  --non_eq_to_eq                          false
% 19.74/2.97  --prep_def_merge                        true
% 19.74/2.97  --prep_def_merge_prop_impl              false
% 19.74/2.97  --prep_def_merge_mbd                    true
% 19.74/2.97  --prep_def_merge_tr_red                 false
% 19.74/2.97  --prep_def_merge_tr_cl                  false
% 19.74/2.97  --smt_preprocessing                     true
% 19.74/2.97  --smt_ac_axioms                         fast
% 19.74/2.97  --preprocessed_out                      false
% 19.74/2.97  --preprocessed_stats                    false
% 19.74/2.97  
% 19.74/2.97  ------ Abstraction refinement Options
% 19.74/2.97  
% 19.74/2.97  --abstr_ref                             []
% 19.74/2.97  --abstr_ref_prep                        false
% 19.74/2.97  --abstr_ref_until_sat                   false
% 19.74/2.97  --abstr_ref_sig_restrict                funpre
% 19.74/2.97  --abstr_ref_af_restrict_to_split_sk     false
% 19.74/2.97  --abstr_ref_under                       []
% 19.74/2.97  
% 19.74/2.97  ------ SAT Options
% 19.74/2.97  
% 19.74/2.97  --sat_mode                              false
% 19.74/2.97  --sat_fm_restart_options                ""
% 19.74/2.97  --sat_gr_def                            false
% 19.74/2.97  --sat_epr_types                         true
% 19.74/2.97  --sat_non_cyclic_types                  false
% 19.74/2.97  --sat_finite_models                     false
% 19.74/2.97  --sat_fm_lemmas                         false
% 19.74/2.97  --sat_fm_prep                           false
% 19.74/2.97  --sat_fm_uc_incr                        true
% 19.74/2.97  --sat_out_model                         small
% 19.74/2.97  --sat_out_clauses                       false
% 19.74/2.97  
% 19.74/2.97  ------ QBF Options
% 19.74/2.97  
% 19.74/2.97  --qbf_mode                              false
% 19.74/2.97  --qbf_elim_univ                         false
% 19.74/2.97  --qbf_dom_inst                          none
% 19.74/2.97  --qbf_dom_pre_inst                      false
% 19.74/2.97  --qbf_sk_in                             false
% 19.74/2.97  --qbf_pred_elim                         true
% 19.74/2.97  --qbf_split                             512
% 19.74/2.97  
% 19.74/2.97  ------ BMC1 Options
% 19.74/2.97  
% 19.74/2.97  --bmc1_incremental                      false
% 19.74/2.97  --bmc1_axioms                           reachable_all
% 19.74/2.97  --bmc1_min_bound                        0
% 19.74/2.97  --bmc1_max_bound                        -1
% 19.74/2.97  --bmc1_max_bound_default                -1
% 19.74/2.97  --bmc1_symbol_reachability              true
% 19.74/2.97  --bmc1_property_lemmas                  false
% 19.74/2.97  --bmc1_k_induction                      false
% 19.74/2.97  --bmc1_non_equiv_states                 false
% 19.74/2.97  --bmc1_deadlock                         false
% 19.74/2.97  --bmc1_ucm                              false
% 19.74/2.97  --bmc1_add_unsat_core                   none
% 19.74/2.97  --bmc1_unsat_core_children              false
% 19.74/2.97  --bmc1_unsat_core_extrapolate_axioms    false
% 19.74/2.97  --bmc1_out_stat                         full
% 19.74/2.97  --bmc1_ground_init                      false
% 19.74/2.97  --bmc1_pre_inst_next_state              false
% 19.74/2.97  --bmc1_pre_inst_state                   false
% 19.74/2.97  --bmc1_pre_inst_reach_state             false
% 19.74/2.97  --bmc1_out_unsat_core                   false
% 19.74/2.97  --bmc1_aig_witness_out                  false
% 19.74/2.97  --bmc1_verbose                          false
% 19.74/2.97  --bmc1_dump_clauses_tptp                false
% 19.74/2.97  --bmc1_dump_unsat_core_tptp             false
% 19.74/2.97  --bmc1_dump_file                        -
% 19.74/2.97  --bmc1_ucm_expand_uc_limit              128
% 19.74/2.97  --bmc1_ucm_n_expand_iterations          6
% 19.74/2.97  --bmc1_ucm_extend_mode                  1
% 19.74/2.97  --bmc1_ucm_init_mode                    2
% 19.74/2.97  --bmc1_ucm_cone_mode                    none
% 19.74/2.97  --bmc1_ucm_reduced_relation_type        0
% 19.74/2.97  --bmc1_ucm_relax_model                  4
% 19.74/2.97  --bmc1_ucm_full_tr_after_sat            true
% 19.74/2.97  --bmc1_ucm_expand_neg_assumptions       false
% 19.74/2.97  --bmc1_ucm_layered_model                none
% 19.74/2.97  --bmc1_ucm_max_lemma_size               10
% 19.74/2.97  
% 19.74/2.97  ------ AIG Options
% 19.74/2.97  
% 19.74/2.97  --aig_mode                              false
% 19.74/2.97  
% 19.74/2.97  ------ Instantiation Options
% 19.74/2.97  
% 19.74/2.97  --instantiation_flag                    true
% 19.74/2.97  --inst_sos_flag                         true
% 19.74/2.97  --inst_sos_phase                        true
% 19.74/2.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.74/2.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.74/2.97  --inst_lit_sel_side                     num_symb
% 19.74/2.97  --inst_solver_per_active                1400
% 19.74/2.97  --inst_solver_calls_frac                1.
% 19.74/2.97  --inst_passive_queue_type               priority_queues
% 19.74/2.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.74/2.97  --inst_passive_queues_freq              [25;2]
% 19.74/2.97  --inst_dismatching                      true
% 19.74/2.97  --inst_eager_unprocessed_to_passive     true
% 19.74/2.97  --inst_prop_sim_given                   true
% 19.74/2.97  --inst_prop_sim_new                     false
% 19.74/2.97  --inst_subs_new                         false
% 19.74/2.97  --inst_eq_res_simp                      false
% 19.74/2.97  --inst_subs_given                       false
% 19.74/2.97  --inst_orphan_elimination               true
% 19.74/2.97  --inst_learning_loop_flag               true
% 19.74/2.97  --inst_learning_start                   3000
% 19.74/2.97  --inst_learning_factor                  2
% 19.74/2.97  --inst_start_prop_sim_after_learn       3
% 19.74/2.97  --inst_sel_renew                        solver
% 19.74/2.97  --inst_lit_activity_flag                true
% 19.74/2.97  --inst_restr_to_given                   false
% 19.74/2.97  --inst_activity_threshold               500
% 19.74/2.97  --inst_out_proof                        true
% 19.74/2.97  
% 19.74/2.97  ------ Resolution Options
% 19.74/2.97  
% 19.74/2.97  --resolution_flag                       true
% 19.74/2.97  --res_lit_sel                           adaptive
% 19.74/2.97  --res_lit_sel_side                      none
% 19.74/2.97  --res_ordering                          kbo
% 19.74/2.97  --res_to_prop_solver                    active
% 19.74/2.97  --res_prop_simpl_new                    false
% 19.74/2.97  --res_prop_simpl_given                  true
% 19.74/2.97  --res_passive_queue_type                priority_queues
% 19.74/2.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.74/2.97  --res_passive_queues_freq               [15;5]
% 19.74/2.97  --res_forward_subs                      full
% 19.74/2.97  --res_backward_subs                     full
% 19.74/2.97  --res_forward_subs_resolution           true
% 19.74/2.97  --res_backward_subs_resolution          true
% 19.74/2.97  --res_orphan_elimination                true
% 19.74/2.97  --res_time_limit                        2.
% 19.74/2.97  --res_out_proof                         true
% 19.74/2.97  
% 19.74/2.97  ------ Superposition Options
% 19.74/2.97  
% 19.74/2.97  --superposition_flag                    true
% 19.74/2.97  --sup_passive_queue_type                priority_queues
% 19.74/2.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.74/2.97  --sup_passive_queues_freq               [8;1;4]
% 19.74/2.97  --demod_completeness_check              fast
% 19.74/2.97  --demod_use_ground                      true
% 19.74/2.97  --sup_to_prop_solver                    passive
% 19.74/2.97  --sup_prop_simpl_new                    true
% 19.74/2.97  --sup_prop_simpl_given                  true
% 19.74/2.97  --sup_fun_splitting                     true
% 19.74/2.97  --sup_smt_interval                      50000
% 19.74/2.97  
% 19.74/2.97  ------ Superposition Simplification Setup
% 19.74/2.97  
% 19.74/2.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.74/2.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.74/2.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.74/2.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.74/2.97  --sup_full_triv                         [TrivRules;PropSubs]
% 19.74/2.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.74/2.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.74/2.97  --sup_immed_triv                        [TrivRules]
% 19.74/2.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/2.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/2.97  --sup_immed_bw_main                     []
% 19.74/2.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.74/2.97  --sup_input_triv                        [Unflattening;TrivRules]
% 19.74/2.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/2.97  --sup_input_bw                          []
% 19.74/2.97  
% 19.74/2.97  ------ Combination Options
% 19.74/2.97  
% 19.74/2.97  --comb_res_mult                         3
% 19.74/2.97  --comb_sup_mult                         2
% 19.74/2.97  --comb_inst_mult                        10
% 19.74/2.97  
% 19.74/2.97  ------ Debug Options
% 19.74/2.97  
% 19.74/2.97  --dbg_backtrace                         false
% 19.74/2.97  --dbg_dump_prop_clauses                 false
% 19.74/2.97  --dbg_dump_prop_clauses_file            -
% 19.74/2.97  --dbg_out_stat                          false
% 19.74/2.97  ------ Parsing...
% 19.74/2.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.74/2.97  
% 19.74/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.74/2.97  
% 19.74/2.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.74/2.97  
% 19.74/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.74/2.97  ------ Proving...
% 19.74/2.97  ------ Problem Properties 
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  clauses                                 20
% 19.74/2.97  conjectures                             3
% 19.74/2.97  EPR                                     5
% 19.74/2.97  Horn                                    17
% 19.74/2.97  unary                                   4
% 19.74/2.97  binary                                  10
% 19.74/2.97  lits                                    43
% 19.74/2.97  lits eq                                 7
% 19.74/2.97  fd_pure                                 0
% 19.74/2.97  fd_pseudo                               0
% 19.74/2.97  fd_cond                                 1
% 19.74/2.97  fd_pseudo_cond                          0
% 19.74/2.97  AC symbols                              0
% 19.74/2.97  
% 19.74/2.97  ------ Schedule dynamic 5 is on 
% 19.74/2.97  
% 19.74/2.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  ------ 
% 19.74/2.97  Current options:
% 19.74/2.97  ------ 
% 19.74/2.97  
% 19.74/2.97  ------ Input Options
% 19.74/2.97  
% 19.74/2.97  --out_options                           all
% 19.74/2.97  --tptp_safe_out                         true
% 19.74/2.97  --problem_path                          ""
% 19.74/2.97  --include_path                          ""
% 19.74/2.97  --clausifier                            res/vclausify_rel
% 19.74/2.97  --clausifier_options                    ""
% 19.74/2.97  --stdin                                 false
% 19.74/2.97  --stats_out                             all
% 19.74/2.97  
% 19.74/2.97  ------ General Options
% 19.74/2.97  
% 19.74/2.97  --fof                                   false
% 19.74/2.97  --time_out_real                         305.
% 19.74/2.97  --time_out_virtual                      -1.
% 19.74/2.97  --symbol_type_check                     false
% 19.74/2.97  --clausify_out                          false
% 19.74/2.97  --sig_cnt_out                           false
% 19.74/2.97  --trig_cnt_out                          false
% 19.74/2.97  --trig_cnt_out_tolerance                1.
% 19.74/2.97  --trig_cnt_out_sk_spl                   false
% 19.74/2.97  --abstr_cl_out                          false
% 19.74/2.97  
% 19.74/2.97  ------ Global Options
% 19.74/2.97  
% 19.74/2.97  --schedule                              default
% 19.74/2.97  --add_important_lit                     false
% 19.74/2.97  --prop_solver_per_cl                    1000
% 19.74/2.97  --min_unsat_core                        false
% 19.74/2.97  --soft_assumptions                      false
% 19.74/2.97  --soft_lemma_size                       3
% 19.74/2.97  --prop_impl_unit_size                   0
% 19.74/2.97  --prop_impl_unit                        []
% 19.74/2.97  --share_sel_clauses                     true
% 19.74/2.97  --reset_solvers                         false
% 19.74/2.97  --bc_imp_inh                            [conj_cone]
% 19.74/2.97  --conj_cone_tolerance                   3.
% 19.74/2.97  --extra_neg_conj                        none
% 19.74/2.97  --large_theory_mode                     true
% 19.74/2.97  --prolific_symb_bound                   200
% 19.74/2.97  --lt_threshold                          2000
% 19.74/2.97  --clause_weak_htbl                      true
% 19.74/2.97  --gc_record_bc_elim                     false
% 19.74/2.97  
% 19.74/2.97  ------ Preprocessing Options
% 19.74/2.97  
% 19.74/2.97  --preprocessing_flag                    true
% 19.74/2.97  --time_out_prep_mult                    0.1
% 19.74/2.97  --splitting_mode                        input
% 19.74/2.97  --splitting_grd                         true
% 19.74/2.97  --splitting_cvd                         false
% 19.74/2.97  --splitting_cvd_svl                     false
% 19.74/2.97  --splitting_nvd                         32
% 19.74/2.97  --sub_typing                            true
% 19.74/2.97  --prep_gs_sim                           true
% 19.74/2.97  --prep_unflatten                        true
% 19.74/2.97  --prep_res_sim                          true
% 19.74/2.97  --prep_upred                            true
% 19.74/2.97  --prep_sem_filter                       exhaustive
% 19.74/2.97  --prep_sem_filter_out                   false
% 19.74/2.97  --pred_elim                             true
% 19.74/2.97  --res_sim_input                         true
% 19.74/2.97  --eq_ax_congr_red                       true
% 19.74/2.97  --pure_diseq_elim                       true
% 19.74/2.97  --brand_transform                       false
% 19.74/2.97  --non_eq_to_eq                          false
% 19.74/2.97  --prep_def_merge                        true
% 19.74/2.97  --prep_def_merge_prop_impl              false
% 19.74/2.97  --prep_def_merge_mbd                    true
% 19.74/2.97  --prep_def_merge_tr_red                 false
% 19.74/2.97  --prep_def_merge_tr_cl                  false
% 19.74/2.97  --smt_preprocessing                     true
% 19.74/2.97  --smt_ac_axioms                         fast
% 19.74/2.97  --preprocessed_out                      false
% 19.74/2.97  --preprocessed_stats                    false
% 19.74/2.97  
% 19.74/2.97  ------ Abstraction refinement Options
% 19.74/2.97  
% 19.74/2.97  --abstr_ref                             []
% 19.74/2.97  --abstr_ref_prep                        false
% 19.74/2.97  --abstr_ref_until_sat                   false
% 19.74/2.97  --abstr_ref_sig_restrict                funpre
% 19.74/2.97  --abstr_ref_af_restrict_to_split_sk     false
% 19.74/2.97  --abstr_ref_under                       []
% 19.74/2.97  
% 19.74/2.97  ------ SAT Options
% 19.74/2.97  
% 19.74/2.97  --sat_mode                              false
% 19.74/2.97  --sat_fm_restart_options                ""
% 19.74/2.97  --sat_gr_def                            false
% 19.74/2.97  --sat_epr_types                         true
% 19.74/2.97  --sat_non_cyclic_types                  false
% 19.74/2.97  --sat_finite_models                     false
% 19.74/2.97  --sat_fm_lemmas                         false
% 19.74/2.97  --sat_fm_prep                           false
% 19.74/2.97  --sat_fm_uc_incr                        true
% 19.74/2.97  --sat_out_model                         small
% 19.74/2.97  --sat_out_clauses                       false
% 19.74/2.97  
% 19.74/2.97  ------ QBF Options
% 19.74/2.97  
% 19.74/2.97  --qbf_mode                              false
% 19.74/2.97  --qbf_elim_univ                         false
% 19.74/2.97  --qbf_dom_inst                          none
% 19.74/2.97  --qbf_dom_pre_inst                      false
% 19.74/2.97  --qbf_sk_in                             false
% 19.74/2.97  --qbf_pred_elim                         true
% 19.74/2.97  --qbf_split                             512
% 19.74/2.97  
% 19.74/2.97  ------ BMC1 Options
% 19.74/2.97  
% 19.74/2.97  --bmc1_incremental                      false
% 19.74/2.97  --bmc1_axioms                           reachable_all
% 19.74/2.97  --bmc1_min_bound                        0
% 19.74/2.97  --bmc1_max_bound                        -1
% 19.74/2.97  --bmc1_max_bound_default                -1
% 19.74/2.97  --bmc1_symbol_reachability              true
% 19.74/2.97  --bmc1_property_lemmas                  false
% 19.74/2.97  --bmc1_k_induction                      false
% 19.74/2.97  --bmc1_non_equiv_states                 false
% 19.74/2.97  --bmc1_deadlock                         false
% 19.74/2.97  --bmc1_ucm                              false
% 19.74/2.97  --bmc1_add_unsat_core                   none
% 19.74/2.97  --bmc1_unsat_core_children              false
% 19.74/2.97  --bmc1_unsat_core_extrapolate_axioms    false
% 19.74/2.97  --bmc1_out_stat                         full
% 19.74/2.97  --bmc1_ground_init                      false
% 19.74/2.97  --bmc1_pre_inst_next_state              false
% 19.74/2.97  --bmc1_pre_inst_state                   false
% 19.74/2.97  --bmc1_pre_inst_reach_state             false
% 19.74/2.97  --bmc1_out_unsat_core                   false
% 19.74/2.97  --bmc1_aig_witness_out                  false
% 19.74/2.97  --bmc1_verbose                          false
% 19.74/2.97  --bmc1_dump_clauses_tptp                false
% 19.74/2.97  --bmc1_dump_unsat_core_tptp             false
% 19.74/2.97  --bmc1_dump_file                        -
% 19.74/2.97  --bmc1_ucm_expand_uc_limit              128
% 19.74/2.97  --bmc1_ucm_n_expand_iterations          6
% 19.74/2.97  --bmc1_ucm_extend_mode                  1
% 19.74/2.97  --bmc1_ucm_init_mode                    2
% 19.74/2.97  --bmc1_ucm_cone_mode                    none
% 19.74/2.97  --bmc1_ucm_reduced_relation_type        0
% 19.74/2.97  --bmc1_ucm_relax_model                  4
% 19.74/2.97  --bmc1_ucm_full_tr_after_sat            true
% 19.74/2.97  --bmc1_ucm_expand_neg_assumptions       false
% 19.74/2.97  --bmc1_ucm_layered_model                none
% 19.74/2.97  --bmc1_ucm_max_lemma_size               10
% 19.74/2.97  
% 19.74/2.97  ------ AIG Options
% 19.74/2.97  
% 19.74/2.97  --aig_mode                              false
% 19.74/2.97  
% 19.74/2.97  ------ Instantiation Options
% 19.74/2.97  
% 19.74/2.97  --instantiation_flag                    true
% 19.74/2.97  --inst_sos_flag                         true
% 19.74/2.97  --inst_sos_phase                        true
% 19.74/2.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.74/2.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.74/2.97  --inst_lit_sel_side                     none
% 19.74/2.97  --inst_solver_per_active                1400
% 19.74/2.97  --inst_solver_calls_frac                1.
% 19.74/2.97  --inst_passive_queue_type               priority_queues
% 19.74/2.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.74/2.97  --inst_passive_queues_freq              [25;2]
% 19.74/2.97  --inst_dismatching                      true
% 19.74/2.97  --inst_eager_unprocessed_to_passive     true
% 19.74/2.97  --inst_prop_sim_given                   true
% 19.74/2.97  --inst_prop_sim_new                     false
% 19.74/2.97  --inst_subs_new                         false
% 19.74/2.97  --inst_eq_res_simp                      false
% 19.74/2.97  --inst_subs_given                       false
% 19.74/2.97  --inst_orphan_elimination               true
% 19.74/2.97  --inst_learning_loop_flag               true
% 19.74/2.97  --inst_learning_start                   3000
% 19.74/2.97  --inst_learning_factor                  2
% 19.74/2.97  --inst_start_prop_sim_after_learn       3
% 19.74/2.97  --inst_sel_renew                        solver
% 19.74/2.97  --inst_lit_activity_flag                true
% 19.74/2.97  --inst_restr_to_given                   false
% 19.74/2.97  --inst_activity_threshold               500
% 19.74/2.97  --inst_out_proof                        true
% 19.74/2.97  
% 19.74/2.97  ------ Resolution Options
% 19.74/2.97  
% 19.74/2.97  --resolution_flag                       false
% 19.74/2.97  --res_lit_sel                           adaptive
% 19.74/2.97  --res_lit_sel_side                      none
% 19.74/2.97  --res_ordering                          kbo
% 19.74/2.97  --res_to_prop_solver                    active
% 19.74/2.97  --res_prop_simpl_new                    false
% 19.74/2.97  --res_prop_simpl_given                  true
% 19.74/2.97  --res_passive_queue_type                priority_queues
% 19.74/2.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.74/2.97  --res_passive_queues_freq               [15;5]
% 19.74/2.97  --res_forward_subs                      full
% 19.74/2.97  --res_backward_subs                     full
% 19.74/2.97  --res_forward_subs_resolution           true
% 19.74/2.97  --res_backward_subs_resolution          true
% 19.74/2.97  --res_orphan_elimination                true
% 19.74/2.97  --res_time_limit                        2.
% 19.74/2.97  --res_out_proof                         true
% 19.74/2.97  
% 19.74/2.97  ------ Superposition Options
% 19.74/2.97  
% 19.74/2.97  --superposition_flag                    true
% 19.74/2.97  --sup_passive_queue_type                priority_queues
% 19.74/2.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.74/2.97  --sup_passive_queues_freq               [8;1;4]
% 19.74/2.97  --demod_completeness_check              fast
% 19.74/2.97  --demod_use_ground                      true
% 19.74/2.97  --sup_to_prop_solver                    passive
% 19.74/2.97  --sup_prop_simpl_new                    true
% 19.74/2.97  --sup_prop_simpl_given                  true
% 19.74/2.97  --sup_fun_splitting                     true
% 19.74/2.97  --sup_smt_interval                      50000
% 19.74/2.97  
% 19.74/2.97  ------ Superposition Simplification Setup
% 19.74/2.97  
% 19.74/2.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.74/2.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.74/2.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.74/2.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.74/2.97  --sup_full_triv                         [TrivRules;PropSubs]
% 19.74/2.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.74/2.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.74/2.97  --sup_immed_triv                        [TrivRules]
% 19.74/2.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/2.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/2.97  --sup_immed_bw_main                     []
% 19.74/2.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.74/2.97  --sup_input_triv                        [Unflattening;TrivRules]
% 19.74/2.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.74/2.97  --sup_input_bw                          []
% 19.74/2.97  
% 19.74/2.97  ------ Combination Options
% 19.74/2.97  
% 19.74/2.97  --comb_res_mult                         3
% 19.74/2.97  --comb_sup_mult                         2
% 19.74/2.97  --comb_inst_mult                        10
% 19.74/2.97  
% 19.74/2.97  ------ Debug Options
% 19.74/2.97  
% 19.74/2.97  --dbg_backtrace                         false
% 19.74/2.97  --dbg_dump_prop_clauses                 false
% 19.74/2.97  --dbg_dump_prop_clauses_file            -
% 19.74/2.97  --dbg_out_stat                          false
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  ------ Proving...
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  % SZS status Theorem for theBenchmark.p
% 19.74/2.97  
% 19.74/2.97  % SZS output start CNFRefutation for theBenchmark.p
% 19.74/2.97  
% 19.74/2.97  fof(f11,axiom,(
% 19.74/2.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f27,plain,(
% 19.74/2.97    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 19.74/2.97    inference(ennf_transformation,[],[f11])).
% 19.74/2.97  
% 19.74/2.97  fof(f33,plain,(
% 19.74/2.97    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 19.74/2.97    inference(nnf_transformation,[],[f27])).
% 19.74/2.97  
% 19.74/2.97  fof(f34,plain,(
% 19.74/2.97    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 19.74/2.97    inference(flattening,[],[f33])).
% 19.74/2.97  
% 19.74/2.97  fof(f55,plain,(
% 19.74/2.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f34])).
% 19.74/2.97  
% 19.74/2.97  fof(f3,axiom,(
% 19.74/2.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f16,plain,(
% 19.74/2.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.74/2.97    inference(rectify,[],[f3])).
% 19.74/2.97  
% 19.74/2.97  fof(f19,plain,(
% 19.74/2.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.74/2.97    inference(ennf_transformation,[],[f16])).
% 19.74/2.97  
% 19.74/2.97  fof(f31,plain,(
% 19.74/2.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.74/2.97    introduced(choice_axiom,[])).
% 19.74/2.97  
% 19.74/2.97  fof(f32,plain,(
% 19.74/2.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.74/2.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f31])).
% 19.74/2.97  
% 19.74/2.97  fof(f43,plain,(
% 19.74/2.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f32])).
% 19.74/2.97  
% 19.74/2.97  fof(f13,axiom,(
% 19.74/2.97    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f29,plain,(
% 19.74/2.97    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 19.74/2.97    inference(ennf_transformation,[],[f13])).
% 19.74/2.97  
% 19.74/2.97  fof(f57,plain,(
% 19.74/2.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f29])).
% 19.74/2.97  
% 19.74/2.97  fof(f8,axiom,(
% 19.74/2.97    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f24,plain,(
% 19.74/2.97    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 19.74/2.97    inference(ennf_transformation,[],[f8])).
% 19.74/2.97  
% 19.74/2.97  fof(f25,plain,(
% 19.74/2.97    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 19.74/2.97    inference(flattening,[],[f24])).
% 19.74/2.97  
% 19.74/2.97  fof(f48,plain,(
% 19.74/2.97    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f25])).
% 19.74/2.97  
% 19.74/2.97  fof(f4,axiom,(
% 19.74/2.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f44,plain,(
% 19.74/2.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f4])).
% 19.74/2.97  
% 19.74/2.97  fof(f42,plain,(
% 19.74/2.97    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f32])).
% 19.74/2.97  
% 19.74/2.97  fof(f10,axiom,(
% 19.74/2.97    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f26,plain,(
% 19.74/2.97    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 19.74/2.97    inference(ennf_transformation,[],[f10])).
% 19.74/2.97  
% 19.74/2.97  fof(f52,plain,(
% 19.74/2.97    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f26])).
% 19.74/2.97  
% 19.74/2.97  fof(f2,axiom,(
% 19.74/2.97    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f18,plain,(
% 19.74/2.97    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.74/2.97    inference(ennf_transformation,[],[f2])).
% 19.74/2.97  
% 19.74/2.97  fof(f40,plain,(
% 19.74/2.97    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f18])).
% 19.74/2.97  
% 19.74/2.97  fof(f5,axiom,(
% 19.74/2.97    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f20,plain,(
% 19.74/2.97    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 19.74/2.97    inference(ennf_transformation,[],[f5])).
% 19.74/2.97  
% 19.74/2.97  fof(f21,plain,(
% 19.74/2.97    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 19.74/2.97    inference(flattening,[],[f20])).
% 19.74/2.97  
% 19.74/2.97  fof(f45,plain,(
% 19.74/2.97    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f21])).
% 19.74/2.97  
% 19.74/2.97  fof(f12,axiom,(
% 19.74/2.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f28,plain,(
% 19.74/2.97    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.74/2.97    inference(ennf_transformation,[],[f12])).
% 19.74/2.97  
% 19.74/2.97  fof(f56,plain,(
% 19.74/2.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f28])).
% 19.74/2.97  
% 19.74/2.97  fof(f53,plain,(
% 19.74/2.97    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f34])).
% 19.74/2.97  
% 19.74/2.97  fof(f41,plain,(
% 19.74/2.97    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f32])).
% 19.74/2.97  
% 19.74/2.97  fof(f14,conjecture,(
% 19.74/2.97    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f15,negated_conjecture,(
% 19.74/2.97    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 19.74/2.97    inference(negated_conjecture,[],[f14])).
% 19.74/2.97  
% 19.74/2.97  fof(f30,plain,(
% 19.74/2.97    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 19.74/2.97    inference(ennf_transformation,[],[f15])).
% 19.74/2.97  
% 19.74/2.97  fof(f35,plain,(
% 19.74/2.97    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 19.74/2.97    inference(nnf_transformation,[],[f30])).
% 19.74/2.97  
% 19.74/2.97  fof(f36,plain,(
% 19.74/2.97    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 19.74/2.97    inference(flattening,[],[f35])).
% 19.74/2.97  
% 19.74/2.97  fof(f37,plain,(
% 19.74/2.97    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 19.74/2.97    introduced(choice_axiom,[])).
% 19.74/2.97  
% 19.74/2.97  fof(f38,plain,(
% 19.74/2.97    (~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 19.74/2.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f37])).
% 19.74/2.97  
% 19.74/2.97  fof(f59,plain,(
% 19.74/2.97    r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)),
% 19.74/2.97    inference(cnf_transformation,[],[f38])).
% 19.74/2.97  
% 19.74/2.97  fof(f7,axiom,(
% 19.74/2.97    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f23,plain,(
% 19.74/2.97    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 19.74/2.97    inference(ennf_transformation,[],[f7])).
% 19.74/2.97  
% 19.74/2.97  fof(f47,plain,(
% 19.74/2.97    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f23])).
% 19.74/2.97  
% 19.74/2.97  fof(f1,axiom,(
% 19.74/2.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f17,plain,(
% 19.74/2.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 19.74/2.97    inference(ennf_transformation,[],[f1])).
% 19.74/2.97  
% 19.74/2.97  fof(f39,plain,(
% 19.74/2.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 19.74/2.97    inference(cnf_transformation,[],[f17])).
% 19.74/2.97  
% 19.74/2.97  fof(f60,plain,(
% 19.74/2.97    ~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)),
% 19.74/2.97    inference(cnf_transformation,[],[f38])).
% 19.74/2.97  
% 19.74/2.97  fof(f9,axiom,(
% 19.74/2.97    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 19.74/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.74/2.97  
% 19.74/2.97  fof(f50,plain,(
% 19.74/2.97    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 19.74/2.97    inference(cnf_transformation,[],[f9])).
% 19.74/2.97  
% 19.74/2.97  fof(f58,plain,(
% 19.74/2.97    v1_relat_1(sK2)),
% 19.74/2.97    inference(cnf_transformation,[],[f38])).
% 19.74/2.97  
% 19.74/2.97  cnf(c_493,plain,
% 19.74/2.97      ( ~ r2_hidden(X0_45,X0_43)
% 19.74/2.97      | r2_hidden(X1_45,X1_43)
% 19.74/2.97      | X1_45 != X0_45
% 19.74/2.97      | X1_43 != X0_43 ),
% 19.74/2.97      theory(equality) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_63459,plain,
% 19.74/2.97      ( r2_hidden(X0_45,X0_43)
% 19.74/2.97      | ~ r2_hidden(X1_45,k1_relat_1(k7_relat_1(X1_43,X2_43)))
% 19.74/2.97      | X0_45 != X1_45
% 19.74/2.97      | X0_43 != k1_relat_1(k7_relat_1(X1_43,X2_43)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_493]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_67979,plain,
% 19.74/2.97      ( r2_hidden(X0_45,X0_43)
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
% 19.74/2.97      | X0_45 != sK0(k1_relat_1(sK2),sK1)
% 19.74/2.97      | X0_43 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_63459]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_70372,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),X0_43)
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
% 19.74/2.97      | sK0(k1_relat_1(sK2),sK1) != sK0(k1_relat_1(sK2),sK1)
% 19.74/2.97      | X0_43 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_67979]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_70374,plain,
% 19.74/2.97      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
% 19.74/2.97      | r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_xboole_0)
% 19.74/2.97      | sK0(k1_relat_1(sK2),sK1) != sK0(k1_relat_1(sK2),sK1)
% 19.74/2.97      | k1_xboole_0 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_70372]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_489,plain,( X0_45 = X0_45 ),theory(equality) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_69454,plain,
% 19.74/2.97      ( sK0(k1_relat_1(sK2),sK1) = sK0(k1_relat_1(sK2),sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_489]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_14,plain,
% 19.74/2.97      ( ~ r2_hidden(X0,X1)
% 19.74/2.97      | ~ r2_hidden(X0,k1_relat_1(X2))
% 19.74/2.97      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 19.74/2.97      | ~ v1_relat_1(X2) ),
% 19.74/2.97      inference(cnf_transformation,[],[f55]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_473,plain,
% 19.74/2.97      ( ~ r2_hidden(X0_45,X0_43)
% 19.74/2.97      | ~ r2_hidden(X0_45,k1_relat_1(X1_43))
% 19.74/2.97      | r2_hidden(X0_45,k1_relat_1(k7_relat_1(X1_43,X0_43)))
% 19.74/2.97      | ~ v1_relat_1(X1_43) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_14]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_63315,plain,
% 19.74/2.97      ( ~ r2_hidden(X0_45,k1_relat_1(X0_43))
% 19.74/2.97      | r2_hidden(X0_45,k1_relat_1(k7_relat_1(X0_43,sK1)))
% 19.74/2.97      | ~ r2_hidden(X0_45,sK1)
% 19.74/2.97      | ~ v1_relat_1(X0_43) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_473]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_65277,plain,
% 19.74/2.97      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(X0_43))
% 19.74/2.97      | r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(X0_43,sK1)))
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 19.74/2.97      | ~ v1_relat_1(X0_43) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_63315]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_65908,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 19.74/2.97      | ~ v1_relat_1(sK2) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_65277]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_2,plain,
% 19.74/2.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 19.74/2.97      inference(cnf_transformation,[],[f43]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_483,plain,
% 19.74/2.97      ( ~ r2_hidden(X0_45,X0_43)
% 19.74/2.97      | ~ r2_hidden(X0_45,X1_43)
% 19.74/2.97      | ~ r1_xboole_0(X0_43,X1_43) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_2]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_65244,plain,
% 19.74/2.97      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),X0_43)
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 19.74/2.97      | ~ r1_xboole_0(X0_43,k1_relat_1(sK2)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_483]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_65247,plain,
% 19.74/2.97      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_xboole_0)
% 19.74/2.97      | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_65244]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_18,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0)
% 19.74/2.97      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 19.74/2.97      inference(cnf_transformation,[],[f57]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_470,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0_43)
% 19.74/2.97      | k5_relat_1(k6_relat_1(X1_43),X0_43) = k7_relat_1(X0_43,X1_43) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_18]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_64073,plain,
% 19.74/2.97      ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
% 19.74/2.97      | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) = k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_470]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_10,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0)
% 19.74/2.97      | ~ v1_xboole_0(X1)
% 19.74/2.97      | v1_xboole_0(k7_relat_1(X0,X1)) ),
% 19.74/2.97      inference(cnf_transformation,[],[f48]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_477,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0_43)
% 19.74/2.97      | ~ v1_xboole_0(X1_43)
% 19.74/2.97      | v1_xboole_0(k7_relat_1(X0_43,X1_43)) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_10]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_64001,plain,
% 19.74/2.97      ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
% 19.74/2.97      | v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))))
% 19.74/2.97      | ~ v1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1))) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_477]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_491,plain,
% 19.74/2.97      ( ~ v1_xboole_0(X0_43) | v1_xboole_0(X1_43) | X1_43 != X0_43 ),
% 19.74/2.97      theory(equality) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_63574,plain,
% 19.74/2.97      ( ~ v1_xboole_0(X0_43)
% 19.74/2.97      | v1_xboole_0(k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)))
% 19.74/2.97      | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) != X0_43 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_491]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_63742,plain,
% 19.74/2.97      ( v1_xboole_0(k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)))
% 19.74/2.97      | ~ v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))))
% 19.74/2.97      | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) != k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK1))) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_63574]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_63255,plain,
% 19.74/2.97      ( ~ v1_xboole_0(X0_43)
% 19.74/2.97      | v1_xboole_0(k7_relat_1(sK2,sK1))
% 19.74/2.97      | k7_relat_1(sK2,sK1) != X0_43 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_491]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_63453,plain,
% 19.74/2.97      ( ~ v1_xboole_0(k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)))
% 19.74/2.97      | v1_xboole_0(k7_relat_1(sK2,sK1))
% 19.74/2.97      | k7_relat_1(sK2,sK1) != k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_63255]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_490,plain,
% 19.74/2.97      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 19.74/2.97      theory(equality) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1434,plain,
% 19.74/2.97      ( X0_43 != X1_43
% 19.74/2.97      | X0_43 = k1_relat_1(X2_43)
% 19.74/2.97      | k1_relat_1(X2_43) != X1_43 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_490]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_23126,plain,
% 19.74/2.97      ( X0_43 != X1_43
% 19.74/2.97      | X0_43 = k1_relat_1(k7_relat_1(sK2,sK1))
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) != X1_43 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1434]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_23127,plain,
% 19.74/2.97      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
% 19.74/2.97      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,sK1))
% 19.74/2.97      | k1_xboole_0 != k1_xboole_0 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_23126]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_5,plain,
% 19.74/2.97      ( r1_xboole_0(X0,k1_xboole_0) ),
% 19.74/2.97      inference(cnf_transformation,[],[f44]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_480,plain,
% 19.74/2.97      ( r1_xboole_0(X0_43,k1_xboole_0) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_5]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_21268,plain,
% 19.74/2.97      ( r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_480]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_3,plain,
% 19.74/2.97      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 19.74/2.97      inference(cnf_transformation,[],[f42]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_482,plain,
% 19.74/2.97      ( r2_hidden(sK0(X0_43,X1_43),X1_43) | r1_xboole_0(X0_43,X1_43) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_3]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1460,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)),k1_relat_1(sK2))
% 19.74/2.97      | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_482]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_15958,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(sK2))
% 19.74/2.97      | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1460]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_992,plain,
% 19.74/2.97      ( ~ r2_hidden(X0_45,k1_relat_1(sK2))
% 19.74/2.97      | ~ r2_hidden(X0_45,sK1)
% 19.74/2.97      | ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_483]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_12041,plain,
% 19.74/2.97      ( ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(sK2))
% 19.74/2.97      | ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),sK1)
% 19.74/2.97      | ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_992]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_13,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0)
% 19.74/2.97      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 19.74/2.97      inference(cnf_transformation,[],[f52]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_474,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0_43)
% 19.74/2.97      | k5_relat_1(k6_relat_1(k1_relat_1(X0_43)),X0_43) = X0_43 ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_13]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_2484,plain,
% 19.74/2.97      ( ~ v1_relat_1(k7_relat_1(sK2,X0_43))
% 19.74/2.97      | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,X0_43))),k7_relat_1(sK2,X0_43)) = k7_relat_1(sK2,X0_43) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_474]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_7741,plain,
% 19.74/2.97      ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
% 19.74/2.97      | k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) = k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_2484]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1,plain,
% 19.74/2.97      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.74/2.97      inference(cnf_transformation,[],[f40]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_484,plain,
% 19.74/2.97      ( ~ r1_xboole_0(X0_43,X1_43) | r1_xboole_0(X1_43,X0_43) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_1]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_6757,plain,
% 19.74/2.97      ( r1_xboole_0(X0_43,k1_relat_1(sK2))
% 19.74/2.97      | ~ r1_xboole_0(k1_relat_1(sK2),X0_43) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_484]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_6759,plain,
% 19.74/2.97      ( ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
% 19.74/2.97      | r1_xboole_0(k1_xboole_0,k1_relat_1(sK2)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_6757]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_6,plain,
% 19.74/2.97      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 19.74/2.97      inference(cnf_transformation,[],[f45]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_17,plain,
% 19.74/2.97      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 19.74/2.97      | ~ v1_relat_1(X0) ),
% 19.74/2.97      inference(cnf_transformation,[],[f56]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_276,plain,
% 19.74/2.97      ( ~ r1_xboole_0(X0,X1)
% 19.74/2.97      | ~ v1_relat_1(X2)
% 19.74/2.97      | v1_xboole_0(X0)
% 19.74/2.97      | k1_relat_1(X2) != X1
% 19.74/2.97      | k1_relat_1(k7_relat_1(X2,X3)) != X0 ),
% 19.74/2.97      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_277,plain,
% 19.74/2.97      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 19.74/2.97      | ~ v1_relat_1(X0)
% 19.74/2.97      | v1_xboole_0(k1_relat_1(k7_relat_1(X0,X1))) ),
% 19.74/2.97      inference(unflattening,[status(thm)],[c_276]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_466,plain,
% 19.74/2.97      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(X0_43,X1_43)),k1_relat_1(X0_43))
% 19.74/2.97      | ~ v1_relat_1(X0_43)
% 19.74/2.97      | v1_xboole_0(k1_relat_1(k7_relat_1(X0_43,X1_43))) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_277]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1222,plain,
% 19.74/2.97      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2))
% 19.74/2.97      | ~ v1_relat_1(sK2)
% 19.74/2.97      | v1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43))) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_466]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_5776,plain,
% 19.74/2.97      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))
% 19.74/2.97      | ~ v1_relat_1(sK2)
% 19.74/2.97      | v1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1))) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1222]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1023,plain,
% 19.74/2.97      ( X0_43 != X1_43
% 19.74/2.97      | k7_relat_1(sK2,sK1) != X1_43
% 19.74/2.97      | k7_relat_1(sK2,sK1) = X0_43 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_490]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1080,plain,
% 19.74/2.97      ( X0_43 != k7_relat_1(sK2,sK1)
% 19.74/2.97      | k7_relat_1(sK2,sK1) = X0_43
% 19.74/2.97      | k7_relat_1(sK2,sK1) != k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1023]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_3678,plain,
% 19.74/2.97      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1)) != k7_relat_1(sK2,sK1)
% 19.74/2.97      | k7_relat_1(sK2,sK1) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))),k7_relat_1(sK2,sK1))
% 19.74/2.97      | k7_relat_1(sK2,sK1) != k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1080]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_16,plain,
% 19.74/2.97      ( r2_hidden(X0,X1)
% 19.74/2.97      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 19.74/2.97      | ~ v1_relat_1(X2) ),
% 19.74/2.97      inference(cnf_transformation,[],[f53]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_471,plain,
% 19.74/2.97      ( r2_hidden(X0_45,X0_43)
% 19.74/2.97      | ~ r2_hidden(X0_45,k1_relat_1(k7_relat_1(X1_43,X0_43)))
% 19.74/2.97      | ~ v1_relat_1(X1_43) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_16]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1012,plain,
% 19.74/2.97      ( ~ r2_hidden(X0_45,k1_relat_1(k7_relat_1(X0_43,sK1)))
% 19.74/2.97      | r2_hidden(X0_45,sK1)
% 19.74/2.97      | ~ v1_relat_1(X0_43) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_471]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1045,plain,
% 19.74/2.97      ( ~ r2_hidden(X0_45,k1_relat_1(k7_relat_1(sK2,sK1)))
% 19.74/2.97      | r2_hidden(X0_45,sK1)
% 19.74/2.97      | ~ v1_relat_1(sK2) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1012]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_3403,plain,
% 19.74/2.97      ( ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,sK1)))
% 19.74/2.97      | r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),sK1)
% 19.74/2.97      | ~ v1_relat_1(sK2) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1045]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_4,plain,
% 19.74/2.97      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 19.74/2.97      inference(cnf_transformation,[],[f41]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_481,plain,
% 19.74/2.97      ( r2_hidden(sK0(X0_43,X1_43),X0_43) | r1_xboole_0(X0_43,X1_43) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_4]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1459,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,X0_43)))
% 19.74/2.97      | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0_43)),k1_relat_1(sK2)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_481]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_3399,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,sK1)))
% 19.74/2.97      | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1459]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_2785,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 19.74/2.97      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_481]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_2786,plain,
% 19.74/2.97      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 19.74/2.97      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_482]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_20,negated_conjecture,
% 19.74/2.97      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 19.74/2.97      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(cnf_transformation,[],[f59]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_468,negated_conjecture,
% 19.74/2.97      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 19.74/2.97      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_20]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_968,plain,
% 19.74/2.97      ( k1_xboole_0 = k7_relat_1(sK2,sK1)
% 19.74/2.97      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 19.74/2.97      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_954,plain,
% 19.74/2.97      ( r1_xboole_0(X0_43,X1_43) != iProver_top
% 19.74/2.97      | r1_xboole_0(X1_43,X0_43) = iProver_top ),
% 19.74/2.97      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1211,plain,
% 19.74/2.97      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 19.74/2.97      | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
% 19.74/2.97      inference(superposition,[status(thm)],[c_968,c_954]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1699,plain,
% 19.74/2.97      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 19.74/2.97      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 19.74/2.97      inference(superposition,[status(thm)],[c_1211,c_954]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1435,plain,
% 19.74/2.97      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 19.74/2.97      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 19.74/2.97      | k1_xboole_0 != k1_xboole_0 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1434]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_8,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 19.74/2.97      inference(cnf_transformation,[],[f47]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_478,plain,
% 19.74/2.97      ( ~ v1_relat_1(X0_43) | v1_relat_1(k7_relat_1(X0_43,X1_43)) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_8]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1168,plain,
% 19.74/2.97      ( v1_relat_1(k7_relat_1(sK2,X0_43)) | ~ v1_relat_1(sK2) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_478]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1258,plain,
% 19.74/2.97      ( v1_relat_1(k7_relat_1(sK2,sK1)) | ~ v1_relat_1(sK2) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1168]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_497,plain,
% 19.74/2.97      ( X0_43 != X1_43 | k1_relat_1(X0_43) = k1_relat_1(X1_43) ),
% 19.74/2.97      theory(equality) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1220,plain,
% 19.74/2.97      ( k7_relat_1(sK2,sK1) != X0_43
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(X0_43) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_497]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1221,plain,
% 19.74/2.97      ( k7_relat_1(sK2,sK1) != k1_xboole_0
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k1_xboole_0) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1220]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1137,plain,
% 19.74/2.97      ( X0_43 != X1_43
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) != X1_43
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) = X0_43 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_490]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1203,plain,
% 19.74/2.97      ( X0_43 != k1_relat_1(X1_43)
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) = X0_43
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(X1_43) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1137]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1204,plain,
% 19.74/2.97      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k1_xboole_0)
% 19.74/2.97      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
% 19.74/2.97      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_1203]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_487,plain,( X0_43 = X0_43 ),theory(equality) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_1189,plain,
% 19.74/2.97      ( k7_relat_1(sK2,sK1) = k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_487]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_0,plain,
% 19.74/2.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 19.74/2.97      inference(cnf_transformation,[],[f39]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_485,plain,
% 19.74/2.97      ( ~ v1_xboole_0(X0_43) | k1_xboole_0 = X0_43 ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_0]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_997,plain,
% 19.74/2.97      ( ~ v1_xboole_0(k7_relat_1(sK2,sK1))
% 19.74/2.97      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_485]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_19,negated_conjecture,
% 19.74/2.97      ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
% 19.74/2.97      | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(cnf_transformation,[],[f60]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_469,negated_conjecture,
% 19.74/2.97      ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
% 19.74/2.97      | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_19]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_541,plain,
% 19.74/2.97      ( k1_xboole_0 != k7_relat_1(sK2,sK1)
% 19.74/2.97      | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
% 19.74/2.97      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_12,plain,
% 19.74/2.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.74/2.97      inference(cnf_transformation,[],[f50]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_475,plain,
% 19.74/2.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.74/2.97      inference(subtyping,[status(esa)],[c_12]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_510,plain,
% 19.74/2.97      ( k1_xboole_0 = k1_xboole_0 ),
% 19.74/2.97      inference(instantiation,[status(thm)],[c_487]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_24,plain,
% 19.74/2.97      ( k1_xboole_0 != k7_relat_1(sK2,sK1)
% 19.74/2.97      | r1_xboole_0(k1_relat_1(sK2),sK1) != iProver_top ),
% 19.74/2.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_23,plain,
% 19.74/2.97      ( k1_xboole_0 = k7_relat_1(sK2,sK1)
% 19.74/2.97      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 19.74/2.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(c_21,negated_conjecture,
% 19.74/2.97      ( v1_relat_1(sK2) ),
% 19.74/2.97      inference(cnf_transformation,[],[f58]) ).
% 19.74/2.97  
% 19.74/2.97  cnf(contradiction,plain,
% 19.74/2.97      ( $false ),
% 19.74/2.97      inference(minisat,
% 19.74/2.97                [status(thm)],
% 19.74/2.97                [c_70374,c_69454,c_65908,c_65247,c_64073,c_64001,c_63742,
% 19.74/2.97                 c_63453,c_23127,c_21268,c_15958,c_12041,c_7741,c_6759,
% 19.74/2.97                 c_5776,c_3678,c_3403,c_3399,c_2785,c_2786,c_1699,c_1435,
% 19.74/2.97                 c_1258,c_1221,c_1204,c_1189,c_997,c_541,c_475,c_510,
% 19.74/2.97                 c_24,c_19,c_23,c_20,c_21]) ).
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  % SZS output end CNFRefutation for theBenchmark.p
% 19.74/2.97  
% 19.74/2.97  ------                               Statistics
% 19.74/2.97  
% 19.74/2.97  ------ General
% 19.74/2.97  
% 19.74/2.97  abstr_ref_over_cycles:                  0
% 19.74/2.97  abstr_ref_under_cycles:                 0
% 19.74/2.97  gc_basic_clause_elim:                   0
% 19.74/2.97  forced_gc_time:                         0
% 19.74/2.97  parsing_time:                           0.008
% 19.74/2.97  unif_index_cands_time:                  0.
% 19.74/2.97  unif_index_add_time:                    0.
% 19.74/2.97  orderings_time:                         0.
% 19.74/2.97  out_proof_time:                         0.012
% 19.74/2.97  total_time:                             2.28
% 19.74/2.97  num_of_symbols:                         49
% 19.74/2.97  num_of_terms:                           91570
% 19.74/2.97  
% 19.74/2.97  ------ Preprocessing
% 19.74/2.97  
% 19.74/2.97  num_of_splits:                          0
% 19.74/2.97  num_of_split_atoms:                     0
% 19.74/2.97  num_of_reused_defs:                     0
% 19.74/2.97  num_eq_ax_congr_red:                    12
% 19.74/2.97  num_of_sem_filtered_clauses:            1
% 19.74/2.97  num_of_subtypes:                        3
% 19.74/2.97  monotx_restored_types:                  0
% 19.74/2.97  sat_num_of_epr_types:                   0
% 19.74/2.97  sat_num_of_non_cyclic_types:            0
% 19.74/2.97  sat_guarded_non_collapsed_types:        1
% 19.74/2.97  num_pure_diseq_elim:                    0
% 19.74/2.97  simp_replaced_by:                       0
% 19.74/2.97  res_preprocessed:                       108
% 19.74/2.97  prep_upred:                             0
% 19.74/2.97  prep_unflattend:                        2
% 19.74/2.97  smt_new_axioms:                         0
% 19.74/2.97  pred_elim_cands:                        4
% 19.74/2.97  pred_elim:                              1
% 19.74/2.97  pred_elim_cl:                           1
% 19.74/2.97  pred_elim_cycles:                       3
% 19.74/2.97  merged_defs:                            8
% 19.74/2.97  merged_defs_ncl:                        0
% 19.74/2.97  bin_hyper_res:                          8
% 19.74/2.97  prep_cycles:                            4
% 19.74/2.97  pred_elim_time:                         0.001
% 19.74/2.97  splitting_time:                         0.
% 19.74/2.97  sem_filter_time:                        0.
% 19.74/2.97  monotx_time:                            0.
% 19.74/2.97  subtype_inf_time:                       0.
% 19.74/2.97  
% 19.74/2.97  ------ Problem properties
% 19.74/2.97  
% 19.74/2.97  clauses:                                20
% 19.74/2.97  conjectures:                            3
% 19.74/2.97  epr:                                    5
% 19.74/2.97  horn:                                   17
% 19.74/2.97  ground:                                 5
% 19.74/2.97  unary:                                  4
% 19.74/2.97  binary:                                 10
% 19.74/2.97  lits:                                   43
% 19.74/2.97  lits_eq:                                7
% 19.74/2.97  fd_pure:                                0
% 19.74/2.97  fd_pseudo:                              0
% 19.74/2.97  fd_cond:                                1
% 19.74/2.97  fd_pseudo_cond:                         0
% 19.74/2.97  ac_symbols:                             0
% 19.74/2.97  
% 19.74/2.97  ------ Propositional Solver
% 19.74/2.97  
% 19.74/2.97  prop_solver_calls:                      49
% 19.74/2.97  prop_fast_solver_calls:                 2580
% 19.74/2.97  smt_solver_calls:                       0
% 19.74/2.97  smt_fast_solver_calls:                  0
% 19.74/2.97  prop_num_of_clauses:                    31650
% 19.74/2.97  prop_preprocess_simplified:             55629
% 19.74/2.97  prop_fo_subsumed:                       110
% 19.74/2.97  prop_solver_time:                       0.
% 19.74/2.97  smt_solver_time:                        0.
% 19.74/2.97  smt_fast_solver_time:                   0.
% 19.74/2.97  prop_fast_solver_time:                  0.
% 19.74/2.97  prop_unsat_core_time:                   0.003
% 19.74/2.97  
% 19.74/2.97  ------ QBF
% 19.74/2.97  
% 19.74/2.97  qbf_q_res:                              0
% 19.74/2.97  qbf_num_tautologies:                    0
% 19.74/2.97  qbf_prep_cycles:                        0
% 19.74/2.97  
% 19.74/2.97  ------ BMC1
% 19.74/2.97  
% 19.74/2.97  bmc1_current_bound:                     -1
% 19.74/2.97  bmc1_last_solved_bound:                 -1
% 19.74/2.97  bmc1_unsat_core_size:                   -1
% 19.74/2.97  bmc1_unsat_core_parents_size:           -1
% 19.74/2.97  bmc1_merge_next_fun:                    0
% 19.74/2.97  bmc1_unsat_core_clauses_time:           0.
% 19.74/2.97  
% 19.74/2.97  ------ Instantiation
% 19.74/2.97  
% 19.74/2.97  inst_num_of_clauses:                    939
% 19.74/2.97  inst_num_in_passive:                    208
% 19.74/2.97  inst_num_in_active:                     2830
% 19.74/2.97  inst_num_in_unprocessed:                277
% 19.74/2.97  inst_num_of_loops:                      3526
% 19.74/2.97  inst_num_of_learning_restarts:          1
% 19.74/2.97  inst_num_moves_active_passive:          684
% 19.74/2.97  inst_lit_activity:                      0
% 19.74/2.97  inst_lit_activity_moves:                0
% 19.74/2.97  inst_num_tautologies:                   0
% 19.74/2.97  inst_num_prop_implied:                  0
% 19.74/2.97  inst_num_existing_simplified:           0
% 19.74/2.97  inst_num_eq_res_simplified:             0
% 19.74/2.97  inst_num_child_elim:                    0
% 19.74/2.97  inst_num_of_dismatching_blockings:      8578
% 19.74/2.97  inst_num_of_non_proper_insts:           7728
% 19.74/2.97  inst_num_of_duplicates:                 0
% 19.74/2.97  inst_inst_num_from_inst_to_res:         0
% 19.74/2.97  inst_dismatching_checking_time:         0.
% 19.74/2.97  
% 19.74/2.97  ------ Resolution
% 19.74/2.97  
% 19.74/2.97  res_num_of_clauses:                     33
% 19.74/2.97  res_num_in_passive:                     33
% 19.74/2.97  res_num_in_active:                      0
% 19.74/2.97  res_num_of_loops:                       112
% 19.74/2.97  res_forward_subset_subsumed:            114
% 19.74/2.97  res_backward_subset_subsumed:           16
% 19.74/2.97  res_forward_subsumed:                   0
% 19.74/2.97  res_backward_subsumed:                  0
% 19.74/2.97  res_forward_subsumption_resolution:     0
% 19.74/2.97  res_backward_subsumption_resolution:    0
% 19.74/2.97  res_clause_to_clause_subsumption:       44710
% 19.74/2.97  res_orphan_elimination:                 0
% 19.74/2.97  res_tautology_del:                      509
% 19.74/2.97  res_num_eq_res_simplified:              0
% 19.74/2.97  res_num_sel_changes:                    0
% 19.74/2.97  res_moves_from_active_to_pass:          0
% 19.74/2.97  
% 19.74/2.97  ------ Superposition
% 19.74/2.97  
% 19.74/2.97  sup_time_total:                         0.
% 19.74/2.97  sup_time_generating:                    0.
% 19.74/2.97  sup_time_sim_full:                      0.
% 19.74/2.97  sup_time_sim_immed:                     0.
% 19.74/2.97  
% 19.74/2.97  sup_num_of_clauses:                     1652
% 19.74/2.97  sup_num_in_active:                      685
% 19.74/2.97  sup_num_in_passive:                     967
% 19.74/2.97  sup_num_of_loops:                       704
% 19.74/2.97  sup_fw_superposition:                   3773
% 19.74/2.97  sup_bw_superposition:                   1333
% 19.74/2.97  sup_immediate_simplified:               2724
% 19.74/2.97  sup_given_eliminated:                   4
% 19.74/2.97  comparisons_done:                       0
% 19.74/2.97  comparisons_avoided:                    0
% 19.74/2.97  
% 19.74/2.97  ------ Simplifications
% 19.74/2.97  
% 19.74/2.97  
% 19.74/2.97  sim_fw_subset_subsumed:                 79
% 19.74/2.97  sim_bw_subset_subsumed:                 38
% 19.74/2.97  sim_fw_subsumed:                        1399
% 19.74/2.97  sim_bw_subsumed:                        25
% 19.74/2.97  sim_fw_subsumption_res:                 0
% 19.74/2.97  sim_bw_subsumption_res:                 0
% 19.74/2.97  sim_tautology_del:                      129
% 19.74/2.97  sim_eq_tautology_del:                   431
% 19.74/2.97  sim_eq_res_simp:                        0
% 19.74/2.97  sim_fw_demodulated:                     1368
% 19.74/2.97  sim_bw_demodulated:                     4
% 19.74/2.97  sim_light_normalised:                   1806
% 19.74/2.97  sim_joinable_taut:                      0
% 19.74/2.97  sim_joinable_simp:                      0
% 19.74/2.97  sim_ac_normalised:                      0
% 19.74/2.97  sim_smt_subsumption:                    0
% 19.74/2.97  
%------------------------------------------------------------------------------
