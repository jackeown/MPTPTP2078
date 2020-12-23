%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:08 EST 2020

% Result     : Theorem 11.77s
% Output     : CNFRefutation 11.77s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 252 expanded)
%              Number of clauses        :   64 (  78 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  319 (1069 expanded)
%              Number of equality atoms :   85 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f53,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f68,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,sK3)
      & v2_funct_1(sK4)
      & r1_tarski(sK2,k1_relat_1(sK4))
      & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ~ r1_tarski(sK2,sK3)
    & v2_funct_1(sK4)
    & r1_tarski(sK2,k1_relat_1(sK4))
    & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f54,f68])).

fof(f114,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f110,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f111,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f103,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f69])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f113,plain,(
    r1_tarski(sK2,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1541,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_37,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1544,plain,
    ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2962,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1544])).

cnf(c_44,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1969,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_4031,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2962,c_44,c_43,c_40,c_1969])).

cnf(c_35,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1546,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5450,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4031,c_1546])).

cnf(c_38,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1543,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2034,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1543])).

cnf(c_1974,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2257,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2034,c_44,c_43,c_40,c_1974])).

cnf(c_5475,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5450,c_2257])).

cnf(c_45,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_46,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_31,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1876,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1877,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_32,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1895,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1896,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_42433,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5475,c_45,c_46,c_1877,c_1896])).

cnf(c_42,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1539,plain,
    ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1558,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3422,plain,
    ( k2_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = k9_relat_1(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1539,c_1558])).

cnf(c_1537,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_30,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1551,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10009,plain,
    ( k2_xboole_0(k10_relat_1(sK4,X0),k10_relat_1(sK4,X1)) = k10_relat_1(sK4,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1537,c_1551])).

cnf(c_19,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1559,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11199,plain,
    ( r1_tarski(k10_relat_1(sK4,X0),X1) = iProver_top
    | r1_tarski(k10_relat_1(sK4,k2_xboole_0(X0,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10009,c_1559])).

cnf(c_27386,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK3)),X0) != iProver_top
    | r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3422,c_11199])).

cnf(c_43430,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_42433,c_27386])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2658,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),X0)
    | r2_hidden(sK0(sK2,sK3),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7572,plain,
    ( r2_hidden(sK0(sK2,sK3),X0)
    | ~ r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
    | ~ r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_2658])).

cnf(c_19778,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
    | r2_hidden(sK0(sK2,sK3),sK3)
    | ~ r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),sK3) ),
    inference(instantiation,[status(thm)],[c_7572])).

cnf(c_19781,plain,
    ( r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2))) != iProver_top
    | r2_hidden(sK0(sK2,sK3),sK3) = iProver_top
    | r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19778])).

cnf(c_2120,plain,
    ( r2_hidden(sK0(sK2,sK3),X0)
    | ~ r2_hidden(sK0(sK2,sK3),sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4009,plain,
    ( r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
    | ~ r2_hidden(sK0(sK2,sK3),sK2)
    | ~ r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2))) ),
    inference(instantiation,[status(thm)],[c_2120])).

cnf(c_4010,plain,
    ( r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2))) = iProver_top
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4009])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2651,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK3)
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2654,plain,
    ( r2_hidden(sK0(sK2,sK3),sK3) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_36,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1944,plain,
    ( r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_2324,plain,
    ( r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
    | ~ r1_tarski(sK2,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_2325,plain,
    ( r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1913,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2)
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1914,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_39,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_50,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_41,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_48,plain,
    ( r1_tarski(sK2,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43430,c_19781,c_4010,c_2654,c_2325,c_1914,c_50,c_48,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:11:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.77/2.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.77/2.02  
% 11.77/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.77/2.02  
% 11.77/2.02  ------  iProver source info
% 11.77/2.02  
% 11.77/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.77/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.77/2.02  git: non_committed_changes: false
% 11.77/2.02  git: last_make_outside_of_git: false
% 11.77/2.02  
% 11.77/2.02  ------ 
% 11.77/2.02  ------ Parsing...
% 11.77/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.77/2.02  
% 11.77/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.77/2.02  
% 11.77/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.77/2.02  
% 11.77/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.77/2.02  ------ Proving...
% 11.77/2.02  ------ Problem Properties 
% 11.77/2.02  
% 11.77/2.02  
% 11.77/2.02  clauses                                 44
% 11.77/2.02  conjectures                             6
% 11.77/2.02  EPR                                     10
% 11.77/2.02  Horn                                    39
% 11.77/2.02  unary                                   15
% 11.77/2.02  binary                                  15
% 11.77/2.02  lits                                    91
% 11.77/2.02  lits eq                                 21
% 11.77/2.02  fd_pure                                 0
% 11.77/2.02  fd_pseudo                               0
% 11.77/2.02  fd_cond                                 1
% 11.77/2.02  fd_pseudo_cond                          4
% 11.77/2.02  AC symbols                              0
% 11.77/2.02  
% 11.77/2.02  ------ Input Options Time Limit: Unbounded
% 11.77/2.02  
% 11.77/2.02  
% 11.77/2.02  ------ 
% 11.77/2.02  Current options:
% 11.77/2.02  ------ 
% 11.77/2.02  
% 11.77/2.02  
% 11.77/2.02  
% 11.77/2.02  
% 11.77/2.02  ------ Proving...
% 11.77/2.02  
% 11.77/2.02  
% 11.77/2.02  % SZS status Theorem for theBenchmark.p
% 11.77/2.02  
% 11.77/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.77/2.02  
% 11.77/2.02  fof(f29,conjecture,(
% 11.77/2.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f30,negated_conjecture,(
% 11.77/2.02    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.77/2.02    inference(negated_conjecture,[],[f29])).
% 11.77/2.02  
% 11.77/2.02  fof(f53,plain,(
% 11.77/2.02    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.77/2.02    inference(ennf_transformation,[],[f30])).
% 11.77/2.02  
% 11.77/2.02  fof(f54,plain,(
% 11.77/2.02    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.77/2.02    inference(flattening,[],[f53])).
% 11.77/2.02  
% 11.77/2.02  fof(f68,plain,(
% 11.77/2.02    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK2,sK3) & v2_funct_1(sK4) & r1_tarski(sK2,k1_relat_1(sK4)) & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 11.77/2.02    introduced(choice_axiom,[])).
% 11.77/2.02  
% 11.77/2.02  fof(f69,plain,(
% 11.77/2.02    ~r1_tarski(sK2,sK3) & v2_funct_1(sK4) & r1_tarski(sK2,k1_relat_1(sK4)) & r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 11.77/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f54,f68])).
% 11.77/2.02  
% 11.77/2.02  fof(f114,plain,(
% 11.77/2.02    v2_funct_1(sK4)),
% 11.77/2.02    inference(cnf_transformation,[],[f69])).
% 11.77/2.02  
% 11.77/2.02  fof(f27,axiom,(
% 11.77/2.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0)))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f49,plain,(
% 11.77/2.02    ! [X0,X1] : ((k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.77/2.02    inference(ennf_transformation,[],[f27])).
% 11.77/2.02  
% 11.77/2.02  fof(f50,plain,(
% 11.77/2.02    ! [X0,X1] : (k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.77/2.02    inference(flattening,[],[f49])).
% 11.77/2.02  
% 11.77/2.02  fof(f108,plain,(
% 11.77/2.02    ( ! [X0,X1] : (k10_relat_1(k2_funct_1(X1),X0) = k9_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f50])).
% 11.77/2.02  
% 11.77/2.02  fof(f110,plain,(
% 11.77/2.02    v1_relat_1(sK4)),
% 11.77/2.02    inference(cnf_transformation,[],[f69])).
% 11.77/2.02  
% 11.77/2.02  fof(f111,plain,(
% 11.77/2.02    v1_funct_1(sK4)),
% 11.77/2.02    inference(cnf_transformation,[],[f69])).
% 11.77/2.02  
% 11.77/2.02  fof(f25,axiom,(
% 11.77/2.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f45,plain,(
% 11.77/2.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.77/2.02    inference(ennf_transformation,[],[f25])).
% 11.77/2.02  
% 11.77/2.02  fof(f46,plain,(
% 11.77/2.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.77/2.02    inference(flattening,[],[f45])).
% 11.77/2.02  
% 11.77/2.02  fof(f106,plain,(
% 11.77/2.02    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f46])).
% 11.77/2.02  
% 11.77/2.02  fof(f28,axiom,(
% 11.77/2.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f51,plain,(
% 11.77/2.02    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.77/2.02    inference(ennf_transformation,[],[f28])).
% 11.77/2.02  
% 11.77/2.02  fof(f52,plain,(
% 11.77/2.02    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.77/2.02    inference(flattening,[],[f51])).
% 11.77/2.02  
% 11.77/2.02  fof(f109,plain,(
% 11.77/2.02    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f52])).
% 11.77/2.02  
% 11.77/2.02  fof(f22,axiom,(
% 11.77/2.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f39,plain,(
% 11.77/2.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.77/2.02    inference(ennf_transformation,[],[f22])).
% 11.77/2.02  
% 11.77/2.02  fof(f40,plain,(
% 11.77/2.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.77/2.02    inference(flattening,[],[f39])).
% 11.77/2.02  
% 11.77/2.02  fof(f103,plain,(
% 11.77/2.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f40])).
% 11.77/2.02  
% 11.77/2.02  fof(f102,plain,(
% 11.77/2.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f40])).
% 11.77/2.02  
% 11.77/2.02  fof(f112,plain,(
% 11.77/2.02    r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),
% 11.77/2.02    inference(cnf_transformation,[],[f69])).
% 11.77/2.02  
% 11.77/2.02  fof(f10,axiom,(
% 11.77/2.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f34,plain,(
% 11.77/2.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.77/2.02    inference(ennf_transformation,[],[f10])).
% 11.77/2.02  
% 11.77/2.02  fof(f90,plain,(
% 11.77/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f34])).
% 11.77/2.02  
% 11.77/2.02  fof(f21,axiom,(
% 11.77/2.02    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f38,plain,(
% 11.77/2.02    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.77/2.02    inference(ennf_transformation,[],[f21])).
% 11.77/2.02  
% 11.77/2.02  fof(f101,plain,(
% 11.77/2.02    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f38])).
% 11.77/2.02  
% 11.77/2.02  fof(f9,axiom,(
% 11.77/2.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f33,plain,(
% 11.77/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.77/2.02    inference(ennf_transformation,[],[f9])).
% 11.77/2.02  
% 11.77/2.02  fof(f89,plain,(
% 11.77/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f33])).
% 11.77/2.02  
% 11.77/2.02  fof(f2,axiom,(
% 11.77/2.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f31,plain,(
% 11.77/2.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.77/2.02    inference(ennf_transformation,[],[f2])).
% 11.77/2.02  
% 11.77/2.02  fof(f55,plain,(
% 11.77/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.77/2.02    inference(nnf_transformation,[],[f31])).
% 11.77/2.02  
% 11.77/2.02  fof(f56,plain,(
% 11.77/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.77/2.02    inference(rectify,[],[f55])).
% 11.77/2.02  
% 11.77/2.02  fof(f57,plain,(
% 11.77/2.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.77/2.02    introduced(choice_axiom,[])).
% 11.77/2.02  
% 11.77/2.02  fof(f58,plain,(
% 11.77/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.77/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).
% 11.77/2.02  
% 11.77/2.02  fof(f71,plain,(
% 11.77/2.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f58])).
% 11.77/2.02  
% 11.77/2.02  fof(f73,plain,(
% 11.77/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f58])).
% 11.77/2.02  
% 11.77/2.02  fof(f26,axiom,(
% 11.77/2.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 11.77/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.02  
% 11.77/2.02  fof(f47,plain,(
% 11.77/2.02    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.77/2.02    inference(ennf_transformation,[],[f26])).
% 11.77/2.02  
% 11.77/2.02  fof(f48,plain,(
% 11.77/2.02    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.77/2.02    inference(flattening,[],[f47])).
% 11.77/2.02  
% 11.77/2.02  fof(f107,plain,(
% 11.77/2.02    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f48])).
% 11.77/2.02  
% 11.77/2.02  fof(f72,plain,(
% 11.77/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.77/2.02    inference(cnf_transformation,[],[f58])).
% 11.77/2.02  
% 11.77/2.02  fof(f115,plain,(
% 11.77/2.02    ~r1_tarski(sK2,sK3)),
% 11.77/2.02    inference(cnf_transformation,[],[f69])).
% 11.77/2.02  
% 11.77/2.02  fof(f113,plain,(
% 11.77/2.02    r1_tarski(sK2,k1_relat_1(sK4))),
% 11.77/2.02    inference(cnf_transformation,[],[f69])).
% 11.77/2.02  
% 11.77/2.02  cnf(c_40,negated_conjecture,
% 11.77/2.02      ( v2_funct_1(sK4) ),
% 11.77/2.02      inference(cnf_transformation,[],[f114]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1541,plain,
% 11.77/2.02      ( v2_funct_1(sK4) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_37,plain,
% 11.77/2.02      ( ~ v2_funct_1(X0)
% 11.77/2.02      | ~ v1_funct_1(X0)
% 11.77/2.02      | ~ v1_relat_1(X0)
% 11.77/2.02      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 11.77/2.02      inference(cnf_transformation,[],[f108]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1544,plain,
% 11.77/2.02      ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 11.77/2.02      | v2_funct_1(X0) != iProver_top
% 11.77/2.02      | v1_funct_1(X0) != iProver_top
% 11.77/2.02      | v1_relat_1(X0) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2962,plain,
% 11.77/2.02      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
% 11.77/2.02      | v1_funct_1(sK4) != iProver_top
% 11.77/2.02      | v1_relat_1(sK4) != iProver_top ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_1541,c_1544]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_44,negated_conjecture,
% 11.77/2.02      ( v1_relat_1(sK4) ),
% 11.77/2.02      inference(cnf_transformation,[],[f110]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_43,negated_conjecture,
% 11.77/2.02      ( v1_funct_1(sK4) ),
% 11.77/2.02      inference(cnf_transformation,[],[f111]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1969,plain,
% 11.77/2.02      ( ~ v2_funct_1(sK4)
% 11.77/2.02      | ~ v1_funct_1(sK4)
% 11.77/2.02      | ~ v1_relat_1(sK4)
% 11.77/2.02      | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_37]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_4031,plain,
% 11.77/2.02      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 11.77/2.02      inference(global_propositional_subsumption,
% 11.77/2.02                [status(thm)],
% 11.77/2.02                [c_2962,c_44,c_43,c_40,c_1969]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_35,plain,
% 11.77/2.02      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 11.77/2.02      | ~ v1_funct_1(X0)
% 11.77/2.02      | ~ v1_relat_1(X0) ),
% 11.77/2.02      inference(cnf_transformation,[],[f106]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1546,plain,
% 11.77/2.02      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 11.77/2.02      | v1_funct_1(X0) != iProver_top
% 11.77/2.02      | v1_relat_1(X0) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_5450,plain,
% 11.77/2.02      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
% 11.77/2.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 11.77/2.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_4031,c_1546]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_38,plain,
% 11.77/2.02      ( ~ v2_funct_1(X0)
% 11.77/2.02      | ~ v1_funct_1(X0)
% 11.77/2.02      | ~ v1_relat_1(X0)
% 11.77/2.02      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 11.77/2.02      inference(cnf_transformation,[],[f109]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1543,plain,
% 11.77/2.02      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 11.77/2.02      | v2_funct_1(X0) != iProver_top
% 11.77/2.02      | v1_funct_1(X0) != iProver_top
% 11.77/2.02      | v1_relat_1(X0) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2034,plain,
% 11.77/2.02      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
% 11.77/2.02      | v1_funct_1(sK4) != iProver_top
% 11.77/2.02      | v1_relat_1(sK4) != iProver_top ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_1541,c_1543]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1974,plain,
% 11.77/2.02      ( ~ v2_funct_1(sK4)
% 11.77/2.02      | ~ v1_funct_1(sK4)
% 11.77/2.02      | ~ v1_relat_1(sK4)
% 11.77/2.02      | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_38]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2257,plain,
% 11.77/2.02      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 11.77/2.02      inference(global_propositional_subsumption,
% 11.77/2.02                [status(thm)],
% 11.77/2.02                [c_2034,c_44,c_43,c_40,c_1974]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_5475,plain,
% 11.77/2.02      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
% 11.77/2.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 11.77/2.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 11.77/2.02      inference(demodulation,[status(thm)],[c_5450,c_2257]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_45,plain,
% 11.77/2.02      ( v1_relat_1(sK4) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_46,plain,
% 11.77/2.02      ( v1_funct_1(sK4) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_31,plain,
% 11.77/2.02      ( ~ v1_funct_1(X0)
% 11.77/2.02      | v1_funct_1(k2_funct_1(X0))
% 11.77/2.02      | ~ v1_relat_1(X0) ),
% 11.77/2.02      inference(cnf_transformation,[],[f103]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1876,plain,
% 11.77/2.02      ( v1_funct_1(k2_funct_1(sK4))
% 11.77/2.02      | ~ v1_funct_1(sK4)
% 11.77/2.02      | ~ v1_relat_1(sK4) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_31]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1877,plain,
% 11.77/2.02      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 11.77/2.02      | v1_funct_1(sK4) != iProver_top
% 11.77/2.02      | v1_relat_1(sK4) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_1876]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_32,plain,
% 11.77/2.02      ( ~ v1_funct_1(X0)
% 11.77/2.02      | ~ v1_relat_1(X0)
% 11.77/2.02      | v1_relat_1(k2_funct_1(X0)) ),
% 11.77/2.02      inference(cnf_transformation,[],[f102]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1895,plain,
% 11.77/2.02      ( ~ v1_funct_1(sK4)
% 11.77/2.02      | v1_relat_1(k2_funct_1(sK4))
% 11.77/2.02      | ~ v1_relat_1(sK4) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_32]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1896,plain,
% 11.77/2.02      ( v1_funct_1(sK4) != iProver_top
% 11.77/2.02      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 11.77/2.02      | v1_relat_1(sK4) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_42433,plain,
% 11.77/2.02      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top ),
% 11.77/2.02      inference(global_propositional_subsumption,
% 11.77/2.02                [status(thm)],
% 11.77/2.02                [c_5475,c_45,c_46,c_1877,c_1896]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_42,negated_conjecture,
% 11.77/2.02      ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 11.77/2.02      inference(cnf_transformation,[],[f112]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1539,plain,
% 11.77/2.02      ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_20,plain,
% 11.77/2.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.77/2.02      inference(cnf_transformation,[],[f90]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1558,plain,
% 11.77/2.02      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_3422,plain,
% 11.77/2.02      ( k2_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = k9_relat_1(sK4,sK3) ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_1539,c_1558]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1537,plain,
% 11.77/2.02      ( v1_relat_1(sK4) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_30,plain,
% 11.77/2.02      ( ~ v1_relat_1(X0)
% 11.77/2.02      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 11.77/2.02      inference(cnf_transformation,[],[f101]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1551,plain,
% 11.77/2.02      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 11.77/2.02      | v1_relat_1(X0) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_10009,plain,
% 11.77/2.02      ( k2_xboole_0(k10_relat_1(sK4,X0),k10_relat_1(sK4,X1)) = k10_relat_1(sK4,k2_xboole_0(X0,X1)) ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_1537,c_1551]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_19,plain,
% 11.77/2.02      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.77/2.02      inference(cnf_transformation,[],[f89]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1559,plain,
% 11.77/2.02      ( r1_tarski(X0,X1) = iProver_top
% 11.77/2.02      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_11199,plain,
% 11.77/2.02      ( r1_tarski(k10_relat_1(sK4,X0),X1) = iProver_top
% 11.77/2.02      | r1_tarski(k10_relat_1(sK4,k2_xboole_0(X0,X2)),X1) != iProver_top ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_10009,c_1559]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_27386,plain,
% 11.77/2.02      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK3)),X0) != iProver_top
% 11.77/2.02      | r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),X0) = iProver_top ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_3422,c_11199]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_43430,plain,
% 11.77/2.02      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),sK3) = iProver_top ),
% 11.77/2.02      inference(superposition,[status(thm)],[c_42433,c_27386]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_4,plain,
% 11.77/2.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.77/2.02      inference(cnf_transformation,[],[f71]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2658,plain,
% 11.77/2.02      ( ~ r2_hidden(sK0(sK2,sK3),X0)
% 11.77/2.02      | r2_hidden(sK0(sK2,sK3),X1)
% 11.77/2.02      | ~ r1_tarski(X0,X1) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_4]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_7572,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),X0)
% 11.77/2.02      | ~ r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
% 11.77/2.02      | ~ r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),X0) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_2658]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_19778,plain,
% 11.77/2.02      ( ~ r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
% 11.77/2.02      | r2_hidden(sK0(sK2,sK3),sK3)
% 11.77/2.02      | ~ r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),sK3) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_7572]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_19781,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2))) != iProver_top
% 11.77/2.02      | r2_hidden(sK0(sK2,sK3),sK3) = iProver_top
% 11.77/2.02      | r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,sK2)),sK3) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_19778]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2120,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),X0)
% 11.77/2.02      | ~ r2_hidden(sK0(sK2,sK3),sK2)
% 11.77/2.02      | ~ r1_tarski(sK2,X0) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_4]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_4009,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
% 11.77/2.02      | ~ r2_hidden(sK0(sK2,sK3),sK2)
% 11.77/2.02      | ~ r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2))) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_2120]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_4010,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),k10_relat_1(sK4,k9_relat_1(sK4,sK2))) = iProver_top
% 11.77/2.02      | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
% 11.77/2.02      | r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2))) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_4009]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2,plain,
% 11.77/2.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.77/2.02      inference(cnf_transformation,[],[f73]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2651,plain,
% 11.77/2.02      ( ~ r2_hidden(sK0(sK2,sK3),sK3) | r1_tarski(sK2,sK3) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_2]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2654,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),sK3) != iProver_top
% 11.77/2.02      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_36,plain,
% 11.77/2.02      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 11.77/2.02      | ~ r1_tarski(X0,k1_relat_1(X1))
% 11.77/2.02      | ~ v1_relat_1(X1) ),
% 11.77/2.02      inference(cnf_transformation,[],[f107]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1944,plain,
% 11.77/2.02      ( r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0)))
% 11.77/2.02      | ~ r1_tarski(X0,k1_relat_1(sK4))
% 11.77/2.02      | ~ v1_relat_1(sK4) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_36]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2324,plain,
% 11.77/2.02      ( r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2)))
% 11.77/2.02      | ~ r1_tarski(sK2,k1_relat_1(sK4))
% 11.77/2.02      | ~ v1_relat_1(sK4) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_1944]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_2325,plain,
% 11.77/2.02      ( r1_tarski(sK2,k10_relat_1(sK4,k9_relat_1(sK4,sK2))) = iProver_top
% 11.77/2.02      | r1_tarski(sK2,k1_relat_1(sK4)) != iProver_top
% 11.77/2.02      | v1_relat_1(sK4) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_2324]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_3,plain,
% 11.77/2.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.77/2.02      inference(cnf_transformation,[],[f72]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1913,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),sK2) | r1_tarski(sK2,sK3) ),
% 11.77/2.02      inference(instantiation,[status(thm)],[c_3]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_1914,plain,
% 11.77/2.02      ( r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
% 11.77/2.02      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_39,negated_conjecture,
% 11.77/2.02      ( ~ r1_tarski(sK2,sK3) ),
% 11.77/2.02      inference(cnf_transformation,[],[f115]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_50,plain,
% 11.77/2.02      ( r1_tarski(sK2,sK3) != iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_41,negated_conjecture,
% 11.77/2.02      ( r1_tarski(sK2,k1_relat_1(sK4)) ),
% 11.77/2.02      inference(cnf_transformation,[],[f113]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(c_48,plain,
% 11.77/2.02      ( r1_tarski(sK2,k1_relat_1(sK4)) = iProver_top ),
% 11.77/2.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.77/2.02  
% 11.77/2.02  cnf(contradiction,plain,
% 11.77/2.02      ( $false ),
% 11.77/2.02      inference(minisat,
% 11.77/2.02                [status(thm)],
% 11.77/2.02                [c_43430,c_19781,c_4010,c_2654,c_2325,c_1914,c_50,c_48,
% 11.77/2.02                 c_45]) ).
% 11.77/2.02  
% 11.77/2.02  
% 11.77/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.77/2.02  
% 11.77/2.02  ------                               Statistics
% 11.77/2.02  
% 11.77/2.02  ------ Selected
% 11.77/2.02  
% 11.77/2.02  total_time:                             1.191
% 11.77/2.02  
%------------------------------------------------------------------------------
