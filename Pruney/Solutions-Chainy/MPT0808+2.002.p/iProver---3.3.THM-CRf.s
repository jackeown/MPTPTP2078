%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:36 EST 2020

% Result     : Theorem 1.27s
% Output     : CNFRefutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 324 expanded)
%              Number of clauses        :   62 (  81 expanded)
%              Number of leaves         :   10 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  420 (2568 expanded)
%              Number of equality atoms :   73 (  84 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => ! [X3] :
                      ~ ( ! [X4] :
                            ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                              & r2_hidden(X4,k3_relat_1(X1)) )
                        & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
              | ~ r2_hidden(X4,k3_relat_1(X1)) )
          & r2_hidden(X3,k3_relat_1(X0)) )
     => ( ! [X4] :
            ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,sK4)),k2_wellord1(X1,k1_wellord1(X1,X4)))
            | ~ r2_hidden(X4,k3_relat_1(X1)) )
        & r2_hidden(sK4,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                  | ~ r2_hidden(X4,k3_relat_1(X1)) )
              & r2_hidden(X3,k3_relat_1(X0)) )
          & r3_wellord1(X0,X1,X2)
          & v2_wellord1(X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            & r2_hidden(X3,k3_relat_1(X0)) )
        & r3_wellord1(X0,X1,sK3)
        & v2_wellord1(X0)
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(sK2,k1_wellord1(sK2,X4)))
                    | ~ r2_hidden(X4,k3_relat_1(sK2)) )
                & r2_hidden(X3,k3_relat_1(X0)) )
            & r3_wellord1(X0,sK2,X2)
            & v2_wellord1(X0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                        | ~ r2_hidden(X4,k3_relat_1(X1)) )
                    & r2_hidden(X3,k3_relat_1(X0)) )
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(sK1)) )
              & r3_wellord1(sK1,X1,X2)
              & v2_wellord1(sK1)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ! [X4] :
        ( ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X4)))
        | ~ r2_hidden(X4,k3_relat_1(sK2)) )
    & r2_hidden(sK4,k3_relat_1(sK1))
    & r3_wellord1(sK1,sK2,sK3)
    & v2_wellord1(sK1)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f21,f20,f19,f18])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( r3_wellord1(X1,X2,X3)
                  & r1_tarski(X0,k3_relat_1(X1))
                  & v2_wellord1(X1) )
               => ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                  & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
      | ~ r3_wellord1(X1,X2,X3)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    r2_hidden(sK4,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    r3_wellord1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
          & r2_hidden(X4,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
        & r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
                    & r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f16])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X4] :
      ( ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X4)))
      | ~ r2_hidden(X4,k3_relat_1(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r4_wellord1(k2_wellord1(X0,X3),k2_wellord1(X1,k9_relat_1(X2,X3)))
    | ~ r1_tarski(X3,k3_relat_1(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,negated_conjecture,
    ( v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_241,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r4_wellord1(k2_wellord1(X0,X3),k2_wellord1(X1,k9_relat_1(X2,X3)))
    | ~ r1_tarski(X3,k3_relat_1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_242,plain,
    ( ~ r3_wellord1(sK1,X0,X1)
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_246,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r3_wellord1(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_14])).

cnf(c_247,plain,
    ( ~ r3_wellord1(sK1,X0,X1)
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_410,plain,
    ( ~ r3_wellord1(sK1,X0,X1)
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_247])).

cnf(c_411,plain,
    ( ~ r3_wellord1(sK1,X0,sK3)
    | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
    | ~ r1_tarski(X1,k3_relat_1(sK1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_415,plain,
    ( ~ v1_relat_1(X0)
    | ~ r1_tarski(X1,k3_relat_1(sK1))
    | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
    | ~ r3_wellord1(sK1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_12])).

cnf(c_416,plain,
    ( ~ r3_wellord1(sK1,X0,sK3)
    | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
    | ~ r1_tarski(X1,k3_relat_1(sK1))
    | ~ v1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_785,plain,
    ( ~ r3_wellord1(sK1,X0_45,sK3)
    | r4_wellord1(k2_wellord1(sK1,X0_46),k2_wellord1(X0_45,k9_relat_1(sK3,X0_46)))
    | ~ r1_tarski(X0_46,k3_relat_1(sK1))
    | ~ v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_1094,plain,
    ( r3_wellord1(sK1,X0_45,sK3) != iProver_top
    | r4_wellord1(k2_wellord1(sK1,X0_46),k2_wellord1(X0_45,k9_relat_1(sK3,X0_46))) = iProver_top
    | r1_tarski(X0_46,k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK4,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_794,negated_conjecture,
    ( r2_hidden(sK4,k3_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1086,plain,
    ( r2_hidden(sK4,k3_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_9,negated_conjecture,
    ( r3_wellord1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_793,negated_conjecture,
    ( r3_wellord1(sK1,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1087,plain,
    ( r3_wellord1(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_5,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_383,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_384,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK3)
    | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_388,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ r3_wellord1(X0,X1,sK3)
    | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_12])).

cnf(c_389,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_786,plain,
    ( ~ r3_wellord1(X0_45,X1_45,sK3)
    | ~ r2_hidden(X0_47,k3_relat_1(X0_45))
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45)
    | k1_wellord1(X1_45,sK0(X0_45,X1_45,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(X0_45,X0_47)) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1093,plain,
    ( k1_wellord1(X0_45,sK0(X1_45,X0_45,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(X1_45,X0_47))
    | r3_wellord1(X1_45,X0_45,sK3) != iProver_top
    | r2_hidden(X0_47,k3_relat_1(X1_45)) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_1620,plain,
    ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(sK1,X0_47))
    | r2_hidden(X0_47,k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1093])).

cnf(c_15,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1702,plain,
    ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(sK1,X0_47))
    | r2_hidden(X0_47,k3_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1620,c_15,c_16])).

cnf(c_1710,plain,
    ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,sK4)) = k9_relat_1(sK3,k1_wellord1(sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_1086,c_1702])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK2))
    | ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_795,negated_conjecture,
    ( ~ r2_hidden(X0_47,k3_relat_1(sK2))
    | ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0_47))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1085,plain,
    ( r2_hidden(X0_47,k3_relat_1(sK2)) != iProver_top
    | r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_1728,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,sK4),k3_relat_1(sK2)) != iProver_top
    | r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k9_relat_1(sK3,k1_wellord1(sK1,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1710,c_1085])).

cnf(c_20,plain,
    ( r3_wellord1(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_21,plain,
    ( r2_hidden(sK4,k3_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_356,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_357,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_361,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ r3_wellord1(X0,X1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_12])).

cnf(c_362,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_787,plain,
    ( ~ r3_wellord1(X0_45,X1_45,sK3)
    | ~ r2_hidden(X0_47,k3_relat_1(X0_45))
    | r2_hidden(sK0(X0_45,X1_45,sK3,X0_47),k3_relat_1(X1_45))
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_1194,plain,
    ( ~ r3_wellord1(sK1,sK2,sK3)
    | ~ r2_hidden(X0_47,k3_relat_1(sK1))
    | r2_hidden(sK0(sK1,sK2,sK3,X0_47),k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1195,plain,
    ( r3_wellord1(sK1,sK2,sK3) != iProver_top
    | r2_hidden(X0_47,k3_relat_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3,X0_47),k3_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1194])).

cnf(c_1197,plain,
    ( r3_wellord1(sK1,sK2,sK3) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3,sK4),k3_relat_1(sK2)) = iProver_top
    | r2_hidden(sK4,k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_1821,plain,
    ( r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k9_relat_1(sK3,k1_wellord1(sK1,sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_15,c_16,c_20,c_21,c_1197])).

cnf(c_1826,plain,
    ( r3_wellord1(sK1,sK2,sK3) != iProver_top
    | r1_tarski(k1_wellord1(sK1,sK4),k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1821])).

cnf(c_2,plain,
    ( ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_269,plain,
    ( ~ v1_relat_1(X0)
    | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_270,plain,
    ( ~ v1_relat_1(sK1)
    | k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) = k1_wellord1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_274,plain,
    ( k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) = k1_wellord1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_14])).

cnf(c_789,plain,
    ( k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0_47))) = k1_wellord1(sK1,X0_47) ),
    inference(subtyping,[status(esa)],[c_274])).

cnf(c_1,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_796,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_45,X0_46)),k3_relat_1(X0_45))
    | ~ v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1084,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_45,X0_46)),k3_relat_1(X0_45)) = iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_1374,plain,
    ( r1_tarski(k1_wellord1(sK1,X0_47),k3_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_1084])).

cnf(c_1385,plain,
    ( r1_tarski(k1_wellord1(sK1,sK4),k3_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1826,c_1385,c_20,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.27/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.27/1.05  
% 1.27/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.27/1.05  
% 1.27/1.05  ------  iProver source info
% 1.27/1.05  
% 1.27/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.27/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.27/1.05  git: non_committed_changes: false
% 1.27/1.05  git: last_make_outside_of_git: false
% 1.27/1.05  
% 1.27/1.05  ------ 
% 1.27/1.05  
% 1.27/1.05  ------ Input Options
% 1.27/1.05  
% 1.27/1.05  --out_options                           all
% 1.27/1.05  --tptp_safe_out                         true
% 1.27/1.05  --problem_path                          ""
% 1.27/1.05  --include_path                          ""
% 1.27/1.05  --clausifier                            res/vclausify_rel
% 1.27/1.05  --clausifier_options                    --mode clausify
% 1.27/1.05  --stdin                                 false
% 1.27/1.05  --stats_out                             all
% 1.27/1.05  
% 1.27/1.05  ------ General Options
% 1.27/1.05  
% 1.27/1.05  --fof                                   false
% 1.27/1.05  --time_out_real                         305.
% 1.27/1.05  --time_out_virtual                      -1.
% 1.27/1.05  --symbol_type_check                     false
% 1.27/1.05  --clausify_out                          false
% 1.27/1.05  --sig_cnt_out                           false
% 1.27/1.05  --trig_cnt_out                          false
% 1.27/1.05  --trig_cnt_out_tolerance                1.
% 1.27/1.05  --trig_cnt_out_sk_spl                   false
% 1.27/1.05  --abstr_cl_out                          false
% 1.27/1.05  
% 1.27/1.05  ------ Global Options
% 1.27/1.05  
% 1.27/1.05  --schedule                              default
% 1.27/1.05  --add_important_lit                     false
% 1.27/1.05  --prop_solver_per_cl                    1000
% 1.27/1.05  --min_unsat_core                        false
% 1.27/1.05  --soft_assumptions                      false
% 1.27/1.05  --soft_lemma_size                       3
% 1.27/1.05  --prop_impl_unit_size                   0
% 1.27/1.05  --prop_impl_unit                        []
% 1.27/1.05  --share_sel_clauses                     true
% 1.27/1.05  --reset_solvers                         false
% 1.27/1.05  --bc_imp_inh                            [conj_cone]
% 1.27/1.05  --conj_cone_tolerance                   3.
% 1.27/1.05  --extra_neg_conj                        none
% 1.27/1.05  --large_theory_mode                     true
% 1.27/1.05  --prolific_symb_bound                   200
% 1.27/1.05  --lt_threshold                          2000
% 1.27/1.05  --clause_weak_htbl                      true
% 1.27/1.05  --gc_record_bc_elim                     false
% 1.27/1.05  
% 1.27/1.05  ------ Preprocessing Options
% 1.27/1.05  
% 1.27/1.05  --preprocessing_flag                    true
% 1.27/1.05  --time_out_prep_mult                    0.1
% 1.27/1.05  --splitting_mode                        input
% 1.27/1.05  --splitting_grd                         true
% 1.27/1.05  --splitting_cvd                         false
% 1.27/1.05  --splitting_cvd_svl                     false
% 1.27/1.05  --splitting_nvd                         32
% 1.27/1.05  --sub_typing                            true
% 1.27/1.05  --prep_gs_sim                           true
% 1.27/1.05  --prep_unflatten                        true
% 1.27/1.05  --prep_res_sim                          true
% 1.27/1.05  --prep_upred                            true
% 1.27/1.05  --prep_sem_filter                       exhaustive
% 1.27/1.05  --prep_sem_filter_out                   false
% 1.27/1.05  --pred_elim                             true
% 1.27/1.05  --res_sim_input                         true
% 1.27/1.05  --eq_ax_congr_red                       true
% 1.27/1.05  --pure_diseq_elim                       true
% 1.27/1.05  --brand_transform                       false
% 1.27/1.05  --non_eq_to_eq                          false
% 1.27/1.05  --prep_def_merge                        true
% 1.27/1.05  --prep_def_merge_prop_impl              false
% 1.27/1.05  --prep_def_merge_mbd                    true
% 1.27/1.05  --prep_def_merge_tr_red                 false
% 1.27/1.05  --prep_def_merge_tr_cl                  false
% 1.27/1.05  --smt_preprocessing                     true
% 1.27/1.05  --smt_ac_axioms                         fast
% 1.27/1.05  --preprocessed_out                      false
% 1.27/1.05  --preprocessed_stats                    false
% 1.27/1.05  
% 1.27/1.05  ------ Abstraction refinement Options
% 1.27/1.05  
% 1.27/1.05  --abstr_ref                             []
% 1.27/1.05  --abstr_ref_prep                        false
% 1.27/1.05  --abstr_ref_until_sat                   false
% 1.27/1.05  --abstr_ref_sig_restrict                funpre
% 1.27/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.27/1.05  --abstr_ref_under                       []
% 1.27/1.05  
% 1.27/1.05  ------ SAT Options
% 1.27/1.05  
% 1.27/1.05  --sat_mode                              false
% 1.27/1.05  --sat_fm_restart_options                ""
% 1.27/1.05  --sat_gr_def                            false
% 1.27/1.05  --sat_epr_types                         true
% 1.27/1.05  --sat_non_cyclic_types                  false
% 1.27/1.05  --sat_finite_models                     false
% 1.27/1.05  --sat_fm_lemmas                         false
% 1.27/1.05  --sat_fm_prep                           false
% 1.27/1.05  --sat_fm_uc_incr                        true
% 1.27/1.05  --sat_out_model                         small
% 1.27/1.05  --sat_out_clauses                       false
% 1.27/1.05  
% 1.27/1.05  ------ QBF Options
% 1.27/1.05  
% 1.27/1.05  --qbf_mode                              false
% 1.27/1.05  --qbf_elim_univ                         false
% 1.27/1.05  --qbf_dom_inst                          none
% 1.27/1.05  --qbf_dom_pre_inst                      false
% 1.27/1.05  --qbf_sk_in                             false
% 1.27/1.05  --qbf_pred_elim                         true
% 1.27/1.05  --qbf_split                             512
% 1.27/1.05  
% 1.27/1.05  ------ BMC1 Options
% 1.27/1.05  
% 1.27/1.05  --bmc1_incremental                      false
% 1.27/1.05  --bmc1_axioms                           reachable_all
% 1.27/1.05  --bmc1_min_bound                        0
% 1.27/1.05  --bmc1_max_bound                        -1
% 1.27/1.05  --bmc1_max_bound_default                -1
% 1.27/1.05  --bmc1_symbol_reachability              true
% 1.27/1.05  --bmc1_property_lemmas                  false
% 1.27/1.05  --bmc1_k_induction                      false
% 1.27/1.05  --bmc1_non_equiv_states                 false
% 1.27/1.05  --bmc1_deadlock                         false
% 1.27/1.05  --bmc1_ucm                              false
% 1.27/1.05  --bmc1_add_unsat_core                   none
% 1.27/1.05  --bmc1_unsat_core_children              false
% 1.27/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.27/1.05  --bmc1_out_stat                         full
% 1.27/1.05  --bmc1_ground_init                      false
% 1.27/1.05  --bmc1_pre_inst_next_state              false
% 1.27/1.05  --bmc1_pre_inst_state                   false
% 1.27/1.05  --bmc1_pre_inst_reach_state             false
% 1.27/1.05  --bmc1_out_unsat_core                   false
% 1.27/1.05  --bmc1_aig_witness_out                  false
% 1.27/1.05  --bmc1_verbose                          false
% 1.27/1.05  --bmc1_dump_clauses_tptp                false
% 1.27/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.27/1.05  --bmc1_dump_file                        -
% 1.27/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.27/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.27/1.05  --bmc1_ucm_extend_mode                  1
% 1.27/1.05  --bmc1_ucm_init_mode                    2
% 1.27/1.05  --bmc1_ucm_cone_mode                    none
% 1.27/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.27/1.05  --bmc1_ucm_relax_model                  4
% 1.27/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.27/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.27/1.05  --bmc1_ucm_layered_model                none
% 1.27/1.05  --bmc1_ucm_max_lemma_size               10
% 1.27/1.05  
% 1.27/1.05  ------ AIG Options
% 1.27/1.05  
% 1.27/1.05  --aig_mode                              false
% 1.27/1.05  
% 1.27/1.05  ------ Instantiation Options
% 1.27/1.05  
% 1.27/1.05  --instantiation_flag                    true
% 1.27/1.05  --inst_sos_flag                         false
% 1.27/1.05  --inst_sos_phase                        true
% 1.27/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.27/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.27/1.05  --inst_lit_sel_side                     num_symb
% 1.27/1.05  --inst_solver_per_active                1400
% 1.27/1.05  --inst_solver_calls_frac                1.
% 1.27/1.05  --inst_passive_queue_type               priority_queues
% 1.27/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.27/1.05  --inst_passive_queues_freq              [25;2]
% 1.27/1.05  --inst_dismatching                      true
% 1.27/1.05  --inst_eager_unprocessed_to_passive     true
% 1.27/1.05  --inst_prop_sim_given                   true
% 1.27/1.05  --inst_prop_sim_new                     false
% 1.27/1.05  --inst_subs_new                         false
% 1.27/1.05  --inst_eq_res_simp                      false
% 1.27/1.05  --inst_subs_given                       false
% 1.27/1.05  --inst_orphan_elimination               true
% 1.27/1.05  --inst_learning_loop_flag               true
% 1.27/1.05  --inst_learning_start                   3000
% 1.27/1.05  --inst_learning_factor                  2
% 1.27/1.05  --inst_start_prop_sim_after_learn       3
% 1.27/1.05  --inst_sel_renew                        solver
% 1.27/1.05  --inst_lit_activity_flag                true
% 1.27/1.05  --inst_restr_to_given                   false
% 1.27/1.05  --inst_activity_threshold               500
% 1.27/1.05  --inst_out_proof                        true
% 1.27/1.05  
% 1.27/1.05  ------ Resolution Options
% 1.27/1.05  
% 1.27/1.05  --resolution_flag                       true
% 1.27/1.05  --res_lit_sel                           adaptive
% 1.27/1.05  --res_lit_sel_side                      none
% 1.27/1.05  --res_ordering                          kbo
% 1.27/1.05  --res_to_prop_solver                    active
% 1.27/1.05  --res_prop_simpl_new                    false
% 1.27/1.05  --res_prop_simpl_given                  true
% 1.27/1.05  --res_passive_queue_type                priority_queues
% 1.27/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.27/1.05  --res_passive_queues_freq               [15;5]
% 1.27/1.05  --res_forward_subs                      full
% 1.27/1.05  --res_backward_subs                     full
% 1.27/1.05  --res_forward_subs_resolution           true
% 1.27/1.05  --res_backward_subs_resolution          true
% 1.27/1.05  --res_orphan_elimination                true
% 1.27/1.05  --res_time_limit                        2.
% 1.27/1.05  --res_out_proof                         true
% 1.27/1.05  
% 1.27/1.05  ------ Superposition Options
% 1.27/1.05  
% 1.27/1.05  --superposition_flag                    true
% 1.27/1.05  --sup_passive_queue_type                priority_queues
% 1.27/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.27/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.27/1.05  --demod_completeness_check              fast
% 1.27/1.05  --demod_use_ground                      true
% 1.27/1.05  --sup_to_prop_solver                    passive
% 1.27/1.05  --sup_prop_simpl_new                    true
% 1.27/1.05  --sup_prop_simpl_given                  true
% 1.27/1.05  --sup_fun_splitting                     false
% 1.27/1.05  --sup_smt_interval                      50000
% 1.27/1.05  
% 1.27/1.05  ------ Superposition Simplification Setup
% 1.27/1.05  
% 1.27/1.05  --sup_indices_passive                   []
% 1.27/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.27/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.05  --sup_full_bw                           [BwDemod]
% 1.27/1.05  --sup_immed_triv                        [TrivRules]
% 1.27/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.27/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.05  --sup_immed_bw_main                     []
% 1.27/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.27/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.05  
% 1.27/1.05  ------ Combination Options
% 1.27/1.05  
% 1.27/1.05  --comb_res_mult                         3
% 1.27/1.05  --comb_sup_mult                         2
% 1.27/1.05  --comb_inst_mult                        10
% 1.27/1.05  
% 1.27/1.05  ------ Debug Options
% 1.27/1.05  
% 1.27/1.05  --dbg_backtrace                         false
% 1.27/1.05  --dbg_dump_prop_clauses                 false
% 1.27/1.05  --dbg_dump_prop_clauses_file            -
% 1.27/1.05  --dbg_out_stat                          false
% 1.27/1.05  ------ Parsing...
% 1.27/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.27/1.05  
% 1.27/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.27/1.05  
% 1.27/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.27/1.05  
% 1.27/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.27/1.05  ------ Proving...
% 1.27/1.05  ------ Problem Properties 
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  clauses                                 13
% 1.27/1.05  conjectures                             6
% 1.27/1.05  EPR                                     4
% 1.27/1.05  Horn                                    13
% 1.27/1.05  unary                                   6
% 1.27/1.05  binary                                  3
% 1.27/1.05  lits                                    30
% 1.27/1.05  lits eq                                 2
% 1.27/1.05  fd_pure                                 0
% 1.27/1.05  fd_pseudo                               0
% 1.27/1.05  fd_cond                                 0
% 1.27/1.05  fd_pseudo_cond                          0
% 1.27/1.05  AC symbols                              0
% 1.27/1.05  
% 1.27/1.05  ------ Schedule dynamic 5 is on 
% 1.27/1.05  
% 1.27/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  ------ 
% 1.27/1.05  Current options:
% 1.27/1.05  ------ 
% 1.27/1.05  
% 1.27/1.05  ------ Input Options
% 1.27/1.05  
% 1.27/1.05  --out_options                           all
% 1.27/1.05  --tptp_safe_out                         true
% 1.27/1.05  --problem_path                          ""
% 1.27/1.05  --include_path                          ""
% 1.27/1.05  --clausifier                            res/vclausify_rel
% 1.27/1.05  --clausifier_options                    --mode clausify
% 1.27/1.05  --stdin                                 false
% 1.27/1.05  --stats_out                             all
% 1.27/1.05  
% 1.27/1.05  ------ General Options
% 1.27/1.05  
% 1.27/1.05  --fof                                   false
% 1.27/1.05  --time_out_real                         305.
% 1.27/1.05  --time_out_virtual                      -1.
% 1.27/1.05  --symbol_type_check                     false
% 1.27/1.05  --clausify_out                          false
% 1.27/1.05  --sig_cnt_out                           false
% 1.27/1.05  --trig_cnt_out                          false
% 1.27/1.05  --trig_cnt_out_tolerance                1.
% 1.27/1.05  --trig_cnt_out_sk_spl                   false
% 1.27/1.05  --abstr_cl_out                          false
% 1.27/1.05  
% 1.27/1.05  ------ Global Options
% 1.27/1.05  
% 1.27/1.05  --schedule                              default
% 1.27/1.05  --add_important_lit                     false
% 1.27/1.05  --prop_solver_per_cl                    1000
% 1.27/1.05  --min_unsat_core                        false
% 1.27/1.05  --soft_assumptions                      false
% 1.27/1.05  --soft_lemma_size                       3
% 1.27/1.05  --prop_impl_unit_size                   0
% 1.27/1.05  --prop_impl_unit                        []
% 1.27/1.05  --share_sel_clauses                     true
% 1.27/1.05  --reset_solvers                         false
% 1.27/1.05  --bc_imp_inh                            [conj_cone]
% 1.27/1.05  --conj_cone_tolerance                   3.
% 1.27/1.05  --extra_neg_conj                        none
% 1.27/1.05  --large_theory_mode                     true
% 1.27/1.05  --prolific_symb_bound                   200
% 1.27/1.05  --lt_threshold                          2000
% 1.27/1.05  --clause_weak_htbl                      true
% 1.27/1.05  --gc_record_bc_elim                     false
% 1.27/1.05  
% 1.27/1.05  ------ Preprocessing Options
% 1.27/1.05  
% 1.27/1.05  --preprocessing_flag                    true
% 1.27/1.05  --time_out_prep_mult                    0.1
% 1.27/1.05  --splitting_mode                        input
% 1.27/1.05  --splitting_grd                         true
% 1.27/1.05  --splitting_cvd                         false
% 1.27/1.05  --splitting_cvd_svl                     false
% 1.27/1.05  --splitting_nvd                         32
% 1.27/1.05  --sub_typing                            true
% 1.27/1.05  --prep_gs_sim                           true
% 1.27/1.05  --prep_unflatten                        true
% 1.27/1.05  --prep_res_sim                          true
% 1.27/1.05  --prep_upred                            true
% 1.27/1.05  --prep_sem_filter                       exhaustive
% 1.27/1.05  --prep_sem_filter_out                   false
% 1.27/1.05  --pred_elim                             true
% 1.27/1.05  --res_sim_input                         true
% 1.27/1.05  --eq_ax_congr_red                       true
% 1.27/1.05  --pure_diseq_elim                       true
% 1.27/1.05  --brand_transform                       false
% 1.27/1.05  --non_eq_to_eq                          false
% 1.27/1.05  --prep_def_merge                        true
% 1.27/1.05  --prep_def_merge_prop_impl              false
% 1.27/1.05  --prep_def_merge_mbd                    true
% 1.27/1.05  --prep_def_merge_tr_red                 false
% 1.27/1.05  --prep_def_merge_tr_cl                  false
% 1.27/1.05  --smt_preprocessing                     true
% 1.27/1.05  --smt_ac_axioms                         fast
% 1.27/1.05  --preprocessed_out                      false
% 1.27/1.05  --preprocessed_stats                    false
% 1.27/1.05  
% 1.27/1.05  ------ Abstraction refinement Options
% 1.27/1.05  
% 1.27/1.05  --abstr_ref                             []
% 1.27/1.05  --abstr_ref_prep                        false
% 1.27/1.05  --abstr_ref_until_sat                   false
% 1.27/1.05  --abstr_ref_sig_restrict                funpre
% 1.27/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.27/1.05  --abstr_ref_under                       []
% 1.27/1.05  
% 1.27/1.05  ------ SAT Options
% 1.27/1.05  
% 1.27/1.05  --sat_mode                              false
% 1.27/1.05  --sat_fm_restart_options                ""
% 1.27/1.05  --sat_gr_def                            false
% 1.27/1.05  --sat_epr_types                         true
% 1.27/1.05  --sat_non_cyclic_types                  false
% 1.27/1.05  --sat_finite_models                     false
% 1.27/1.05  --sat_fm_lemmas                         false
% 1.27/1.05  --sat_fm_prep                           false
% 1.27/1.05  --sat_fm_uc_incr                        true
% 1.27/1.05  --sat_out_model                         small
% 1.27/1.05  --sat_out_clauses                       false
% 1.27/1.05  
% 1.27/1.05  ------ QBF Options
% 1.27/1.05  
% 1.27/1.05  --qbf_mode                              false
% 1.27/1.05  --qbf_elim_univ                         false
% 1.27/1.05  --qbf_dom_inst                          none
% 1.27/1.05  --qbf_dom_pre_inst                      false
% 1.27/1.05  --qbf_sk_in                             false
% 1.27/1.05  --qbf_pred_elim                         true
% 1.27/1.05  --qbf_split                             512
% 1.27/1.05  
% 1.27/1.05  ------ BMC1 Options
% 1.27/1.05  
% 1.27/1.05  --bmc1_incremental                      false
% 1.27/1.05  --bmc1_axioms                           reachable_all
% 1.27/1.05  --bmc1_min_bound                        0
% 1.27/1.05  --bmc1_max_bound                        -1
% 1.27/1.05  --bmc1_max_bound_default                -1
% 1.27/1.05  --bmc1_symbol_reachability              true
% 1.27/1.05  --bmc1_property_lemmas                  false
% 1.27/1.05  --bmc1_k_induction                      false
% 1.27/1.05  --bmc1_non_equiv_states                 false
% 1.27/1.05  --bmc1_deadlock                         false
% 1.27/1.05  --bmc1_ucm                              false
% 1.27/1.05  --bmc1_add_unsat_core                   none
% 1.27/1.05  --bmc1_unsat_core_children              false
% 1.27/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.27/1.05  --bmc1_out_stat                         full
% 1.27/1.05  --bmc1_ground_init                      false
% 1.27/1.05  --bmc1_pre_inst_next_state              false
% 1.27/1.05  --bmc1_pre_inst_state                   false
% 1.27/1.05  --bmc1_pre_inst_reach_state             false
% 1.27/1.05  --bmc1_out_unsat_core                   false
% 1.27/1.05  --bmc1_aig_witness_out                  false
% 1.27/1.05  --bmc1_verbose                          false
% 1.27/1.05  --bmc1_dump_clauses_tptp                false
% 1.27/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.27/1.05  --bmc1_dump_file                        -
% 1.27/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.27/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.27/1.05  --bmc1_ucm_extend_mode                  1
% 1.27/1.05  --bmc1_ucm_init_mode                    2
% 1.27/1.05  --bmc1_ucm_cone_mode                    none
% 1.27/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.27/1.05  --bmc1_ucm_relax_model                  4
% 1.27/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.27/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.27/1.05  --bmc1_ucm_layered_model                none
% 1.27/1.05  --bmc1_ucm_max_lemma_size               10
% 1.27/1.05  
% 1.27/1.05  ------ AIG Options
% 1.27/1.05  
% 1.27/1.05  --aig_mode                              false
% 1.27/1.05  
% 1.27/1.05  ------ Instantiation Options
% 1.27/1.05  
% 1.27/1.05  --instantiation_flag                    true
% 1.27/1.05  --inst_sos_flag                         false
% 1.27/1.05  --inst_sos_phase                        true
% 1.27/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.27/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.27/1.05  --inst_lit_sel_side                     none
% 1.27/1.05  --inst_solver_per_active                1400
% 1.27/1.05  --inst_solver_calls_frac                1.
% 1.27/1.05  --inst_passive_queue_type               priority_queues
% 1.27/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.27/1.05  --inst_passive_queues_freq              [25;2]
% 1.27/1.05  --inst_dismatching                      true
% 1.27/1.05  --inst_eager_unprocessed_to_passive     true
% 1.27/1.05  --inst_prop_sim_given                   true
% 1.27/1.05  --inst_prop_sim_new                     false
% 1.27/1.05  --inst_subs_new                         false
% 1.27/1.05  --inst_eq_res_simp                      false
% 1.27/1.05  --inst_subs_given                       false
% 1.27/1.05  --inst_orphan_elimination               true
% 1.27/1.05  --inst_learning_loop_flag               true
% 1.27/1.05  --inst_learning_start                   3000
% 1.27/1.05  --inst_learning_factor                  2
% 1.27/1.05  --inst_start_prop_sim_after_learn       3
% 1.27/1.05  --inst_sel_renew                        solver
% 1.27/1.05  --inst_lit_activity_flag                true
% 1.27/1.05  --inst_restr_to_given                   false
% 1.27/1.05  --inst_activity_threshold               500
% 1.27/1.05  --inst_out_proof                        true
% 1.27/1.05  
% 1.27/1.05  ------ Resolution Options
% 1.27/1.05  
% 1.27/1.05  --resolution_flag                       false
% 1.27/1.05  --res_lit_sel                           adaptive
% 1.27/1.05  --res_lit_sel_side                      none
% 1.27/1.05  --res_ordering                          kbo
% 1.27/1.05  --res_to_prop_solver                    active
% 1.27/1.05  --res_prop_simpl_new                    false
% 1.27/1.05  --res_prop_simpl_given                  true
% 1.27/1.05  --res_passive_queue_type                priority_queues
% 1.27/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.27/1.05  --res_passive_queues_freq               [15;5]
% 1.27/1.05  --res_forward_subs                      full
% 1.27/1.05  --res_backward_subs                     full
% 1.27/1.05  --res_forward_subs_resolution           true
% 1.27/1.05  --res_backward_subs_resolution          true
% 1.27/1.05  --res_orphan_elimination                true
% 1.27/1.05  --res_time_limit                        2.
% 1.27/1.05  --res_out_proof                         true
% 1.27/1.05  
% 1.27/1.05  ------ Superposition Options
% 1.27/1.05  
% 1.27/1.05  --superposition_flag                    true
% 1.27/1.05  --sup_passive_queue_type                priority_queues
% 1.27/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.27/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.27/1.05  --demod_completeness_check              fast
% 1.27/1.05  --demod_use_ground                      true
% 1.27/1.05  --sup_to_prop_solver                    passive
% 1.27/1.05  --sup_prop_simpl_new                    true
% 1.27/1.05  --sup_prop_simpl_given                  true
% 1.27/1.05  --sup_fun_splitting                     false
% 1.27/1.05  --sup_smt_interval                      50000
% 1.27/1.05  
% 1.27/1.05  ------ Superposition Simplification Setup
% 1.27/1.05  
% 1.27/1.05  --sup_indices_passive                   []
% 1.27/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.27/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.05  --sup_full_bw                           [BwDemod]
% 1.27/1.05  --sup_immed_triv                        [TrivRules]
% 1.27/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.27/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.05  --sup_immed_bw_main                     []
% 1.27/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.27/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.05  
% 1.27/1.05  ------ Combination Options
% 1.27/1.05  
% 1.27/1.05  --comb_res_mult                         3
% 1.27/1.05  --comb_sup_mult                         2
% 1.27/1.05  --comb_inst_mult                        10
% 1.27/1.05  
% 1.27/1.05  ------ Debug Options
% 1.27/1.05  
% 1.27/1.05  --dbg_backtrace                         false
% 1.27/1.05  --dbg_dump_prop_clauses                 false
% 1.27/1.05  --dbg_dump_prop_clauses_file            -
% 1.27/1.05  --dbg_out_stat                          false
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  ------ Proving...
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  % SZS status Theorem for theBenchmark.p
% 1.27/1.05  
% 1.27/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.27/1.05  
% 1.27/1.05  fof(f5,conjecture,(
% 1.27/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => ! [X3] : ~(! [X4] : ~(r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 1.27/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.05  
% 1.27/1.05  fof(f6,negated_conjecture,(
% 1.27/1.05    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => ! [X3] : ~(! [X4] : ~(r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 1.27/1.05    inference(negated_conjecture,[],[f5])).
% 1.27/1.05  
% 1.27/1.05  fof(f14,plain,(
% 1.27/1.05    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & (r3_wellord1(X0,X1,X2) & v2_wellord1(X0))) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.27/1.05    inference(ennf_transformation,[],[f6])).
% 1.27/1.05  
% 1.27/1.05  fof(f15,plain,(
% 1.27/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.27/1.05    inference(flattening,[],[f14])).
% 1.27/1.05  
% 1.27/1.05  fof(f21,plain,(
% 1.27/1.05    ( ! [X0,X1] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) => (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,sK4)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(sK4,k3_relat_1(X0)))) )),
% 1.27/1.05    introduced(choice_axiom,[])).
% 1.27/1.05  
% 1.27/1.05  fof(f20,plain,(
% 1.27/1.05    ( ! [X0,X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,sK3) & v2_wellord1(X0) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 1.27/1.05    introduced(choice_axiom,[])).
% 1.27/1.05  
% 1.27/1.05  fof(f19,plain,(
% 1.27/1.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(sK2,k1_wellord1(sK2,X4))) | ~r2_hidden(X4,k3_relat_1(sK2))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,sK2,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK2))) )),
% 1.27/1.05    introduced(choice_axiom,[])).
% 1.27/1.05  
% 1.27/1.05  fof(f18,plain,(
% 1.27/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(sK1))) & r3_wellord1(sK1,X1,X2) & v2_wellord1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 1.27/1.05    introduced(choice_axiom,[])).
% 1.27/1.05  
% 1.27/1.05  fof(f22,plain,(
% 1.27/1.05    (((! [X4] : (~r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X4))) | ~r2_hidden(X4,k3_relat_1(sK2))) & r2_hidden(sK4,k3_relat_1(sK1))) & r3_wellord1(sK1,sK2,sK3) & v2_wellord1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 1.27/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f21,f20,f19,f18])).
% 1.27/1.05  
% 1.27/1.05  fof(f33,plain,(
% 1.27/1.05    v1_funct_1(sK3)),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f3,axiom,(
% 1.27/1.05    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((r3_wellord1(X1,X2,X3) & r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)))))))),
% 1.27/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.05  
% 1.27/1.05  fof(f10,plain,(
% 1.27/1.05    ! [X0,X1] : (! [X2] : (! [X3] : (((r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0))) | (~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.27/1.05    inference(ennf_transformation,[],[f3])).
% 1.27/1.05  
% 1.27/1.05  fof(f11,plain,(
% 1.27/1.05    ! [X0,X1] : (! [X2] : (! [X3] : ((r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0))) | ~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.27/1.05    inference(flattening,[],[f10])).
% 1.27/1.05  
% 1.27/1.05  fof(f27,plain,(
% 1.27/1.05    ( ! [X2,X0,X3,X1] : (r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) | ~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.27/1.05    inference(cnf_transformation,[],[f11])).
% 1.27/1.05  
% 1.27/1.05  fof(f34,plain,(
% 1.27/1.05    v2_wellord1(sK1)),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f30,plain,(
% 1.27/1.05    v1_relat_1(sK1)),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f32,plain,(
% 1.27/1.05    v1_relat_1(sK3)),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f36,plain,(
% 1.27/1.05    r2_hidden(sK4,k3_relat_1(sK1))),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f35,plain,(
% 1.27/1.05    r3_wellord1(sK1,sK2,sK3)),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f4,axiom,(
% 1.27/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3] : ~(! [X4] : ~(k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3)) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 1.27/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.05  
% 1.27/1.05  fof(f12,plain,(
% 1.27/1.05    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (? [X4] : (k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3)) & r2_hidden(X4,k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.27/1.05    inference(ennf_transformation,[],[f4])).
% 1.27/1.05  
% 1.27/1.05  fof(f13,plain,(
% 1.27/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (? [X4] : (k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3)) & r2_hidden(X4,k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.27/1.05    inference(flattening,[],[f12])).
% 1.27/1.05  
% 1.27/1.05  fof(f16,plain,(
% 1.27/1.05    ! [X3,X2,X1,X0] : (? [X4] : (k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3)) & r2_hidden(X4,k3_relat_1(X1))) => (k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3)) & r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))))),
% 1.27/1.05    introduced(choice_axiom,[])).
% 1.27/1.05  
% 1.27/1.05  fof(f17,plain,(
% 1.27/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3)) & r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.27/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f16])).
% 1.27/1.05  
% 1.27/1.05  fof(f29,plain,(
% 1.27/1.05    ( ! [X2,X0,X3,X1] : (k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.27/1.05    inference(cnf_transformation,[],[f17])).
% 1.27/1.05  
% 1.27/1.05  fof(f31,plain,(
% 1.27/1.05    v1_relat_1(sK2)),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f37,plain,(
% 1.27/1.05    ( ! [X4] : (~r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X4))) | ~r2_hidden(X4,k3_relat_1(sK2))) )),
% 1.27/1.05    inference(cnf_transformation,[],[f22])).
% 1.27/1.05  
% 1.27/1.05  fof(f28,plain,(
% 1.27/1.05    ( ! [X2,X0,X3,X1] : (r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.27/1.05    inference(cnf_transformation,[],[f17])).
% 1.27/1.05  
% 1.27/1.05  fof(f2,axiom,(
% 1.27/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)))),
% 1.27/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.05  
% 1.27/1.05  fof(f8,plain,(
% 1.27/1.05    ! [X0,X1] : ((k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 1.27/1.05    inference(ennf_transformation,[],[f2])).
% 1.27/1.05  
% 1.27/1.05  fof(f9,plain,(
% 1.27/1.05    ! [X0,X1] : (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 1.27/1.05    inference(flattening,[],[f8])).
% 1.27/1.05  
% 1.27/1.05  fof(f25,plain,(
% 1.27/1.05    ( ! [X0,X1] : (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 1.27/1.05    inference(cnf_transformation,[],[f9])).
% 1.27/1.05  
% 1.27/1.05  fof(f1,axiom,(
% 1.27/1.05    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.27/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.05  
% 1.27/1.05  fof(f7,plain,(
% 1.27/1.05    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.27/1.05    inference(ennf_transformation,[],[f1])).
% 1.27/1.05  
% 1.27/1.05  fof(f23,plain,(
% 1.27/1.05    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.27/1.05    inference(cnf_transformation,[],[f7])).
% 1.27/1.05  
% 1.27/1.05  cnf(c_11,negated_conjecture,
% 1.27/1.05      ( v1_funct_1(sK3) ),
% 1.27/1.05      inference(cnf_transformation,[],[f33]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_3,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,X2)
% 1.27/1.05      | r4_wellord1(k2_wellord1(X0,X3),k2_wellord1(X1,k9_relat_1(X2,X3)))
% 1.27/1.05      | ~ r1_tarski(X3,k3_relat_1(X0))
% 1.27/1.05      | ~ v1_funct_1(X2)
% 1.27/1.05      | ~ v2_wellord1(X0)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X1) ),
% 1.27/1.05      inference(cnf_transformation,[],[f27]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_10,negated_conjecture,
% 1.27/1.05      ( v2_wellord1(sK1) ),
% 1.27/1.05      inference(cnf_transformation,[],[f34]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_241,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,X2)
% 1.27/1.05      | r4_wellord1(k2_wellord1(X0,X3),k2_wellord1(X1,k9_relat_1(X2,X3)))
% 1.27/1.05      | ~ r1_tarski(X3,k3_relat_1(X0))
% 1.27/1.05      | ~ v1_funct_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | sK1 != X0 ),
% 1.27/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_242,plain,
% 1.27/1.05      ( ~ r3_wellord1(sK1,X0,X1)
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
% 1.27/1.05      | ~ r1_tarski(X2,k3_relat_1(sK1))
% 1.27/1.05      | ~ v1_funct_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(sK1) ),
% 1.27/1.05      inference(unflattening,[status(thm)],[c_241]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_14,negated_conjecture,
% 1.27/1.05      ( v1_relat_1(sK1) ),
% 1.27/1.05      inference(cnf_transformation,[],[f30]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_246,plain,
% 1.27/1.05      ( ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_funct_1(X1)
% 1.27/1.05      | ~ r1_tarski(X2,k3_relat_1(sK1))
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
% 1.27/1.05      | ~ r3_wellord1(sK1,X0,X1) ),
% 1.27/1.05      inference(global_propositional_subsumption,
% 1.27/1.05                [status(thm)],
% 1.27/1.05                [c_242,c_14]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_247,plain,
% 1.27/1.05      ( ~ r3_wellord1(sK1,X0,X1)
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
% 1.27/1.05      | ~ r1_tarski(X2,k3_relat_1(sK1))
% 1.27/1.05      | ~ v1_funct_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X1) ),
% 1.27/1.05      inference(renaming,[status(thm)],[c_246]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_410,plain,
% 1.27/1.05      ( ~ r3_wellord1(sK1,X0,X1)
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
% 1.27/1.05      | ~ r1_tarski(X2,k3_relat_1(sK1))
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | sK3 != X1 ),
% 1.27/1.05      inference(resolution_lifted,[status(thm)],[c_11,c_247]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_411,plain,
% 1.27/1.05      ( ~ r3_wellord1(sK1,X0,sK3)
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
% 1.27/1.05      | ~ r1_tarski(X1,k3_relat_1(sK1))
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(sK3) ),
% 1.27/1.05      inference(unflattening,[status(thm)],[c_410]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_12,negated_conjecture,
% 1.27/1.05      ( v1_relat_1(sK3) ),
% 1.27/1.05      inference(cnf_transformation,[],[f32]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_415,plain,
% 1.27/1.05      ( ~ v1_relat_1(X0)
% 1.27/1.05      | ~ r1_tarski(X1,k3_relat_1(sK1))
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
% 1.27/1.05      | ~ r3_wellord1(sK1,X0,sK3) ),
% 1.27/1.05      inference(global_propositional_subsumption,
% 1.27/1.05                [status(thm)],
% 1.27/1.05                [c_411,c_12]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_416,plain,
% 1.27/1.05      ( ~ r3_wellord1(sK1,X0,sK3)
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
% 1.27/1.05      | ~ r1_tarski(X1,k3_relat_1(sK1))
% 1.27/1.05      | ~ v1_relat_1(X0) ),
% 1.27/1.05      inference(renaming,[status(thm)],[c_415]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_785,plain,
% 1.27/1.05      ( ~ r3_wellord1(sK1,X0_45,sK3)
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X0_46),k2_wellord1(X0_45,k9_relat_1(sK3,X0_46)))
% 1.27/1.05      | ~ r1_tarski(X0_46,k3_relat_1(sK1))
% 1.27/1.05      | ~ v1_relat_1(X0_45) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_416]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1094,plain,
% 1.27/1.05      ( r3_wellord1(sK1,X0_45,sK3) != iProver_top
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,X0_46),k2_wellord1(X0_45,k9_relat_1(sK3,X0_46))) = iProver_top
% 1.27/1.05      | r1_tarski(X0_46,k3_relat_1(sK1)) != iProver_top
% 1.27/1.05      | v1_relat_1(X0_45) != iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_8,negated_conjecture,
% 1.27/1.05      ( r2_hidden(sK4,k3_relat_1(sK1)) ),
% 1.27/1.05      inference(cnf_transformation,[],[f36]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_794,negated_conjecture,
% 1.27/1.05      ( r2_hidden(sK4,k3_relat_1(sK1)) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_8]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1086,plain,
% 1.27/1.05      ( r2_hidden(sK4,k3_relat_1(sK1)) = iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_9,negated_conjecture,
% 1.27/1.05      ( r3_wellord1(sK1,sK2,sK3) ),
% 1.27/1.05      inference(cnf_transformation,[],[f35]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_793,negated_conjecture,
% 1.27/1.05      ( r3_wellord1(sK1,sK2,sK3) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_9]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1087,plain,
% 1.27/1.05      ( r3_wellord1(sK1,sK2,sK3) = iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_5,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,X2)
% 1.27/1.05      | ~ r2_hidden(X3,k3_relat_1(X0))
% 1.27/1.05      | ~ v1_funct_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3)) ),
% 1.27/1.05      inference(cnf_transformation,[],[f29]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_383,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,X2)
% 1.27/1.05      | ~ r2_hidden(X3,k3_relat_1(X0))
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
% 1.27/1.05      | sK3 != X2 ),
% 1.27/1.05      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_384,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,sK3)
% 1.27/1.05      | ~ r2_hidden(X2,k3_relat_1(X0))
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(sK3)
% 1.27/1.05      | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
% 1.27/1.05      inference(unflattening,[status(thm)],[c_383]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_388,plain,
% 1.27/1.05      ( ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ r2_hidden(X2,k3_relat_1(X0))
% 1.27/1.05      | ~ r3_wellord1(X0,X1,sK3)
% 1.27/1.05      | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
% 1.27/1.05      inference(global_propositional_subsumption,
% 1.27/1.05                [status(thm)],
% 1.27/1.05                [c_384,c_12]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_389,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,sK3)
% 1.27/1.05      | ~ r2_hidden(X2,k3_relat_1(X0))
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
% 1.27/1.05      inference(renaming,[status(thm)],[c_388]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_786,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0_45,X1_45,sK3)
% 1.27/1.05      | ~ r2_hidden(X0_47,k3_relat_1(X0_45))
% 1.27/1.05      | ~ v1_relat_1(X0_45)
% 1.27/1.05      | ~ v1_relat_1(X1_45)
% 1.27/1.05      | k1_wellord1(X1_45,sK0(X0_45,X1_45,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(X0_45,X0_47)) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_389]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1093,plain,
% 1.27/1.05      ( k1_wellord1(X0_45,sK0(X1_45,X0_45,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(X1_45,X0_47))
% 1.27/1.05      | r3_wellord1(X1_45,X0_45,sK3) != iProver_top
% 1.27/1.05      | r2_hidden(X0_47,k3_relat_1(X1_45)) != iProver_top
% 1.27/1.05      | v1_relat_1(X0_45) != iProver_top
% 1.27/1.05      | v1_relat_1(X1_45) != iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1620,plain,
% 1.27/1.05      ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(sK1,X0_47))
% 1.27/1.05      | r2_hidden(X0_47,k3_relat_1(sK1)) != iProver_top
% 1.27/1.05      | v1_relat_1(sK2) != iProver_top
% 1.27/1.05      | v1_relat_1(sK1) != iProver_top ),
% 1.27/1.05      inference(superposition,[status(thm)],[c_1087,c_1093]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_15,plain,
% 1.27/1.05      ( v1_relat_1(sK1) = iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_13,negated_conjecture,
% 1.27/1.05      ( v1_relat_1(sK2) ),
% 1.27/1.05      inference(cnf_transformation,[],[f31]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_16,plain,
% 1.27/1.05      ( v1_relat_1(sK2) = iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1702,plain,
% 1.27/1.05      ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,X0_47)) = k9_relat_1(sK3,k1_wellord1(sK1,X0_47))
% 1.27/1.05      | r2_hidden(X0_47,k3_relat_1(sK1)) != iProver_top ),
% 1.27/1.05      inference(global_propositional_subsumption,
% 1.27/1.05                [status(thm)],
% 1.27/1.05                [c_1620,c_15,c_16]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1710,plain,
% 1.27/1.05      ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,sK4)) = k9_relat_1(sK3,k1_wellord1(sK1,sK4)) ),
% 1.27/1.05      inference(superposition,[status(thm)],[c_1086,c_1702]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_7,negated_conjecture,
% 1.27/1.05      ( ~ r2_hidden(X0,k3_relat_1(sK2))
% 1.27/1.05      | ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0))) ),
% 1.27/1.05      inference(cnf_transformation,[],[f37]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_795,negated_conjecture,
% 1.27/1.05      ( ~ r2_hidden(X0_47,k3_relat_1(sK2))
% 1.27/1.05      | ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0_47))) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_7]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1085,plain,
% 1.27/1.05      ( r2_hidden(X0_47,k3_relat_1(sK2)) != iProver_top
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0_47))) != iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1728,plain,
% 1.27/1.05      ( r2_hidden(sK0(sK1,sK2,sK3,sK4),k3_relat_1(sK2)) != iProver_top
% 1.27/1.05      | r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k9_relat_1(sK3,k1_wellord1(sK1,sK4)))) != iProver_top ),
% 1.27/1.05      inference(superposition,[status(thm)],[c_1710,c_1085]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_20,plain,
% 1.27/1.05      ( r3_wellord1(sK1,sK2,sK3) = iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_21,plain,
% 1.27/1.05      ( r2_hidden(sK4,k3_relat_1(sK1)) = iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_6,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,X2)
% 1.27/1.05      | ~ r2_hidden(X3,k3_relat_1(X0))
% 1.27/1.05      | r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
% 1.27/1.05      | ~ v1_funct_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X0) ),
% 1.27/1.05      inference(cnf_transformation,[],[f28]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_356,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,X2)
% 1.27/1.05      | ~ r2_hidden(X3,k3_relat_1(X0))
% 1.27/1.05      | r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X2)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | sK3 != X2 ),
% 1.27/1.05      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_357,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,sK3)
% 1.27/1.05      | ~ r2_hidden(X2,k3_relat_1(X0))
% 1.27/1.05      | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(sK3) ),
% 1.27/1.05      inference(unflattening,[status(thm)],[c_356]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_361,plain,
% 1.27/1.05      ( ~ v1_relat_1(X1)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
% 1.27/1.05      | ~ r2_hidden(X2,k3_relat_1(X0))
% 1.27/1.05      | ~ r3_wellord1(X0,X1,sK3) ),
% 1.27/1.05      inference(global_propositional_subsumption,
% 1.27/1.05                [status(thm)],
% 1.27/1.05                [c_357,c_12]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_362,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0,X1,sK3)
% 1.27/1.05      | ~ r2_hidden(X2,k3_relat_1(X0))
% 1.27/1.05      | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | ~ v1_relat_1(X1) ),
% 1.27/1.05      inference(renaming,[status(thm)],[c_361]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_787,plain,
% 1.27/1.05      ( ~ r3_wellord1(X0_45,X1_45,sK3)
% 1.27/1.05      | ~ r2_hidden(X0_47,k3_relat_1(X0_45))
% 1.27/1.05      | r2_hidden(sK0(X0_45,X1_45,sK3,X0_47),k3_relat_1(X1_45))
% 1.27/1.05      | ~ v1_relat_1(X0_45)
% 1.27/1.05      | ~ v1_relat_1(X1_45) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_362]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1194,plain,
% 1.27/1.05      ( ~ r3_wellord1(sK1,sK2,sK3)
% 1.27/1.05      | ~ r2_hidden(X0_47,k3_relat_1(sK1))
% 1.27/1.05      | r2_hidden(sK0(sK1,sK2,sK3,X0_47),k3_relat_1(sK2))
% 1.27/1.05      | ~ v1_relat_1(sK2)
% 1.27/1.05      | ~ v1_relat_1(sK1) ),
% 1.27/1.05      inference(instantiation,[status(thm)],[c_787]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1195,plain,
% 1.27/1.05      ( r3_wellord1(sK1,sK2,sK3) != iProver_top
% 1.27/1.05      | r2_hidden(X0_47,k3_relat_1(sK1)) != iProver_top
% 1.27/1.05      | r2_hidden(sK0(sK1,sK2,sK3,X0_47),k3_relat_1(sK2)) = iProver_top
% 1.27/1.05      | v1_relat_1(sK2) != iProver_top
% 1.27/1.05      | v1_relat_1(sK1) != iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_1194]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1197,plain,
% 1.27/1.05      ( r3_wellord1(sK1,sK2,sK3) != iProver_top
% 1.27/1.05      | r2_hidden(sK0(sK1,sK2,sK3,sK4),k3_relat_1(sK2)) = iProver_top
% 1.27/1.05      | r2_hidden(sK4,k3_relat_1(sK1)) != iProver_top
% 1.27/1.05      | v1_relat_1(sK2) != iProver_top
% 1.27/1.05      | v1_relat_1(sK1) != iProver_top ),
% 1.27/1.05      inference(instantiation,[status(thm)],[c_1195]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1821,plain,
% 1.27/1.05      ( r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k9_relat_1(sK3,k1_wellord1(sK1,sK4)))) != iProver_top ),
% 1.27/1.05      inference(global_propositional_subsumption,
% 1.27/1.05                [status(thm)],
% 1.27/1.05                [c_1728,c_15,c_16,c_20,c_21,c_1197]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1826,plain,
% 1.27/1.05      ( r3_wellord1(sK1,sK2,sK3) != iProver_top
% 1.27/1.05      | r1_tarski(k1_wellord1(sK1,sK4),k3_relat_1(sK1)) != iProver_top
% 1.27/1.05      | v1_relat_1(sK2) != iProver_top ),
% 1.27/1.05      inference(superposition,[status(thm)],[c_1094,c_1821]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_2,plain,
% 1.27/1.05      ( ~ v2_wellord1(X0)
% 1.27/1.05      | ~ v1_relat_1(X0)
% 1.27/1.05      | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1) ),
% 1.27/1.05      inference(cnf_transformation,[],[f25]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_269,plain,
% 1.27/1.05      ( ~ v1_relat_1(X0)
% 1.27/1.05      | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1)
% 1.27/1.05      | sK1 != X0 ),
% 1.27/1.05      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_270,plain,
% 1.27/1.05      ( ~ v1_relat_1(sK1)
% 1.27/1.05      | k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) = k1_wellord1(sK1,X0) ),
% 1.27/1.05      inference(unflattening,[status(thm)],[c_269]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_274,plain,
% 1.27/1.05      ( k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) = k1_wellord1(sK1,X0) ),
% 1.27/1.05      inference(global_propositional_subsumption,
% 1.27/1.05                [status(thm)],
% 1.27/1.05                [c_270,c_14]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_789,plain,
% 1.27/1.05      ( k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0_47))) = k1_wellord1(sK1,X0_47) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_274]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1,plain,
% 1.27/1.05      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),k3_relat_1(X0))
% 1.27/1.05      | ~ v1_relat_1(X0) ),
% 1.27/1.05      inference(cnf_transformation,[],[f23]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_796,plain,
% 1.27/1.05      ( r1_tarski(k3_relat_1(k2_wellord1(X0_45,X0_46)),k3_relat_1(X0_45))
% 1.27/1.05      | ~ v1_relat_1(X0_45) ),
% 1.27/1.05      inference(subtyping,[status(esa)],[c_1]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1084,plain,
% 1.27/1.05      ( r1_tarski(k3_relat_1(k2_wellord1(X0_45,X0_46)),k3_relat_1(X0_45)) = iProver_top
% 1.27/1.05      | v1_relat_1(X0_45) != iProver_top ),
% 1.27/1.05      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1374,plain,
% 1.27/1.05      ( r1_tarski(k1_wellord1(sK1,X0_47),k3_relat_1(sK1)) = iProver_top
% 1.27/1.05      | v1_relat_1(sK1) != iProver_top ),
% 1.27/1.05      inference(superposition,[status(thm)],[c_789,c_1084]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(c_1385,plain,
% 1.27/1.05      ( r1_tarski(k1_wellord1(sK1,sK4),k3_relat_1(sK1)) = iProver_top
% 1.27/1.05      | v1_relat_1(sK1) != iProver_top ),
% 1.27/1.05      inference(instantiation,[status(thm)],[c_1374]) ).
% 1.27/1.05  
% 1.27/1.05  cnf(contradiction,plain,
% 1.27/1.05      ( $false ),
% 1.27/1.05      inference(minisat,[status(thm)],[c_1826,c_1385,c_20,c_16,c_15]) ).
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.27/1.05  
% 1.27/1.05  ------                               Statistics
% 1.27/1.05  
% 1.27/1.05  ------ General
% 1.27/1.05  
% 1.27/1.05  abstr_ref_over_cycles:                  0
% 1.27/1.05  abstr_ref_under_cycles:                 0
% 1.27/1.05  gc_basic_clause_elim:                   0
% 1.27/1.05  forced_gc_time:                         0
% 1.27/1.05  parsing_time:                           0.019
% 1.27/1.05  unif_index_cands_time:                  0.
% 1.27/1.05  unif_index_add_time:                    0.
% 1.27/1.05  orderings_time:                         0.
% 1.27/1.05  out_proof_time:                         0.011
% 1.27/1.05  total_time:                             0.108
% 1.27/1.05  num_of_symbols:                         48
% 1.27/1.05  num_of_terms:                           1980
% 1.27/1.05  
% 1.27/1.05  ------ Preprocessing
% 1.27/1.05  
% 1.27/1.05  num_of_splits:                          0
% 1.27/1.05  num_of_split_atoms:                     0
% 1.27/1.05  num_of_reused_defs:                     0
% 1.27/1.05  num_eq_ax_congr_red:                    15
% 1.27/1.05  num_of_sem_filtered_clauses:            1
% 1.27/1.05  num_of_subtypes:                        3
% 1.27/1.05  monotx_restored_types:                  0
% 1.27/1.05  sat_num_of_epr_types:                   0
% 1.27/1.05  sat_num_of_non_cyclic_types:            0
% 1.27/1.05  sat_guarded_non_collapsed_types:        0
% 1.27/1.05  num_pure_diseq_elim:                    0
% 1.27/1.05  simp_replaced_by:                       0
% 1.27/1.05  res_preprocessed:                       85
% 1.27/1.05  prep_upred:                             0
% 1.27/1.05  prep_unflattend:                        19
% 1.27/1.05  smt_new_axioms:                         0
% 1.27/1.05  pred_elim_cands:                        5
% 1.27/1.05  pred_elim:                              2
% 1.27/1.05  pred_elim_cl:                           2
% 1.27/1.05  pred_elim_cycles:                       8
% 1.27/1.05  merged_defs:                            0
% 1.27/1.05  merged_defs_ncl:                        0
% 1.27/1.05  bin_hyper_res:                          0
% 1.27/1.05  prep_cycles:                            4
% 1.27/1.05  pred_elim_time:                         0.01
% 1.27/1.05  splitting_time:                         0.
% 1.27/1.05  sem_filter_time:                        0.
% 1.27/1.05  monotx_time:                            0.
% 1.27/1.05  subtype_inf_time:                       0.
% 1.27/1.05  
% 1.27/1.05  ------ Problem properties
% 1.27/1.05  
% 1.27/1.05  clauses:                                13
% 1.27/1.05  conjectures:                            6
% 1.27/1.05  epr:                                    4
% 1.27/1.05  horn:                                   13
% 1.27/1.05  ground:                                 5
% 1.27/1.05  unary:                                  6
% 1.27/1.05  binary:                                 3
% 1.27/1.05  lits:                                   30
% 1.27/1.05  lits_eq:                                2
% 1.27/1.05  fd_pure:                                0
% 1.27/1.05  fd_pseudo:                              0
% 1.27/1.05  fd_cond:                                0
% 1.27/1.05  fd_pseudo_cond:                         0
% 1.27/1.05  ac_symbols:                             0
% 1.27/1.05  
% 1.27/1.05  ------ Propositional Solver
% 1.27/1.05  
% 1.27/1.05  prop_solver_calls:                      27
% 1.27/1.05  prop_fast_solver_calls:                 621
% 1.27/1.05  smt_solver_calls:                       0
% 1.27/1.05  smt_fast_solver_calls:                  0
% 1.27/1.05  prop_num_of_clauses:                    448
% 1.27/1.05  prop_preprocess_simplified:             2529
% 1.27/1.05  prop_fo_subsumed:                       12
% 1.27/1.05  prop_solver_time:                       0.
% 1.27/1.05  smt_solver_time:                        0.
% 1.27/1.05  smt_fast_solver_time:                   0.
% 1.27/1.05  prop_fast_solver_time:                  0.
% 1.27/1.05  prop_unsat_core_time:                   0.
% 1.27/1.05  
% 1.27/1.05  ------ QBF
% 1.27/1.05  
% 1.27/1.05  qbf_q_res:                              0
% 1.27/1.05  qbf_num_tautologies:                    0
% 1.27/1.05  qbf_prep_cycles:                        0
% 1.27/1.05  
% 1.27/1.05  ------ BMC1
% 1.27/1.05  
% 1.27/1.05  bmc1_current_bound:                     -1
% 1.27/1.05  bmc1_last_solved_bound:                 -1
% 1.27/1.05  bmc1_unsat_core_size:                   -1
% 1.27/1.05  bmc1_unsat_core_parents_size:           -1
% 1.27/1.05  bmc1_merge_next_fun:                    0
% 1.27/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.27/1.05  
% 1.27/1.05  ------ Instantiation
% 1.27/1.05  
% 1.27/1.05  inst_num_of_clauses:                    126
% 1.27/1.05  inst_num_in_passive:                    22
% 1.27/1.05  inst_num_in_active:                     97
% 1.27/1.05  inst_num_in_unprocessed:                8
% 1.27/1.05  inst_num_of_loops:                      100
% 1.27/1.05  inst_num_of_learning_restarts:          0
% 1.27/1.05  inst_num_moves_active_passive:          0
% 1.27/1.05  inst_lit_activity:                      0
% 1.27/1.05  inst_lit_activity_moves:                0
% 1.27/1.05  inst_num_tautologies:                   0
% 1.27/1.05  inst_num_prop_implied:                  0
% 1.27/1.05  inst_num_existing_simplified:           0
% 1.27/1.05  inst_num_eq_res_simplified:             0
% 1.27/1.05  inst_num_child_elim:                    0
% 1.27/1.05  inst_num_of_dismatching_blockings:      62
% 1.27/1.05  inst_num_of_non_proper_insts:           128
% 1.27/1.05  inst_num_of_duplicates:                 0
% 1.27/1.05  inst_inst_num_from_inst_to_res:         0
% 1.27/1.05  inst_dismatching_checking_time:         0.
% 1.27/1.05  
% 1.27/1.05  ------ Resolution
% 1.27/1.05  
% 1.27/1.05  res_num_of_clauses:                     0
% 1.27/1.05  res_num_in_passive:                     0
% 1.27/1.05  res_num_in_active:                      0
% 1.27/1.05  res_num_of_loops:                       89
% 1.27/1.05  res_forward_subset_subsumed:            18
% 1.27/1.05  res_backward_subset_subsumed:           4
% 1.27/1.05  res_forward_subsumed:                   0
% 1.27/1.05  res_backward_subsumed:                  0
% 1.27/1.05  res_forward_subsumption_resolution:     0
% 1.27/1.05  res_backward_subsumption_resolution:    0
% 1.27/1.05  res_clause_to_clause_subsumption:       27
% 1.27/1.05  res_orphan_elimination:                 0
% 1.27/1.05  res_tautology_del:                      22
% 1.27/1.05  res_num_eq_res_simplified:              0
% 1.27/1.05  res_num_sel_changes:                    0
% 1.27/1.05  res_moves_from_active_to_pass:          0
% 1.27/1.05  
% 1.27/1.05  ------ Superposition
% 1.27/1.05  
% 1.27/1.05  sup_time_total:                         0.
% 1.27/1.05  sup_time_generating:                    0.
% 1.27/1.05  sup_time_sim_full:                      0.
% 1.27/1.05  sup_time_sim_immed:                     0.
% 1.27/1.05  
% 1.27/1.05  sup_num_of_clauses:                     22
% 1.27/1.05  sup_num_in_active:                      19
% 1.27/1.05  sup_num_in_passive:                     3
% 1.27/1.05  sup_num_of_loops:                       18
% 1.27/1.05  sup_fw_superposition:                   8
% 1.27/1.05  sup_bw_superposition:                   1
% 1.27/1.05  sup_immediate_simplified:               0
% 1.27/1.05  sup_given_eliminated:                   0
% 1.27/1.05  comparisons_done:                       0
% 1.27/1.05  comparisons_avoided:                    0
% 1.27/1.05  
% 1.27/1.05  ------ Simplifications
% 1.27/1.05  
% 1.27/1.05  
% 1.27/1.05  sim_fw_subset_subsumed:                 0
% 1.27/1.05  sim_bw_subset_subsumed:                 0
% 1.27/1.05  sim_fw_subsumed:                        0
% 1.27/1.05  sim_bw_subsumed:                        0
% 1.27/1.05  sim_fw_subsumption_res:                 0
% 1.27/1.05  sim_bw_subsumption_res:                 0
% 1.27/1.05  sim_tautology_del:                      0
% 1.27/1.05  sim_eq_tautology_del:                   0
% 1.27/1.05  sim_eq_res_simp:                        0
% 1.27/1.05  sim_fw_demodulated:                     0
% 1.27/1.05  sim_bw_demodulated:                     0
% 1.27/1.05  sim_light_normalised:                   0
% 1.27/1.05  sim_joinable_taut:                      0
% 1.27/1.05  sim_joinable_simp:                      0
% 1.27/1.05  sim_ac_normalised:                      0
% 1.27/1.05  sim_smt_subsumption:                    0
% 1.27/1.05  
%------------------------------------------------------------------------------
