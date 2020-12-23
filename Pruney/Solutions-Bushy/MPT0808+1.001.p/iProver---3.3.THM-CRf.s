%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0808+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:09 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 292 expanded)
%              Number of clauses        :   56 (  73 expanded)
%              Number of leaves         :    9 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  394 (2340 expanded)
%              Number of equality atoms :   61 (  72 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f18,plain,(
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

fof(f17,plain,(
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

fof(f16,plain,(
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

fof(f15,plain,
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

fof(f19,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18,f17,f16,f15])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
      | ~ r3_wellord1(X1,X2,X3)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    r2_hidden(sK4,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    r3_wellord1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
          & r2_hidden(X4,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
        & r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X4] :
      ( ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X4)))
      | ~ r2_hidden(X4,k3_relat_1(sK2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r4_wellord1(k2_wellord1(X0,X3),k2_wellord1(X1,k9_relat_1(X2,X3)))
    | ~ r1_tarski(X3,k3_relat_1(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,negated_conjecture,
    ( v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_218,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r4_wellord1(k2_wellord1(X0,X3),k2_wellord1(X1,k9_relat_1(X2,X3)))
    | ~ r1_tarski(X3,k3_relat_1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_219,plain,
    ( ~ r3_wellord1(sK1,X0,X1)
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_223,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r3_wellord1(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_219,c_12])).

cnf(c_224,plain,
    ( ~ r3_wellord1(sK1,X0,X1)
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_443,plain,
    ( ~ r3_wellord1(sK1,X0,X1)
    | r4_wellord1(k2_wellord1(sK1,X2),k2_wellord1(X0,k9_relat_1(X1,X2)))
    | ~ r1_tarski(X2,k3_relat_1(sK1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_224])).

cnf(c_444,plain,
    ( ~ r3_wellord1(sK1,X0,sK3)
    | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
    | ~ r1_tarski(X1,k3_relat_1(sK1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_448,plain,
    ( ~ v1_relat_1(X0)
    | ~ r1_tarski(X1,k3_relat_1(sK1))
    | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
    | ~ r3_wellord1(sK1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_10])).

cnf(c_449,plain,
    ( ~ r3_wellord1(sK1,X0,sK3)
    | r4_wellord1(k2_wellord1(sK1,X1),k2_wellord1(X0,k9_relat_1(sK3,X1)))
    | ~ r1_tarski(X1,k3_relat_1(sK1))
    | ~ v1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_448])).

cnf(c_727,plain,
    ( ~ r3_wellord1(sK1,X0_45,sK3)
    | r4_wellord1(k2_wellord1(sK1,X0_46),k2_wellord1(X0_45,k9_relat_1(sK3,X0_46)))
    | ~ r1_tarski(X0_46,k3_relat_1(sK1))
    | ~ v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_449])).

cnf(c_1016,plain,
    ( r3_wellord1(sK1,X0_45,sK3) != iProver_top
    | r4_wellord1(k2_wellord1(sK1,X0_46),k2_wellord1(X0_45,k9_relat_1(sK3,X0_46))) = iProver_top
    | r1_tarski(X0_46,k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(sK4,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_735,negated_conjecture,
    ( r2_hidden(sK4,k3_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1008,plain,
    ( r2_hidden(sK4,k3_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_7,negated_conjecture,
    ( r3_wellord1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_734,negated_conjecture,
    ( r3_wellord1(sK1,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1009,plain,
    ( r3_wellord1(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_3,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_416,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_wellord1(X1,sK0(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_417,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK3)
    | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_421,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ r3_wellord1(X0,X1,sK3)
    | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_10])).

cnf(c_422,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_wellord1(X1,sK0(X0,X1,sK3,X2)) = k9_relat_1(sK3,k1_wellord1(X0,X2)) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_728,plain,
    ( ~ r3_wellord1(X0_45,X1_45,sK3)
    | ~ r2_hidden(X0_48,k3_relat_1(X0_45))
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45)
    | k1_wellord1(X1_45,sK0(X0_45,X1_45,sK3,X0_48)) = k9_relat_1(sK3,k1_wellord1(X0_45,X0_48)) ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_1015,plain,
    ( k1_wellord1(X0_45,sK0(X1_45,X0_45,sK3,X0_48)) = k9_relat_1(sK3,k1_wellord1(X1_45,X0_48))
    | r3_wellord1(X1_45,X0_45,sK3) != iProver_top
    | r2_hidden(X0_48,k3_relat_1(X1_45)) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_1349,plain,
    ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,X0_48)) = k9_relat_1(sK3,k1_wellord1(sK1,X0_48))
    | r2_hidden(X0_48,k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1009,c_1015])).

cnf(c_13,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1354,plain,
    ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,X0_48)) = k9_relat_1(sK3,k1_wellord1(sK1,X0_48))
    | r2_hidden(X0_48,k3_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1349,c_13,c_14])).

cnf(c_1362,plain,
    ( k1_wellord1(sK2,sK0(sK1,sK2,sK3,sK4)) = k9_relat_1(sK3,k1_wellord1(sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_1008,c_1354])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK2))
    | ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_736,negated_conjecture,
    ( ~ r2_hidden(X0_48,k3_relat_1(sK2))
    | ~ r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0_48))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1007,plain,
    ( r2_hidden(X0_48,k3_relat_1(sK2)) != iProver_top
    | r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k1_wellord1(sK2,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_1413,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,sK4),k3_relat_1(sK2)) != iProver_top
    | r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k9_relat_1(sK3,k1_wellord1(sK1,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_1007])).

cnf(c_18,plain,
    ( r3_wellord1(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19,plain,
    ( r2_hidden(sK4,k3_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_389,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r2_hidden(X3,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,X2,X3),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_390,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ r3_wellord1(X0,X1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_10])).

cnf(c_395,plain,
    ( ~ r3_wellord1(X0,X1,sK3)
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | r2_hidden(sK0(X0,X1,sK3,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_729,plain,
    ( ~ r3_wellord1(X0_45,X1_45,sK3)
    | ~ r2_hidden(X0_48,k3_relat_1(X0_45))
    | r2_hidden(sK0(X0_45,X1_45,sK3,X0_48),k3_relat_1(X1_45))
    | ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_395])).

cnf(c_1108,plain,
    ( ~ r3_wellord1(sK1,sK2,sK3)
    | ~ r2_hidden(X0_48,k3_relat_1(sK1))
    | r2_hidden(sK0(sK1,sK2,sK3,X0_48),k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1109,plain,
    ( r3_wellord1(sK1,sK2,sK3) != iProver_top
    | r2_hidden(X0_48,k3_relat_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3,X0_48),k3_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1111,plain,
    ( r3_wellord1(sK1,sK2,sK3) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK3,sK4),k3_relat_1(sK2)) = iProver_top
    | r2_hidden(sK4,k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_1425,plain,
    ( r4_wellord1(k2_wellord1(sK1,k1_wellord1(sK1,sK4)),k2_wellord1(sK2,k9_relat_1(sK3,k1_wellord1(sK1,sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1413,c_13,c_14,c_18,c_19,c_1111])).

cnf(c_1430,plain,
    ( r3_wellord1(sK1,sK2,sK3) != iProver_top
    | r1_tarski(k1_wellord1(sK1,sK4),k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_1425])).

cnf(c_0,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_737,plain,
    ( r1_tarski(k1_wellord1(X0_45,X0_48),k3_relat_1(X0_45))
    | ~ v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_771,plain,
    ( r1_tarski(k1_wellord1(X0_45,X0_48),k3_relat_1(X0_45)) = iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_773,plain,
    ( r1_tarski(k1_wellord1(sK1,sK4),k3_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1430,c_773,c_18,c_14,c_13])).


%------------------------------------------------------------------------------
