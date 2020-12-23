%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0800+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:08 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 197 expanded)
%              Number of clauses        :   35 (  42 expanded)
%              Number of leaves         :    9 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  364 (1242 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X2] :
                  ( r3_wellord1(X0,X1,X2)
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X3] :
                  ( r3_wellord1(X0,X1,X3)
                  & v1_funct_1(X3)
                  & v1_relat_1(X3) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK0(X0,X1))
        & v1_funct_1(sK0(X0,X1))
        & v1_relat_1(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK0(X0,X1))
                & v1_funct_1(sK0(X0,X1))
                & v1_relat_1(sK0(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( ( v1_funct_1(X3)
                    & v1_relat_1(X3) )
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_relat_1(X4) )
                     => ( ( r3_wellord1(X1,X2,X4)
                          & r3_wellord1(X0,X1,X3) )
                       => r3_wellord1(X0,X2,k5_relat_1(X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
      | ~ r3_wellord1(X1,X2,X4)
      | ~ r3_wellord1(X0,X1,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK0(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( ( r4_wellord1(X1,X2)
                    & r4_wellord1(X0,X1) )
                 => r4_wellord1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r4_wellord1(X0,X2)
          & r4_wellord1(X1,X2)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X2) )
     => ( ~ r4_wellord1(X0,sK3)
        & r4_wellord1(X1,sK3)
        & r4_wellord1(X0,X1)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r4_wellord1(X0,X2)
            & r4_wellord1(sK2,X2)
            & r4_wellord1(X0,sK2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r4_wellord1(X0,X2)
                & r4_wellord1(X1,X2)
                & r4_wellord1(X0,X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(sK1,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(sK1,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r4_wellord1(sK1,sK3)
    & r4_wellord1(sK2,sK3)
    & r4_wellord1(sK1,sK2)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f22,f21,f20])).

fof(f35,plain,(
    r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK0(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK0(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    r4_wellord1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ~ r4_wellord1(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r4_wellord1(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_427,plain,
    ( ~ r3_wellord1(X0,X1,k5_relat_1(X2,sK0(sK2,sK3)))
    | r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k5_relat_1(X2,sK0(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(X2,sK0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_816,plain,
    ( ~ r3_wellord1(X0,X1,k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_942,plain,
    ( ~ r3_wellord1(X0,sK3,k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | r4_wellord1(X0,sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_944,plain,
    ( ~ r3_wellord1(sK1,sK3,k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | r4_wellord1(sK1,sK3)
    | ~ v1_relat_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_80,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_4])).

cnf(c_81,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_80])).

cnf(c_516,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(X0,sK0(sK2,sK3)))
    | ~ v1_relat_1(sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_823,plain,
    ( v1_relat_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ v1_relat_1(sK0(sK2,sK3))
    | ~ v1_relat_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_7,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ r3_wellord1(X3,X0,X4)
    | r3_wellord1(X3,X1,k5_relat_1(X4,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_396,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r3_wellord1(X0,X3,k5_relat_1(X2,sK0(sK2,sK3)))
    | ~ r3_wellord1(X1,X3,sK0(sK2,sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(sK0(sK2,sK3))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_469,plain,
    ( r3_wellord1(X0,X1,k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ r3_wellord1(X2,X1,sK0(sK2,sK3))
    | ~ r3_wellord1(X0,X2,sK0(sK1,sK2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK0(sK2,sK3))
    | ~ v1_relat_1(sK0(sK1,sK2))
    | ~ v1_funct_1(sK0(sK2,sK3))
    | ~ v1_funct_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_749,plain,
    ( ~ r3_wellord1(X0,sK2,sK0(sK1,sK2))
    | r3_wellord1(X0,sK3,k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ r3_wellord1(sK2,sK3,sK0(sK2,sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK0(sK2,sK3))
    | ~ v1_relat_1(sK0(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK0(sK2,sK3))
    | ~ v1_funct_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_751,plain,
    ( ~ r3_wellord1(sK2,sK3,sK0(sK2,sK3))
    | ~ r3_wellord1(sK1,sK2,sK0(sK1,sK2))
    | r3_wellord1(sK1,sK3,k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ v1_relat_1(sK0(sK2,sK3))
    | ~ v1_relat_1(sK0(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0(sK2,sK3))
    | ~ v1_funct_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_406,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK0(sK2,sK3))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k5_relat_1(X0,sK0(sK2,sK3)))
    | ~ v1_funct_1(sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_477,plain,
    ( ~ v1_relat_1(sK0(sK2,sK3))
    | ~ v1_relat_1(sK0(sK1,sK2))
    | v1_funct_1(k5_relat_1(sK0(sK1,sK2),sK0(sK2,sK3)))
    | ~ v1_funct_1(sK0(sK2,sK3))
    | ~ v1_funct_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1,plain,
    ( r3_wellord1(X0,X1,sK0(X0,X1))
    | ~ r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,negated_conjecture,
    ( r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_285,plain,
    ( r3_wellord1(sK1,sK2,sK0(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_2,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_275,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | v1_funct_1(sK0(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_3,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_265,plain,
    ( v1_relat_1(sK0(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_9,negated_conjecture,
    ( r4_wellord1(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_255,plain,
    ( r3_wellord1(sK2,sK3,sK0(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_1,c_9])).

cnf(c_245,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | v1_funct_1(sK0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_235,plain,
    ( v1_relat_1(sK0(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_9])).

cnf(c_8,negated_conjecture,
    ( ~ r4_wellord1(sK1,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_944,c_823,c_751,c_477,c_285,c_275,c_265,c_255,c_245,c_235,c_8,c_11,c_12,c_13])).


%------------------------------------------------------------------------------
