%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0798+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:08 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 111 expanded)
%              Number of clauses        :   21 (  23 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  220 ( 550 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   10 (   4 average)
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

fof(f6,plain,(
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

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK0(X0,X1))
        & v1_funct_1(sK0(X0,X1))
        & v1_relat_1(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
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
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X1,X0,k2_funct_1(X2))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK0(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r4_wellord1(X0,X1)
             => r4_wellord1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r4_wellord1(sK2,X0)
        & r4_wellord1(X0,sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r4_wellord1(X1,X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r4_wellord1(X1,sK1)
          & r4_wellord1(sK1,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r4_wellord1(sK2,sK1)
    & r4_wellord1(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f18,f17])).

fof(f29,plain,(
    r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK0(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK0(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ~ r4_wellord1(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r4_wellord1(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_326,plain,
    ( ~ r3_wellord1(X0,X1,k2_funct_1(sK0(sK1,sK2)))
    | r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k2_funct_1(sK0(sK1,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_381,plain,
    ( ~ r3_wellord1(sK2,sK1,k2_funct_1(sK0(sK1,sK2)))
    | r4_wellord1(sK2,sK1)
    | ~ v1_relat_1(k2_funct_1(sK0(sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_6,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | r3_wellord1(X1,X0,k2_funct_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_309,plain,
    ( ~ r3_wellord1(X0,X1,sK0(sK1,sK2))
    | r3_wellord1(X1,X0,k2_funct_1(sK0(sK1,sK2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK0(sK1,sK2))
    | ~ v1_funct_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_362,plain,
    ( ~ r3_wellord1(sK1,sK2,sK0(sK1,sK2))
    | r3_wellord1(sK2,sK1,k2_funct_1(sK0(sK1,sK2)))
    | ~ v1_relat_1(sK0(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_319,plain,
    ( ~ v1_relat_1(sK0(sK1,sK2))
    | v1_relat_1(k2_funct_1(sK0(sK1,sK2)))
    | ~ v1_funct_1(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_320,plain,
    ( ~ v1_relat_1(sK0(sK1,sK2))
    | ~ v1_funct_1(sK0(sK1,sK2))
    | v1_funct_1(k2_funct_1(sK0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r3_wellord1(X0,X1,sK0(X0,X1))
    | ~ r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,negated_conjecture,
    ( r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_222,plain,
    ( r3_wellord1(sK1,sK2,sK0(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_1,c_8])).

cnf(c_2,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_212,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | v1_funct_1(sK0(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_2,c_8])).

cnf(c_3,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_202,plain,
    ( v1_relat_1(sK0(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_3,c_8])).

cnf(c_7,negated_conjecture,
    ( ~ r4_wellord1(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_381,c_362,c_319,c_320,c_222,c_212,c_202,c_7,c_9,c_10])).


%------------------------------------------------------------------------------
