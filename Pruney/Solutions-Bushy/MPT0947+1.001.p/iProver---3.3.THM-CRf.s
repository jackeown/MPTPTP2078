%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0947+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:29 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   50 (  94 expanded)
%              Number of clauses        :   22 (  24 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  184 ( 488 expanded)
%              Number of equality atoms :   21 (  76 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r4_wellord1(X0,k1_wellord2(X2))
                  & r4_wellord1(X0,k1_wellord2(X1)) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r4_wellord1(X0,k1_wellord2(X2))
                    & r4_wellord1(X0,k1_wellord2(X1)) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r4_wellord1(X0,k1_wellord2(X2))
          & r4_wellord1(X0,k1_wellord2(X1))
          & v3_ordinal1(X2) )
     => ( sK2 != X1
        & r4_wellord1(X0,k1_wellord2(sK2))
        & r4_wellord1(X0,k1_wellord2(X1))
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
     => ( ? [X2] :
            ( sK1 != X2
            & r4_wellord1(X0,k1_wellord2(X2))
            & r4_wellord1(X0,k1_wellord2(sK1))
            & v3_ordinal1(X2) )
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r4_wellord1(X0,k1_wellord2(X2))
                & r4_wellord1(X0,k1_wellord2(X1))
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(sK0,k1_wellord2(X2))
              & r4_wellord1(sK0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( sK1 != sK2
    & r4_wellord1(sK0,k1_wellord2(sK2))
    & r4_wellord1(sK0,k1_wellord2(sK1))
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    r4_wellord1(sK0,k1_wellord2(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    r4_wellord1(sK0,k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_102,plain,
    ( v1_relat_1(k1_wellord2(X0_36)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_458,plain,
    ( v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_3,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ r4_wellord1(X1,X2)
    | r4_wellord1(X0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_99,plain,
    ( ~ r4_wellord1(X0_35,X1_35)
    | ~ r4_wellord1(X1_35,X2_35)
    | r4_wellord1(X0_35,X2_35)
    | ~ v1_relat_1(X1_35)
    | ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(X2_35) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_434,plain,
    ( ~ r4_wellord1(X0_35,k1_wellord2(sK1))
    | ~ r4_wellord1(k1_wellord2(sK2),X0_35)
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK1))
    | ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(k1_wellord2(sK2))
    | ~ v1_relat_1(k1_wellord2(sK1)) ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_436,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK1))
    | ~ r4_wellord1(k1_wellord2(sK2),sK0)
    | ~ r4_wellord1(sK0,k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK2))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_1,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_101,plain,
    ( ~ r4_wellord1(k1_wellord2(X0_36),k1_wellord2(X1_36))
    | ~ v3_ordinal1(X1_36)
    | ~ v3_ordinal1(X0_36)
    | X1_36 = X0_36 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_366,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK1))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_2,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_100,plain,
    ( ~ r4_wellord1(X0_35,X1_35)
    | r4_wellord1(X1_35,X0_35)
    | ~ v1_relat_1(X1_35)
    | ~ v1_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_360,plain,
    ( r4_wellord1(k1_wellord2(sK2),sK0)
    | ~ r4_wellord1(sK0,k1_wellord2(sK2))
    | ~ v1_relat_1(k1_wellord2(sK2))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_4,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_98,negated_conjecture,
    ( sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_119,plain,
    ( v1_relat_1(k1_wellord2(sK1)) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_5,negated_conjecture,
    ( r4_wellord1(sK0,k1_wellord2(sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,negated_conjecture,
    ( r4_wellord1(sK0,k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_458,c_436,c_366,c_360,c_98,c_119,c_5,c_6,c_7,c_8,c_9])).


%------------------------------------------------------------------------------
