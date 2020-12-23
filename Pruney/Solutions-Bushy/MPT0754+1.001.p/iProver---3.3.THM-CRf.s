%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0754+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:03 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   40 (  96 expanded)
%              Number of clauses        :   18 (  20 expanded)
%              Number of leaves         :    5 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 720 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X1)
              & v1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ( ~ v5_ordinal1(sK2)
          | ~ v1_funct_1(sK2)
          | ~ v5_relat_1(sK2,X1)
          | ~ v1_relat_1(sK2) )
        & v5_ordinal1(sK2)
        & v1_funct_1(sK2)
        & v5_relat_1(sK2,X0)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(X2)
              | ~ v1_funct_1(X2)
              | ~ v5_relat_1(X2,X1)
              | ~ v1_relat_1(X2) )
            & v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,sK1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ( ~ v5_ordinal1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v5_relat_1(sK2,sK1)
      | ~ v1_relat_1(sK2) )
    & v5_ordinal1(sK2)
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).

fof(f19,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,
    ( ~ v5_ordinal1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_159,plain,
    ( ~ r1_tarski(X0_37,X1_37)
    | ~ r1_tarski(X2_37,X0_37)
    | r1_tarski(X2_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_176,plain,
    ( ~ r1_tarski(X0_37,sK0)
    | r1_tarski(X0_37,sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_184,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_6,negated_conjecture,
    ( v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_87,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v5_relat_1(sK2,X0) ),
    inference(resolution,[status(thm)],[c_1,c_7])).

cnf(c_122,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

cnf(c_3,negated_conjecture,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,negated_conjecture,
    ( v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_46,negated_conjecture,
    ( ~ v5_relat_1(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_7,c_5,c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_98,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | v5_relat_1(sK2,X0) ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_116,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[status(thm)],[c_46,c_98])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_184,c_122,c_116,c_8])).


%------------------------------------------------------------------------------
