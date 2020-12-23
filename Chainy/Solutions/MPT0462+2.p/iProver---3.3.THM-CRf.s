%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0462+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 27.28s
% Output     : CNFRefutation 27.28s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 109 expanded)
%              Number of clauses        :   23 (  25 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  220 ( 637 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f746,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f747,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f746])).

fof(f1716,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f747])).

fof(f687,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1179,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f687])).

fof(f1180,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1179])).

fof(f2672,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1180])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1128,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2602,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1128])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1542,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2563,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1542])).

fof(f688,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1181,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f688])).

fof(f1182,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1181])).

fof(f2673,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1182])).

fof(f689,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f690,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f689])).

fof(f1183,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f690])).

fof(f1184,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1183])).

fof(f1595,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,sK146))
        & r1_tarski(X2,sK146)
        & r1_tarski(X0,X1)
        & v1_relat_1(sK146) ) ) ),
    introduced(choice_axiom,[])).

fof(f1594,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(X0,X1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(X0,sK145),k5_relat_1(X1,X3))
            & r1_tarski(sK145,X3)
            & r1_tarski(X0,X1)
            & v1_relat_1(X3) )
        & v1_relat_1(sK145) ) ) ),
    introduced(choice_axiom,[])).

fof(f1593,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(sK144,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(X0,sK144)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(sK144) ) ) ),
    introduced(choice_axiom,[])).

fof(f1592,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK143,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK143,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK143) ) ),
    introduced(choice_axiom,[])).

fof(f1596,plain,
    ( ~ r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK144,sK146))
    & r1_tarski(sK145,sK146)
    & r1_tarski(sK143,sK144)
    & v1_relat_1(sK146)
    & v1_relat_1(sK145)
    & v1_relat_1(sK144)
    & v1_relat_1(sK143) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK143,sK144,sK145,sK146])],[f1184,f1595,f1594,f1593,f1592])).

fof(f2680,plain,(
    ~ r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK144,sK146)) ),
    inference(cnf_transformation,[],[f1596])).

fof(f2679,plain,(
    r1_tarski(sK145,sK146) ),
    inference(cnf_transformation,[],[f1596])).

fof(f2678,plain,(
    r1_tarski(sK143,sK144) ),
    inference(cnf_transformation,[],[f1596])).

fof(f2677,plain,(
    v1_relat_1(sK146) ),
    inference(cnf_transformation,[],[f1596])).

fof(f2675,plain,(
    v1_relat_1(sK144) ),
    inference(cnf_transformation,[],[f1596])).

fof(f2674,plain,(
    v1_relat_1(sK143) ),
    inference(cnf_transformation,[],[f1596])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1716])).

cnf(c_48358,plain,
    ( ~ r1_tarski(X0,k5_relat_1(sK144,sK146))
    | ~ r1_tarski(k5_relat_1(sK143,sK145),X0)
    | r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK144,sK146)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_58202,plain,
    ( ~ r1_tarski(k5_relat_1(X0,sK146),k5_relat_1(sK144,sK146))
    | ~ r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(X0,sK146))
    | r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK144,sK146)) ),
    inference(instantiation,[status(thm)],[c_48358])).

cnf(c_110055,plain,
    ( ~ r1_tarski(k5_relat_1(sK143,sK146),k5_relat_1(sK144,sK146))
    | r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK144,sK146))
    | ~ r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK143,sK146)) ),
    inference(instantiation,[status(thm)],[c_58202])).

cnf(c_1061,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2672])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2602])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2563])).

cnf(c_4836,plain,
    ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1061,c_991,c_951])).

cnf(c_4837,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_4836])).

cnf(c_58415,plain,
    ( r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK143,X0))
    | ~ r1_tarski(sK145,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK143) ),
    inference(instantiation,[status(thm)],[c_4837])).

cnf(c_81276,plain,
    ( r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK143,sK146))
    | ~ r1_tarski(sK145,sK146)
    | ~ v1_relat_1(sK146)
    | ~ v1_relat_1(sK143) ),
    inference(instantiation,[status(thm)],[c_58415])).

cnf(c_1062,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2673])).

cnf(c_4831,plain,
    ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_991,c_951])).

cnf(c_4832,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_4831])).

cnf(c_58203,plain,
    ( ~ r1_tarski(X0,sK144)
    | r1_tarski(k5_relat_1(X0,sK146),k5_relat_1(sK144,sK146))
    | ~ v1_relat_1(sK146)
    | ~ v1_relat_1(sK144) ),
    inference(instantiation,[status(thm)],[c_4832])).

cnf(c_78016,plain,
    ( r1_tarski(k5_relat_1(sK143,sK146),k5_relat_1(sK144,sK146))
    | ~ r1_tarski(sK143,sK144)
    | ~ v1_relat_1(sK146)
    | ~ v1_relat_1(sK144) ),
    inference(instantiation,[status(thm)],[c_58203])).

cnf(c_1063,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK143,sK145),k5_relat_1(sK144,sK146)) ),
    inference(cnf_transformation,[],[f2680])).

cnf(c_1064,negated_conjecture,
    ( r1_tarski(sK145,sK146) ),
    inference(cnf_transformation,[],[f2679])).

cnf(c_1065,negated_conjecture,
    ( r1_tarski(sK143,sK144) ),
    inference(cnf_transformation,[],[f2678])).

cnf(c_1066,negated_conjecture,
    ( v1_relat_1(sK146) ),
    inference(cnf_transformation,[],[f2677])).

cnf(c_1068,negated_conjecture,
    ( v1_relat_1(sK144) ),
    inference(cnf_transformation,[],[f2675])).

cnf(c_1069,negated_conjecture,
    ( v1_relat_1(sK143) ),
    inference(cnf_transformation,[],[f2674])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_110055,c_81276,c_78016,c_1063,c_1064,c_1065,c_1066,c_1068,c_1069])).

%------------------------------------------------------------------------------
