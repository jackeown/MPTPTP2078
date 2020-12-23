%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0788+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 207 expanded)
%              Number of clauses        :   24 (  74 expanded)
%              Number of leaves         :    5 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  157 (1349 expanded)
%              Number of equality atoms :   32 ( 238 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
        <=> ( X1 = X2
            | r2_hidden(X1,k1_wellord1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(t37_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t30_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
          <=> ( X1 = X2
              | r2_hidden(X1,k1_wellord1(X3,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_wellord1])).

fof(c_0_6,plain,(
    ! [X3337,X3338,X3339,X3340,X3341,X3342,X3343] :
      ( ( X3340 != X3338
        | ~ r2_hidden(X3340,X3339)
        | X3339 != k1_wellord1(X3337,X3338)
        | ~ v1_relat_1(X3337) )
      & ( r2_hidden(k4_tarski(X3340,X3338),X3337)
        | ~ r2_hidden(X3340,X3339)
        | X3339 != k1_wellord1(X3337,X3338)
        | ~ v1_relat_1(X3337) )
      & ( X3341 = X3338
        | ~ r2_hidden(k4_tarski(X3341,X3338),X3337)
        | r2_hidden(X3341,X3339)
        | X3339 != k1_wellord1(X3337,X3338)
        | ~ v1_relat_1(X3337) )
      & ( ~ r2_hidden(esk256_3(X3337,X3342,X3343),X3343)
        | esk256_3(X3337,X3342,X3343) = X3342
        | ~ r2_hidden(k4_tarski(esk256_3(X3337,X3342,X3343),X3342),X3337)
        | X3343 = k1_wellord1(X3337,X3342)
        | ~ v1_relat_1(X3337) )
      & ( esk256_3(X3337,X3342,X3343) != X3342
        | r2_hidden(esk256_3(X3337,X3342,X3343),X3343)
        | X3343 = k1_wellord1(X3337,X3342)
        | ~ v1_relat_1(X3337) )
      & ( r2_hidden(k4_tarski(esk256_3(X3337,X3342,X3343),X3342),X3337)
        | r2_hidden(esk256_3(X3337,X3342,X3343),X3343)
        | X3343 = k1_wellord1(X3337,X3342)
        | ~ v1_relat_1(X3337) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

fof(c_0_7,plain,(
    ! [X3467,X3468,X3469] :
      ( ( ~ r2_hidden(k4_tarski(X3467,X3468),X3469)
        | r1_tarski(k1_wellord1(X3469,X3467),k1_wellord1(X3469,X3468))
        | ~ v2_wellord1(X3469)
        | ~ r2_hidden(X3467,k3_relat_1(X3469))
        | ~ r2_hidden(X3468,k3_relat_1(X3469))
        | ~ v1_relat_1(X3469) )
      & ( ~ r1_tarski(k1_wellord1(X3469,X3467),k1_wellord1(X3469,X3468))
        | r2_hidden(k4_tarski(X3467,X3468),X3469)
        | ~ v2_wellord1(X3469)
        | ~ r2_hidden(X3467,k3_relat_1(X3469))
        | ~ r2_hidden(X3468,k3_relat_1(X3469))
        | ~ v1_relat_1(X3469) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_wellord1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk280_0)
    & v2_wellord1(esk280_0)
    & r2_hidden(esk278_0,k3_relat_1(esk280_0))
    & r2_hidden(esk279_0,k3_relat_1(esk280_0))
    & ( esk278_0 != esk279_0
      | ~ r1_tarski(k1_wellord1(esk280_0,esk278_0),k1_wellord1(esk280_0,esk279_0)) )
    & ( ~ r2_hidden(esk278_0,k1_wellord1(esk280_0,esk279_0))
      | ~ r1_tarski(k1_wellord1(esk280_0,esk278_0),k1_wellord1(esk280_0,esk279_0)) )
    & ( r1_tarski(k1_wellord1(esk280_0,esk278_0),k1_wellord1(esk280_0,esk279_0))
      | esk278_0 = esk279_0
      | r2_hidden(esk278_0,k1_wellord1(esk280_0,esk279_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_9,plain,(
    ! [X2603,X2604,X2605] :
      ( ( r2_hidden(X2603,k3_relat_1(X2605))
        | ~ r2_hidden(k4_tarski(X2603,X2604),X2605)
        | ~ v1_relat_1(X2605) )
      & ( r2_hidden(X2604,k3_relat_1(X2605))
        | ~ r2_hidden(k4_tarski(X2603,X2604),X2605)
        | ~ v1_relat_1(X2605) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk280_0,esk278_0),k1_wellord1(esk280_0,esk279_0))
    | esk278_0 = esk279_0
    | r2_hidden(esk278_0,k1_wellord1(esk280_0,esk279_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v2_wellord1(esk280_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk280_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk279_0,k3_relat_1(esk280_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk278_0,k3_relat_1(esk280_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v2_wellord1(X3)
    | ~ r2_hidden(X1,k3_relat_1(X3))
    | ~ r2_hidden(X2,k3_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( esk279_0 = esk278_0
    | r2_hidden(esk278_0,k1_wellord1(esk280_0,esk279_0))
    | r2_hidden(k4_tarski(esk278_0,esk279_0),esk280_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_22,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk279_0 = esk278_0
    | r2_hidden(k4_tarski(esk278_0,esk279_0),esk280_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])])).

cnf(c_0_25,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk278_0,k1_wellord1(esk280_0,esk279_0))
    | ~ r1_tarski(k1_wellord1(esk280_0,esk278_0),k1_wellord1(esk280_0,esk279_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( esk279_0 = esk278_0
    | r1_tarski(k1_wellord1(esk280_0,esk278_0),k1_wellord1(esk280_0,esk279_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_13]),c_0_14])])).

cnf(c_0_29,negated_conjecture,
    ( esk279_0 = esk278_0
    | r2_hidden(esk278_0,k1_wellord1(esk280_0,esk279_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_14])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk278_0 != esk279_0
    | ~ r1_tarski(k1_wellord1(esk280_0,esk278_0),k1_wellord1(esk280_0,esk279_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( esk279_0 = esk278_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
