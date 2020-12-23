%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 765 expanded)
%              Number of clauses        :   39 ( 302 expanded)
%              Number of leaves         :    7 ( 190 expanded)
%              Depth                    :   19
%              Number of atoms          :  201 (3917 expanded)
%              Number of equality atoms :   28 ( 391 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(t175_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & v5_funct_1(X2,X1) )
         => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(c_0_6,plain,(
    ! [X20,X21,X22] :
      ( ( X22 != k1_funct_1(X20,X21)
        | r2_hidden(k4_tarski(X21,X22),X20)
        | ~ r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X22 = k1_funct_1(X20,X21)
        | ~ r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X22 != k1_funct_1(X20,X21)
        | X22 = k1_xboole_0
        | r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X22 != k1_xboole_0
        | X22 = k1_funct_1(X20,X21)
        | r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_7,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v5_funct_1(X17,X16)
        | ~ r2_hidden(X18,k1_relat_1(X17))
        | r2_hidden(k1_funct_1(X17,X18),k1_funct_1(X16,X18))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk3_2(X16,X17),k1_relat_1(X17))
        | v5_funct_1(X17,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(k1_funct_1(X17,esk3_2(X16,X17)),k1_funct_1(X16,esk3_2(X16,X17)))
        | v5_funct_1(X17,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_funct_1(X2,X1) )
           => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_1])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))
    | ~ v5_funct_1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v5_funct_1(esk5_0,esk4_0)
    & ~ r1_tarski(k1_relat_1(esk5_0),k1_relat_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_15,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X3,X2))
    | ~ v5_funct_1(X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v5_funct_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,X1),k1_funct_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,esk1_2(X2,k1_relat_1(X1))) = k1_xboole_0
    | r1_tarski(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11])).

fof(c_0_26,plain,(
    ! [X12,X13,X15] :
      ( ( r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,esk2_2(X12,X13))
        | ~ r2_hidden(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),k1_xboole_0)
    | r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_17]),c_0_19])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),X2)
    | r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))) = k1_xboole_0
    | r2_hidden(esk2_2(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),X2),X2)
    | r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_33,plain,
    ( ~ epred1_0
  <=> ! [X1] :
        ( r1_tarski(X1,k1_relat_1(esk4_0))
        | k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))) = k1_xboole_0 ) ),
    introduced(definition)).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))) = k1_xboole_0
    | r1_tarski(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))) = k1_xboole_0
    | r2_hidden(esk2_2(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),k1_xboole_0),X2)
    | r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ epred1_0 ),
    inference(cn,[status(thm)],[inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33]),c_0_33])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))) = k1_xboole_0
    | r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_33]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(X1,k1_relat_1(esk4_0)),X2),esk5_0)
    | r1_tarski(X1,k1_relat_1(esk4_0))
    | X2 != k1_xboole_0
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(esk4_0)),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_18]),c_0_20])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(X1,k1_relat_1(esk4_0)),k1_xboole_0),esk5_0)
    | r1_tarski(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(esk4_0)),k1_relat_1(esk5_0)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk5_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_funct_1(X1,esk1_2(k1_relat_1(X1),X2)),k1_funct_1(X3,esk1_2(k1_relat_1(X1),X2)))
    | r1_tarski(k1_relat_1(X1),X2)
    | ~ v5_funct_1(X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_40])).

cnf(c_0_45,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | X3 = k1_funct_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k1_relat_1(esk5_0),k1_relat_1(esk4_0)),k1_xboole_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk1_2(k1_relat_1(esk5_0),X1)),k1_funct_1(esk4_0,esk1_2(k1_relat_1(esk5_0),X1)))
    | r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(k1_relat_1(esk5_0),k1_relat_1(esk4_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_18]),c_0_20])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_48]),c_0_17]),c_0_19])]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_50]),c_0_50])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_46,c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.13/0.38  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 0.13/0.38  fof(t175_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&v5_funct_1(X2,X1))=>r1_tarski(k1_relat_1(X2),k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.38  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.13/0.38  fof(c_0_6, plain, ![X20, X21, X22]:(((X22!=k1_funct_1(X20,X21)|r2_hidden(k4_tarski(X21,X22),X20)|~r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(~r2_hidden(k4_tarski(X21,X22),X20)|X22=k1_funct_1(X20,X21)|~r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20))))&((X22!=k1_funct_1(X20,X21)|X22=k1_xboole_0|r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(X22!=k1_xboole_0|X22=k1_funct_1(X20,X21)|r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X16, X17, X18]:((~v5_funct_1(X17,X16)|(~r2_hidden(X18,k1_relat_1(X17))|r2_hidden(k1_funct_1(X17,X18),k1_funct_1(X16,X18)))|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&((r2_hidden(esk3_2(X16,X17),k1_relat_1(X17))|v5_funct_1(X17,X16)|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(~r2_hidden(k1_funct_1(X17,esk3_2(X16,X17)),k1_funct_1(X16,esk3_2(X16,X17)))|v5_funct_1(X17,X16)|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.13/0.38  cnf(c_0_8, plain, (X1=k1_xboole_0|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&v5_funct_1(X2,X1))=>r1_tarski(k1_relat_1(X2),k1_relat_1(X1))))), inference(assume_negation,[status(cth)],[t175_funct_1])).
% 0.13/0.38  cnf(c_0_10, plain, (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))|~v5_funct_1(X1,X2)|~r2_hidden(X3,k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_11, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&v5_funct_1(esk5_0,esk4_0))&~r1_tarski(k1_relat_1(esk5_0),k1_relat_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.38  cnf(c_0_15, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X3,X2))|~v5_funct_1(X1,X3)|~v1_funct_1(X3)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (v5_funct_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,X1),k1_funct_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_25, plain, (k1_funct_1(X1,esk1_2(X2,k1_relat_1(X1)))=k1_xboole_0|r1_tarski(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_11])).
% 0.13/0.38  fof(c_0_26, plain, ![X12, X13, X15]:((r2_hidden(esk2_2(X12,X13),X13)|~r2_hidden(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,esk2_2(X12,X13))|~r2_hidden(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0)))=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),k1_xboole_0)|r1_tarski(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_17]), c_0_19])])).
% 0.13/0.38  cnf(c_0_29, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0)))=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),X2)|r1_tarski(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0)))=k1_xboole_0|r2_hidden(esk2_2(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),X2),X2)|r1_tarski(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  fof(c_0_33, plain, (~epred1_0<=>![X1]:(r1_tarski(X1,k1_relat_1(esk4_0))|k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0)))=k1_xboole_0)), introduced(definition)).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0)))=k1_xboole_0|r1_tarski(X1,k1_relat_1(esk4_0))|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_30])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0)))=k1_xboole_0|r2_hidden(esk2_2(k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0))),k1_xboole_0),X2)|r1_tarski(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_32])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~epred1_0), inference(cn,[status(thm)],[inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_33]), c_0_33])])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(X1,k1_relat_1(esk4_0)))=k1_xboole_0|r1_tarski(X1,k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_33]), c_0_36])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(X1,k1_relat_1(esk4_0)),X2),esk5_0)|r1_tarski(X1,k1_relat_1(esk4_0))|X2!=k1_xboole_0|~r2_hidden(esk1_2(X1,k1_relat_1(esk4_0)),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_18]), c_0_20])])).
% 0.13/0.38  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_41, plain, (X2=k1_funct_1(X3,X1)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(X1,k1_relat_1(esk4_0)),k1_xboole_0),esk5_0)|r1_tarski(X1,k1_relat_1(esk4_0))|~r2_hidden(esk1_2(X1,k1_relat_1(esk4_0)),k1_relat_1(esk5_0))), inference(er,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (~r1_tarski(k1_relat_1(esk5_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_44, plain, (r2_hidden(k1_funct_1(X1,esk1_2(k1_relat_1(X1),X2)),k1_funct_1(X3,esk1_2(k1_relat_1(X1),X2)))|r1_tarski(k1_relat_1(X1),X2)|~v5_funct_1(X1,X3)|~v1_funct_1(X3)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_40])).
% 0.13/0.38  cnf(c_0_45, plain, (k1_funct_1(X1,X2)=k1_xboole_0|X3=k1_funct_1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,X3),X1)), inference(spm,[status(thm)],[c_0_41, c_0_11])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k1_relat_1(esk5_0),k1_relat_1(esk4_0)),k1_xboole_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_43])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk1_2(k1_relat_1(esk5_0),X1)),k1_funct_1(esk4_0,esk1_2(k1_relat_1(esk5_0),X1)))|r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(k1_relat_1(esk5_0),k1_relat_1(esk4_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_18]), c_0_20])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_48]), c_0_17]), c_0_19])]), c_0_43])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_49])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_50]), c_0_50])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_46, c_0_51]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 53
% 0.13/0.38  # Proof object clause steps            : 39
% 0.13/0.38  # Proof object formula steps           : 14
% 0.13/0.38  # Proof object conjectures             : 26
% 0.13/0.38  # Proof object clause conjectures      : 23
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 21
% 0.13/0.38  # Proof object simplifying inferences  : 33
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 137
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 30
% 0.13/0.38  # ...remaining for further processing  : 106
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 7
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 346
% 0.13/0.38  # ...of the previous two non-trivial   : 278
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 281
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 6
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 75
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 63
% 0.13/0.38  # Current number of unprocessed clauses: 132
% 0.13/0.38  # ...number of literals in the above   : 675
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1598
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 498
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 56
% 0.13/0.38  # Unit Clause-clause subsumption calls : 200
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 9
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 9436
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.040 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.045 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
