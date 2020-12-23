%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 169 expanded)
%              Number of clauses        :   31 (  71 expanded)
%              Number of leaves         :    5 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  219 ( 973 expanded)
%              Number of equality atoms :   46 ( 157 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(t74_relat_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( X9 = X10
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(X11,X7)
        | X11 != X12
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | ~ r2_hidden(esk1_2(X7,X8),X7)
        | esk1_2(X7,X8) != esk2_2(X7,X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( esk1_2(X7,X8) = esk2_2(X7,X8)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X19,X21,X22,X23,X26] :
      ( ( r2_hidden(k4_tarski(X18,esk3_5(X15,X16,X17,X18,X19)),X15)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_5(X15,X16,X17,X18,X19),X19),X16)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X21,X23),X15)
        | ~ r2_hidden(k4_tarski(X23,X22),X16)
        | r2_hidden(k4_tarski(X21,X22),X17)
        | X17 != k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)
        | ~ r2_hidden(k4_tarski(esk4_3(X15,X16,X17),X26),X15)
        | ~ r2_hidden(k4_tarski(X26,esk5_3(X15,X16,X17)),X16)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk6_3(X15,X16,X17)),X15)
        | r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk5_3(X15,X16,X17)),X16)
        | r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)
        | X17 = k5_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( v1_relat_1(X4)
       => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
        <=> ( r2_hidden(X1,X3)
            & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t74_relat_1])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))
      | ~ r2_hidden(esk7_0,esk9_0)
      | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0) )
    & ( r2_hidden(esk7_0,esk9_0)
      | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0)) )
    & ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
      | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,plain,(
    ! [X30] : v1_relat_1(k6_relat_1(X30)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_relat_1(X4,X5)
    | X4 != k6_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X6),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk7_0,esk9_0)
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | v1_relat_1(k5_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_16,plain,
    ( esk3_5(X1,X2,X3,X4,X5) = X4
    | X3 != k5_relat_1(X1,X2)
    | X1 != k6_relat_1(X6)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_0,esk9_0)
    | r2_hidden(esk7_0,X1)
    | k5_relat_1(k6_relat_1(esk9_0),esk10_0) != k5_relat_1(X2,X3)
    | X2 != k6_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( esk3_5(k6_relat_1(X1),X2,X3,X4,X5) = X4
    | X3 != k5_relat_1(k6_relat_1(X1),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk7_0,esk9_0)
    | r2_hidden(esk7_0,X1)
    | k5_relat_1(k6_relat_1(esk9_0),esk10_0) != k5_relat_1(X2,X3)
    | X2 != k6_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_17])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k5_relat_1(k6_relat_1(X5),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
    | r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk7_0,esk9_0)
    | r2_hidden(esk7_0,X1)
    | k6_relat_1(esk9_0) != k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_17]),c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
    | r2_hidden(k4_tarski(esk7_0,esk8_0),X1)
    | k5_relat_1(k6_relat_1(esk9_0),esk10_0) != k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | X2 != k6_relat_1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk7_0,esk9_0) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_20])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk7_0),X1)
    | X1 != k6_relat_1(esk9_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),X2)
    | X2 != k5_relat_1(X3,esk10_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),X3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_20])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk7_0),k6_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_17])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ r2_hidden(esk7_0,esk9_0)
    | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),X1)
    | X1 != k5_relat_1(k6_relat_1(esk9_0),esk10_0)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_17])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(X1,X2))
    | k5_relat_1(X1,X2) != k5_relat_1(k6_relat_1(esk9_0),esk10_0)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_20]),c_0_17])]),c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_19]),c_0_20]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.027 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_relat_1)).
% 0.20/0.42  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.20/0.42  fof(t74_relat_1, conjecture, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 0.20/0.42  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.42  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.42  fof(c_0_5, plain, ![X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k6_relat_1(X7)|~v1_relat_1(X8))&(X9=X10|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k6_relat_1(X7)|~v1_relat_1(X8)))&(~r2_hidden(X11,X7)|X11!=X12|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k6_relat_1(X7)|~v1_relat_1(X8)))&((~r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|(~r2_hidden(esk1_2(X7,X8),X7)|esk1_2(X7,X8)!=esk2_2(X7,X8))|X8=k6_relat_1(X7)|~v1_relat_1(X8))&((r2_hidden(esk1_2(X7,X8),X7)|r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|X8=k6_relat_1(X7)|~v1_relat_1(X8))&(esk1_2(X7,X8)=esk2_2(X7,X8)|r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|X8=k6_relat_1(X7)|~v1_relat_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.20/0.42  fof(c_0_6, plain, ![X15, X16, X17, X18, X19, X21, X22, X23, X26]:((((r2_hidden(k4_tarski(X18,esk3_5(X15,X16,X17,X18,X19)),X15)|~r2_hidden(k4_tarski(X18,X19),X17)|X17!=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk3_5(X15,X16,X17,X18,X19),X19),X16)|~r2_hidden(k4_tarski(X18,X19),X17)|X17!=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15)))&(~r2_hidden(k4_tarski(X21,X23),X15)|~r2_hidden(k4_tarski(X23,X22),X16)|r2_hidden(k4_tarski(X21,X22),X17)|X17!=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15)))&((~r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)|(~r2_hidden(k4_tarski(esk4_3(X15,X16,X17),X26),X15)|~r2_hidden(k4_tarski(X26,esk5_3(X15,X16,X17)),X16))|X17=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk6_3(X15,X16,X17)),X15)|r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)|X17=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk5_3(X15,X16,X17)),X16)|r2_hidden(k4_tarski(esk4_3(X15,X16,X17),esk5_3(X15,X16,X17)),X17)|X17=k5_relat_1(X15,X16)|~v1_relat_1(X17)|~v1_relat_1(X16)|~v1_relat_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.20/0.42  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4))))), inference(assume_negation,[status(cth)],[t74_relat_1])).
% 0.20/0.42  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.42  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  fof(c_0_10, negated_conjecture, (v1_relat_1(esk10_0)&((~r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))|(~r2_hidden(esk7_0,esk9_0)|~r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)))&((r2_hidden(esk7_0,esk9_0)|r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0)))&(r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)|r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.20/0.42  cnf(c_0_11, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X2),X3)|X3!=k6_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.42  fof(c_0_12, plain, ![X30]:v1_relat_1(k6_relat_1(X30)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.42  cnf(c_0_13, plain, (r2_hidden(X1,X2)|X3!=k5_relat_1(X4,X5)|X4!=k6_relat_1(X2)|~r2_hidden(k4_tarski(X1,X6),X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X5)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.42  cnf(c_0_14, negated_conjecture, (r2_hidden(esk7_0,esk9_0)|r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  fof(c_0_15, plain, ![X28, X29]:(~v1_relat_1(X28)|~v1_relat_1(X29)|v1_relat_1(k5_relat_1(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.42  cnf(c_0_16, plain, (esk3_5(X1,X2,X3,X4,X5)=X4|X3!=k5_relat_1(X1,X2)|X1!=k6_relat_1(X6)|~r2_hidden(k4_tarski(X4,X5),X3)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_11, c_0_9])).
% 0.20/0.42  cnf(c_0_17, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (r2_hidden(esk7_0,esk9_0)|r2_hidden(esk7_0,X1)|k5_relat_1(k6_relat_1(esk9_0),esk10_0)!=k5_relat_1(X2,X3)|X2!=k6_relat_1(X1)|~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.42  cnf(c_0_19, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_22, plain, (esk3_5(k6_relat_1(X1),X2,X3,X4,X5)=X4|X3!=k5_relat_1(k6_relat_1(X1),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_17])])).
% 0.20/0.42  cnf(c_0_23, negated_conjecture, (r2_hidden(esk7_0,esk9_0)|r2_hidden(esk7_0,X1)|k5_relat_1(k6_relat_1(esk9_0),esk10_0)!=k5_relat_1(X2,X3)|X2!=k6_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_17])])).
% 0.20/0.42  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X2),X3)|X4!=k5_relat_1(k6_relat_1(X5),X3)|~r2_hidden(k4_tarski(X1,X2),X4)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)|r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)|X1!=X3|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (r2_hidden(esk7_0,esk9_0)|r2_hidden(esk7_0,X1)|k6_relat_1(esk9_0)!=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_17]), c_0_20])])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)|r2_hidden(k4_tarski(esk7_0,esk8_0),X1)|k5_relat_1(k6_relat_1(esk9_0),esk10_0)!=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.42  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,X1),X2)|X2!=k6_relat_1(X3)|~r2_hidden(X1,X3)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (r2_hidden(esk7_0,esk9_0)), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)|~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_20])])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk7_0),X1)|X1!=k6_relat_1(esk9_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),X2)|X2!=k5_relat_1(X3,esk10_0)|~r2_hidden(k4_tarski(X1,esk7_0),X3)|~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_20])])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk7_0),k6_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_17])])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (~r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~r2_hidden(esk7_0,esk9_0)|~r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),X1)|X1!=k5_relat_1(k6_relat_1(esk9_0),esk10_0)|~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_17])])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (~r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~r2_hidden(k4_tarski(esk7_0,esk8_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_30])])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk8_0),k5_relat_1(X1,X2))|k5_relat_1(X1,X2)!=k5_relat_1(k6_relat_1(esk9_0),esk10_0)|~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_19])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_20]), c_0_17])]), c_0_32])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_19]), c_0_20]), c_0_17])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 42
% 0.20/0.42  # Proof object clause steps            : 31
% 0.20/0.42  # Proof object formula steps           : 11
% 0.20/0.42  # Proof object conjectures             : 21
% 0.20/0.42  # Proof object clause conjectures      : 18
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 12
% 0.20/0.42  # Proof object initial formulas used   : 5
% 0.20/0.42  # Proof object generating inferences   : 17
% 0.20/0.42  # Proof object simplifying inferences  : 28
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 5
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 18
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 18
% 0.20/0.42  # Processed clauses                    : 283
% 0.20/0.42  # ...of these trivial                  : 1
% 0.20/0.42  # ...subsumed                          : 13
% 0.20/0.42  # ...remaining for further processing  : 269
% 0.20/0.42  # Other redundant clauses eliminated   : 1
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 35
% 0.20/0.42  # Backward-rewritten                   : 17
% 0.20/0.42  # Generated clauses                    : 620
% 0.20/0.42  # ...of the previous two non-trivial   : 598
% 0.20/0.42  # Contextual simplify-reflections      : 4
% 0.20/0.42  # Paramodulations                      : 548
% 0.20/0.42  # Factorizations                       : 2
% 0.20/0.42  # Equation resolutions                 : 70
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 198
% 0.20/0.42  #    Positive orientable unit clauses  : 13
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 184
% 0.20/0.42  # Current number of unprocessed clauses: 349
% 0.20/0.42  # ...number of literals in the above   : 2505
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 70
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 10683
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 3237
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 52
% 0.20/0.42  # Unit Clause-clause subsumption calls : 182
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 13
% 0.20/0.42  # BW rewrite match successes           : 4
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 22633
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.073 s
% 0.20/0.42  # System time              : 0.002 s
% 0.20/0.42  # Total time               : 0.075 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
