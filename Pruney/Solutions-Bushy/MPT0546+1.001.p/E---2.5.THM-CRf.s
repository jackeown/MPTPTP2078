%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0546+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:47 EST 2020

% Result     : Theorem 0.23s
% Output     : CNFRefutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 153 expanded)
%              Number of clauses        :   28 (  70 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 ( 770 expanded)
%              Number of equality atoms :   42 ( 190 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t148_relat_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(k4_tarski(X11,X12),X6)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk1_3(X6,X7,X8),X7)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X38)
      | v1_relat_1(k7_relat_1(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( r2_hidden(k4_tarski(esk3_4(X15,X16,X17,X18),X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k9_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk3_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k9_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X15)
        | ~ r2_hidden(X21,X16)
        | r2_hidden(X20,X17)
        | X17 != k9_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(esk4_3(X15,X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk4_3(X15,X22,X23)),X15)
        | ~ r2_hidden(X25,X22)
        | X23 = k9_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk5_3(X15,X22,X23),esk4_3(X15,X22,X23)),X15)
        | r2_hidden(esk4_3(X15,X22,X23),X23)
        | X23 = k9_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk5_3(X15,X22,X23),X22)
        | r2_hidden(esk4_3(X15,X22,X23),X23)
        | X23 = k9_relat_1(X15,X22)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & k2_relat_1(k7_relat_1(esk10_0,esk9_0)) != k9_relat_1(esk10_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk4_3(X1,X2,X3)),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(esk6_3(X27,X28,X29),X29),X27)
        | X28 != k2_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X32,X31),X27)
        | r2_hidden(X31,X28)
        | X28 != k2_relat_1(X27) )
      & ( ~ r2_hidden(esk7_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(X36,esk7_2(X33,X34)),X33)
        | X34 = k2_relat_1(X33) )
      & ( r2_hidden(esk7_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk8_2(X33,X34),esk7_2(X33,X34)),X33)
        | X34 = k2_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( X1 = k9_relat_1(esk10_0,X2)
    | r2_hidden(k4_tarski(esk5_3(esk10_0,X2,X1),esk4_3(esk10_0,X2,X1)),esk10_0)
    | r2_hidden(esk4_3(esk10_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k9_relat_1(esk10_0,X2)
    | r2_hidden(k4_tarski(esk5_3(esk10_0,X2,X1),esk4_3(esk10_0,X2,X1)),k7_relat_1(esk10_0,X3))
    | r2_hidden(esk4_3(esk10_0,X2,X1),X1)
    | ~ r2_hidden(esk5_3(esk10_0,X2,X1),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( X1 = k9_relat_1(esk10_0,X2)
    | r2_hidden(esk5_3(esk10_0,X2,X1),X2)
    | r2_hidden(esk4_3(esk10_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k9_relat_1(esk10_0,X2)
    | r2_hidden(k4_tarski(esk5_3(esk10_0,X2,X1),esk4_3(esk10_0,X2,X1)),k7_relat_1(esk10_0,X2))
    | r2_hidden(esk4_3(esk10_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k9_relat_1(esk10_0,X2)
    | r2_hidden(esk4_3(esk10_0,X2,X1),k2_relat_1(k7_relat_1(esk10_0,X2)))
    | r2_hidden(esk4_3(esk10_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk10_0,X1)) = k9_relat_1(esk10_0,X1)
    | r2_hidden(esk4_3(esk10_0,X1,k2_relat_1(k7_relat_1(esk10_0,X1))),k2_relat_1(k7_relat_1(esk10_0,X1))) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(k4_tarski(X4,esk4_3(X1,X2,X3)),X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk10_0,X1)) = k9_relat_1(esk10_0,X1)
    | r2_hidden(k4_tarski(esk6_3(k7_relat_1(esk10_0,X1),k2_relat_1(k7_relat_1(esk10_0,X1)),esk4_3(esk10_0,X1,k2_relat_1(k7_relat_1(esk10_0,X1)))),esk4_3(esk10_0,X1,k2_relat_1(k7_relat_1(esk10_0,X1)))),k7_relat_1(esk10_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk10_0,X1)) = k9_relat_1(esk10_0,X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_3(esk10_0,X1,k2_relat_1(k7_relat_1(esk10_0,X1)))),esk10_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_13])])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk10_0,X1)) = k9_relat_1(esk10_0,X1)
    | r2_hidden(k4_tarski(esk6_3(k7_relat_1(esk10_0,X1),k2_relat_1(k7_relat_1(esk10_0,X1)),esk4_3(esk10_0,X1,k2_relat_1(k7_relat_1(esk10_0,X1)))),esk4_3(esk10_0,X1,k2_relat_1(k7_relat_1(esk10_0,X1)))),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_13])])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk10_0,X1)) = k9_relat_1(esk10_0,X1)
    | r2_hidden(esk6_3(k7_relat_1(esk10_0,X1),k2_relat_1(k7_relat_1(esk10_0,X1)),esk4_3(esk10_0,X1,k2_relat_1(k7_relat_1(esk10_0,X1)))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_13])])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk10_0,esk9_0)) != k9_relat_1(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk10_0,X1)) = k9_relat_1(esk10_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
