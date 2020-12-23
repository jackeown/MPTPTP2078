%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0560+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:49 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 246 expanded)
%              Number of clauses        :   35 ( 106 expanded)
%              Number of leaves         :    5 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 (1202 expanded)
%              Number of equality atoms :   34 ( 261 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t162_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t162_relat_1])).

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
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | v1_relat_1(k7_relat_1(X33,X34)) ) ),
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
    ( v1_relat_1(esk7_0)
    & r1_tarski(esk8_0,esk9_0)
    & k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0) != k9_relat_1(esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk6_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk6_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk4_3(X1,X2,X3)),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,X2)
    | r2_hidden(k4_tarski(esk5_3(esk7_0,X2,X1),esk4_3(esk7_0,X2,X1)),esk7_0)
    | r2_hidden(esk4_3(esk7_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,X2)
    | r2_hidden(esk5_3(esk7_0,X2,X1),X2)
    | r2_hidden(esk4_3(esk7_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,X2)
    | r2_hidden(k4_tarski(esk5_3(esk7_0,X2,X1),esk4_3(esk7_0,X2,X1)),k7_relat_1(esk7_0,X3))
    | r2_hidden(esk4_3(esk7_0,X2,X1),X1)
    | ~ r2_hidden(esk5_3(esk7_0,X2,X1),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14])])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,esk8_0)
    | r2_hidden(esk5_3(esk7_0,esk8_0,X1),esk9_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,esk8_0)
    | r2_hidden(k4_tarski(esk5_3(esk7_0,esk8_0,X1),esk4_3(esk7_0,esk8_0,X1)),k7_relat_1(esk7_0,esk9_0))
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),k9_relat_1(k7_relat_1(esk7_0,esk9_0),X2))
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1)
    | ~ r2_hidden(esk5_3(esk7_0,esk8_0,X1),X2)
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),k9_relat_1(k7_relat_1(esk7_0,esk9_0),X2))
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1)
    | ~ r2_hidden(esk5_3(esk7_0,esk8_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_12]),c_0_14])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))
    | r2_hidden(esk4_3(esk7_0,esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0) != k9_relat_1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk3_4(X1,X2,X3,X4),X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0)),k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0)) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_30]),c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),X3),X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(k4_tarski(X4,esk4_3(X1,X2,X3)),X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_4(k7_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),esk8_0)
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_4(k7_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),k7_relat_1(esk7_0,esk9_0))
    | ~ v1_relat_1(k7_relat_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_14])]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_4(k7_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_12]),c_0_14])])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_4(k7_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),k7_relat_1(esk7_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_12]),c_0_14])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_4(k7_relat_1(esk7_0,esk9_0),esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),esk4_3(esk7_0,esk8_0,k9_relat_1(k7_relat_1(esk7_0,esk9_0),esk8_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_14])]),c_0_44]),
    [proof]).

%------------------------------------------------------------------------------
