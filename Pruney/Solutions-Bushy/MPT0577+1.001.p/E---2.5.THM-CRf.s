%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0577+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:51 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 160 expanded)
%              Number of clauses        :   35 (  75 expanded)
%              Number of leaves         :    4 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  231 (1032 expanded)
%              Number of equality atoms :   38 ( 195 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(t181_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(c_0_4,plain,(
    ! [X19,X20,X21,X22,X23,X25,X26,X27,X30] :
      ( ( r2_hidden(k4_tarski(X22,esk4_5(X19,X20,X21,X22,X23)),X19)
        | ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk4_5(X19,X20,X21,X22,X23),X23),X20)
        | ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X25,X27),X19)
        | ~ r2_hidden(k4_tarski(X27,X26),X20)
        | r2_hidden(k4_tarski(X25,X26),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)
        | ~ r2_hidden(k4_tarski(esk5_3(X19,X20,X21),X30),X19)
        | ~ r2_hidden(k4_tarski(X30,esk6_3(X19,X20,X21)),X20)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk7_3(X19,X20,X21)),X19)
        | r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk7_3(X19,X20,X21),esk6_3(X19,X20,X21)),X20)
        | r2_hidden(k4_tarski(esk5_3(X19,X20,X21),esk6_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ v1_relat_1(X33)
      | v1_relat_1(k5_relat_1(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X12,X13,X14,X15,X17] :
      ( ( r2_hidden(k4_tarski(X10,esk1_4(X7,X8,X9,X10)),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k10_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk1_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k10_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X12,X13),X7)
        | ~ r2_hidden(X13,X8)
        | r2_hidden(X12,X9)
        | X9 != k10_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(esk2_3(X7,X14,X15),X15)
        | ~ r2_hidden(k4_tarski(esk2_3(X7,X14,X15),X17),X7)
        | ~ r2_hidden(X17,X14)
        | X15 = k10_relat_1(X7,X14)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk2_3(X7,X14,X15),esk3_3(X7,X14,X15)),X7)
        | r2_hidden(esk2_3(X7,X14,X15),X15)
        | X15 = k10_relat_1(X7,X14)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk3_3(X7,X14,X15),X14)
        | r2_hidden(esk2_3(X7,X14,X15),X15)
        | X15 = k10_relat_1(X7,X14)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t181_relat_1])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X4)),k5_relat_1(X5,X2))
    | ~ r2_hidden(k4_tarski(X1,X4),X5)
    | ~ r2_hidden(X4,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_relat_1(esk10_0)
    & k10_relat_1(k5_relat_1(esk9_0,esk10_0),esk8_0) != k10_relat_1(esk9_0,k10_relat_1(esk10_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k10_relat_1(k5_relat_1(X2,X3),X4))
    | ~ r2_hidden(esk1_4(X3,X5,k10_relat_1(X3,X5),X6),X4)
    | ~ r2_hidden(k4_tarski(X1,X6),X2)
    | ~ r2_hidden(X6,k10_relat_1(X3,X5))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X3 = k10_relat_1(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X4),X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_8])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_8])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k10_relat_1(k5_relat_1(X2,X3),X4))
    | ~ r2_hidden(k4_tarski(X1,X5),X2)
    | ~ r2_hidden(X5,k10_relat_1(X3,X4))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k10_relat_1(esk9_0,X2)
    | r2_hidden(k4_tarski(esk2_3(esk9_0,X2,X1),esk3_3(esk9_0,X2,X1)),esk9_0)
    | r2_hidden(esk2_3(esk9_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( X1 = k10_relat_1(X2,X3)
    | ~ r2_hidden(esk4_5(X2,X4,k5_relat_1(X2,X4),esk2_3(X2,X3,X1),X5),X3)
    | ~ r2_hidden(k4_tarski(esk2_3(X2,X3,X1),X5),k5_relat_1(X2,X4))
    | ~ r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),k10_relat_1(X2,X5))
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ r2_hidden(X4,X5)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k10_relat_1(esk9_0,X2)
    | r2_hidden(esk2_3(esk9_0,X2,X1),k10_relat_1(k5_relat_1(esk9_0,X3),X4))
    | r2_hidden(esk2_3(esk9_0,X2,X1),X1)
    | ~ r2_hidden(esk3_3(esk9_0,X2,X1),k10_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k10_relat_1(esk9_0,X2)
    | r2_hidden(esk3_3(esk9_0,X2,X1),X2)
    | r2_hidden(esk2_3(esk9_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_34,plain,
    ( X1 = k10_relat_1(X2,k10_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(esk2_3(X2,k10_relat_1(X3,X4),X1),X5),k5_relat_1(X2,X3))
    | ~ r2_hidden(esk2_3(X2,k10_relat_1(X3,X4),X1),X1)
    | ~ r2_hidden(X5,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k10_relat_1(esk9_0,k10_relat_1(X2,X3))
    | r2_hidden(esk2_3(esk9_0,k10_relat_1(X2,X3),X1),k10_relat_1(k5_relat_1(esk9_0,X2),X3))
    | r2_hidden(esk2_3(esk9_0,k10_relat_1(X2,X3),X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( X1 = k10_relat_1(X2,k10_relat_1(X3,X4))
    | ~ r2_hidden(esk1_4(k5_relat_1(X2,X3),X5,k10_relat_1(k5_relat_1(X2,X3),X5),esk2_3(X2,k10_relat_1(X3,X4),X1)),X4)
    | ~ r2_hidden(esk2_3(X2,k10_relat_1(X3,X4),X1),k10_relat_1(k5_relat_1(X2,X3),X5))
    | ~ r2_hidden(esk2_3(X2,k10_relat_1(X3,X4),X1),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_12]),c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( X1 = k10_relat_1(esk9_0,k10_relat_1(esk10_0,X2))
    | r2_hidden(esk2_3(esk9_0,k10_relat_1(esk10_0,X2),X1),k10_relat_1(k5_relat_1(esk9_0,esk10_0),X2))
    | r2_hidden(esk2_3(esk9_0,k10_relat_1(esk10_0,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( X1 = k10_relat_1(X2,k10_relat_1(X3,X4))
    | ~ r2_hidden(esk2_3(X2,k10_relat_1(X3,X4),X1),k10_relat_1(k5_relat_1(X2,X3),X4))
    | ~ r2_hidden(esk2_3(X2,k10_relat_1(X3,X4),X1),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_8])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk9_0,esk10_0),X1) = k10_relat_1(esk9_0,k10_relat_1(esk10_0,X1))
    | r2_hidden(esk2_3(esk9_0,k10_relat_1(esk10_0,X1),k10_relat_1(k5_relat_1(esk9_0,esk10_0),X1)),k10_relat_1(k5_relat_1(esk9_0,esk10_0),X1)) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk9_0,esk10_0),esk8_0) != k10_relat_1(esk9_0,k10_relat_1(esk10_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk9_0,esk10_0),X1) = k10_relat_1(esk9_0,k10_relat_1(esk10_0,X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23]),c_0_36])]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])]),
    [proof]).

%------------------------------------------------------------------------------
