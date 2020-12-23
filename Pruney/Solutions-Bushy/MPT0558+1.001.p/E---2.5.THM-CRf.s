%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0558+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:49 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 207 expanded)
%              Number of clauses        :   31 (  92 expanded)
%              Number of leaves         :    5 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 (1045 expanded)
%              Number of equality atoms :   38 ( 238 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t160_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t160_relat_1])).

fof(c_0_6,plain,(
    ! [X30,X31,X32,X33,X34,X36,X37,X38,X41] :
      ( ( r2_hidden(k4_tarski(X33,esk7_5(X30,X31,X32,X33,X34)),X30)
        | ~ r2_hidden(k4_tarski(X33,X34),X32)
        | X32 != k5_relat_1(X30,X31)
        | ~ v1_relat_1(X32)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk7_5(X30,X31,X32,X33,X34),X34),X31)
        | ~ r2_hidden(k4_tarski(X33,X34),X32)
        | X32 != k5_relat_1(X30,X31)
        | ~ v1_relat_1(X32)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(X36,X38),X30)
        | ~ r2_hidden(k4_tarski(X38,X37),X31)
        | r2_hidden(k4_tarski(X36,X37),X32)
        | X32 != k5_relat_1(X30,X31)
        | ~ v1_relat_1(X32)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk8_3(X30,X31,X32),esk9_3(X30,X31,X32)),X32)
        | ~ r2_hidden(k4_tarski(esk8_3(X30,X31,X32),X41),X30)
        | ~ r2_hidden(k4_tarski(X41,esk9_3(X30,X31,X32)),X31)
        | X32 = k5_relat_1(X30,X31)
        | ~ v1_relat_1(X32)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk8_3(X30,X31,X32),esk10_3(X30,X31,X32)),X30)
        | r2_hidden(k4_tarski(esk8_3(X30,X31,X32),esk9_3(X30,X31,X32)),X32)
        | X32 = k5_relat_1(X30,X31)
        | ~ v1_relat_1(X32)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk10_3(X30,X31,X32),esk9_3(X30,X31,X32)),X31)
        | r2_hidden(k4_tarski(esk8_3(X30,X31,X32),esk9_3(X30,X31,X32)),X32)
        | X32 = k5_relat_1(X30,X31)
        | ~ v1_relat_1(X32)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | ~ v1_relat_1(X44)
      | v1_relat_1(k5_relat_1(X43,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X12,X13,X14,X15,X17] :
      ( ( r2_hidden(k4_tarski(esk1_4(X7,X8,X9,X10),X10),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k9_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk1_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k9_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X13,X12),X7)
        | ~ r2_hidden(X13,X8)
        | r2_hidden(X12,X9)
        | X9 != k9_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(esk2_3(X7,X14,X15),X15)
        | ~ r2_hidden(k4_tarski(X17,esk2_3(X7,X14,X15)),X7)
        | ~ r2_hidden(X17,X14)
        | X15 = k9_relat_1(X7,X14)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk3_3(X7,X14,X15),esk2_3(X7,X14,X15)),X7)
        | r2_hidden(esk2_3(X7,X14,X15),X15)
        | X15 = k9_relat_1(X7,X14)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk3_3(X7,X14,X15),X14)
        | r2_hidden(esk2_3(X7,X14,X15),X15)
        | X15 = k9_relat_1(X7,X14)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & v1_relat_1(esk12_0)
    & k2_relat_1(k5_relat_1(esk11_0,esk12_0)) != k9_relat_1(esk12_0,k2_relat_1(esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(k4_tarski(esk4_3(X19,X20,X21),X21),X19)
        | X20 != k2_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X24,X23),X19)
        | r2_hidden(X23,X20)
        | X20 != k2_relat_1(X19) )
      & ( ~ r2_hidden(esk5_2(X25,X26),X26)
        | ~ r2_hidden(k4_tarski(X28,esk5_2(X25,X26)),X25)
        | X26 = k2_relat_1(X25) )
      & ( r2_hidden(esk5_2(X25,X26),X26)
        | r2_hidden(k4_tarski(esk6_2(X25,X26),esk5_2(X25,X26)),X25)
        | X26 = k2_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( X1 = k9_relat_1(esk12_0,X2)
    | r2_hidden(k4_tarski(esk3_3(esk12_0,X2,X1),esk2_3(esk12_0,X2,X1)),esk12_0)
    | r2_hidden(esk2_3(esk12_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( X1 = k9_relat_1(esk12_0,X2)
    | r2_hidden(esk3_3(esk12_0,X2,X1),X2)
    | r2_hidden(esk2_3(esk12_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( X1 = k9_relat_1(esk12_0,X2)
    | r2_hidden(k4_tarski(X3,esk2_3(esk12_0,X2,X1)),k5_relat_1(X4,esk12_0))
    | r2_hidden(esk2_3(esk12_0,X2,X1),X1)
    | ~ r2_hidden(k4_tarski(X3,esk3_3(esk12_0,X2,X1)),X4)
    | ~ v1_relat_1(X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k9_relat_1(esk12_0,k2_relat_1(X2))
    | r2_hidden(k4_tarski(esk4_3(X2,k2_relat_1(X2),esk3_3(esk12_0,k2_relat_1(X2),X1)),esk3_3(esk12_0,k2_relat_1(X2),X1)),X2)
    | r2_hidden(esk2_3(esk12_0,k2_relat_1(X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k9_relat_1(esk12_0,k2_relat_1(X2))
    | r2_hidden(k4_tarski(esk4_3(X2,k2_relat_1(X2),esk3_3(esk12_0,k2_relat_1(X2),X1)),esk2_3(esk12_0,k2_relat_1(X2),X1)),k5_relat_1(X2,esk12_0))
    | r2_hidden(esk2_3(esk12_0,k2_relat_1(X2),X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k9_relat_1(esk12_0,k2_relat_1(esk11_0))
    | r2_hidden(k4_tarski(esk4_3(esk11_0,k2_relat_1(esk11_0),esk3_3(esk12_0,k2_relat_1(esk11_0),X1)),esk2_3(esk12_0,k2_relat_1(esk11_0),X1)),k5_relat_1(esk11_0,esk12_0))
    | r2_hidden(esk2_3(esk12_0,k2_relat_1(esk11_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k9_relat_1(esk12_0,k2_relat_1(esk11_0))
    | r2_hidden(esk2_3(esk12_0,k2_relat_1(esk11_0),X1),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))
    | r2_hidden(esk2_3(esk12_0,k2_relat_1(esk11_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk11_0,esk12_0)) != k9_relat_1(esk12_0,k2_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0))),k2_relat_1(k5_relat_1(esk11_0,esk12_0))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(k5_relat_1(esk11_0,esk12_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),k5_relat_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(k4_tarski(X4,esk2_3(X1,X2,X3)),X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(k5_relat_1(esk11_0,esk12_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk7_5(esk11_0,esk12_0,k5_relat_1(esk11_0,esk12_0),esk4_3(k5_relat_1(esk11_0,esk12_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0))))),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_14]),c_0_25])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk12_0)
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_14])]),c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk7_5(esk11_0,esk12_0,k5_relat_1(esk11_0,esk12_0),esk4_3(k5_relat_1(esk11_0,esk12_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_5(esk11_0,esk12_0,k5_relat_1(esk11_0,esk12_0),esk4_3(k5_relat_1(esk11_0,esk12_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk2_3(esk12_0,k2_relat_1(esk11_0),k2_relat_1(k5_relat_1(esk11_0,esk12_0)))),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_14]),c_0_25])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),
    [proof]).

%------------------------------------------------------------------------------
