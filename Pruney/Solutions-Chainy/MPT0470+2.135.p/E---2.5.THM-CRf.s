%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:13 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 345 expanded)
%              Number of clauses        :   40 ( 157 expanded)
%              Number of leaves         :    7 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  247 (1247 expanded)
%              Number of equality atoms :   46 ( 257 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

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

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(k4_tarski(X14,X15),X12)
        | r2_hidden(k4_tarski(X14,X15),X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk1_2(X12,X16),esk2_2(X12,X16)),X12)
        | r1_tarski(X12,X16)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X12,X16),esk2_2(X12,X16)),X16)
        | r1_tarski(X12,X16)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22,X23,X25,X26,X27,X30] :
      ( ( r2_hidden(k4_tarski(X22,esk3_5(X19,X20,X21,X22,X23)),X19)
        | ~ r2_hidden(k4_tarski(X22,X23),X21)
        | X21 != k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk3_5(X19,X20,X21,X22,X23),X23),X20)
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
      & ( ~ r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21)),X21)
        | ~ r2_hidden(k4_tarski(esk4_3(X19,X20,X21),X30),X19)
        | ~ r2_hidden(k4_tarski(X30,esk5_3(X19,X20,X21)),X20)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk6_3(X19,X20,X21)),X19)
        | r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk5_3(X19,X20,X21)),X20)
        | r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21)),X21)
        | X21 = k5_relat_1(X19,X20)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | v1_relat_1(k4_xboole_0(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_10,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k2_xboole_0(X8,X9)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

fof(c_0_12,plain,(
    ! [X10,X11] : ~ r2_hidden(X10,k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
      | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X6)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | ~ r1_tarski(X2,X6) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_21,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_tarski(X2,k2_zfmisc_1(k4_tarski(X4,esk3_5(X2,X3,X1,X4,X5)),X6)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X1 != k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X1 != k5_relat_1(k1_xboole_0,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,X1),X2)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_13,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X6)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ r1_tarski(X2,X6) ),
    inference(spm,[status(thm)],[c_0_13,c_0_30])).

cnf(c_0_34,plain,
    ( X1 != k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_31])).

cnf(c_0_35,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,k2_zfmisc_1(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_32])).

cnf(c_0_36,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_tarski(X3,k2_zfmisc_1(k4_tarski(esk3_5(X2,X3,X1,X4,X5),X5),X6)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_33])).

cnf(c_0_37,plain,
    ( ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_25])])).

cnf(c_0_40,plain,
    ( X1 != k5_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_25])])).

cnf(c_0_41,plain,
    ( X1 = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | r2_hidden(k4_tarski(esk4_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1),esk5_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1)),X1)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_39])).

cnf(c_0_43,plain,
    ( X1 = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | X1 != k5_relat_1(X5,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_42])).

cnf(c_0_45,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_46,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_25])])).

cnf(c_0_47,plain,
    ( k5_relat_1(X1,k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_25])])).

cnf(c_0_48,plain,
    ( k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_25])])).

cnf(c_0_49,negated_conjecture,
    ( k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_25])])).

cnf(c_0_51,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
    | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_22])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:18:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.43/0.61  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.43/0.61  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.43/0.61  #
% 0.43/0.61  # Preprocessing time       : 0.027 s
% 0.43/0.61  # Presaturation interreduction done
% 0.43/0.61  
% 0.43/0.61  # Proof found!
% 0.43/0.61  # SZS status Theorem
% 0.43/0.61  # SZS output start CNFRefutation
% 0.43/0.61  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.43/0.61  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.43/0.61  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.43/0.61  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.43/0.61  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.43/0.61  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.43/0.61  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.43/0.61  fof(c_0_7, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(k4_tarski(X14,X15),X12)|r2_hidden(k4_tarski(X14,X15),X13))|~v1_relat_1(X12))&((r2_hidden(k4_tarski(esk1_2(X12,X16),esk2_2(X12,X16)),X12)|r1_tarski(X12,X16)|~v1_relat_1(X12))&(~r2_hidden(k4_tarski(esk1_2(X12,X16),esk2_2(X12,X16)),X16)|r1_tarski(X12,X16)|~v1_relat_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.43/0.61  fof(c_0_8, plain, ![X19, X20, X21, X22, X23, X25, X26, X27, X30]:((((r2_hidden(k4_tarski(X22,esk3_5(X19,X20,X21,X22,X23)),X19)|~r2_hidden(k4_tarski(X22,X23),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk3_5(X19,X20,X21,X22,X23),X23),X20)|~r2_hidden(k4_tarski(X22,X23),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19)))&(~r2_hidden(k4_tarski(X25,X27),X19)|~r2_hidden(k4_tarski(X27,X26),X20)|r2_hidden(k4_tarski(X25,X26),X21)|X21!=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19)))&((~r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21)),X21)|(~r2_hidden(k4_tarski(esk4_3(X19,X20,X21),X30),X19)|~r2_hidden(k4_tarski(X30,esk5_3(X19,X20,X21)),X20))|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&((r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk6_3(X19,X20,X21)),X19)|r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21)),X21)|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk6_3(X19,X20,X21),esk5_3(X19,X20,X21)),X20)|r2_hidden(k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21)),X21)|X21=k5_relat_1(X19,X20)|~v1_relat_1(X21)|~v1_relat_1(X20)|~v1_relat_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.43/0.61  fof(c_0_9, plain, ![X32, X33]:(~v1_relat_1(X32)|v1_relat_1(k4_xboole_0(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.43/0.61  fof(c_0_10, plain, ![X8, X9]:k4_xboole_0(X8,k2_xboole_0(X8,X9))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.43/0.61  fof(c_0_11, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.43/0.61  fof(c_0_12, plain, ![X10, X11]:~r2_hidden(X10,k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.43/0.61  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.43/0.61  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.43/0.61  cnf(c_0_15, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.43/0.61  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.43/0.61  fof(c_0_17, negated_conjecture, (v1_relat_1(esk7_0)&(k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.43/0.61  cnf(c_0_18, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.43/0.61  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X6)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X5),X4)|~r1_tarski(X2,X6)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.43/0.61  fof(c_0_20, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.43/0.61  cnf(c_0_21, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.43/0.61  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.43/0.61  cnf(c_0_23, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_tarski(X2,k2_zfmisc_1(k4_tarski(X4,esk3_5(X2,X3,X1,X4,X5)),X6))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.43/0.61  cnf(c_0_24, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.43/0.61  cnf(c_0_25, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.43/0.61  cnf(c_0_26, plain, (X1!=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.43/0.61  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.43/0.61  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X1!=k5_relat_1(k1_xboole_0,X3)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.43/0.61  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.43/0.61  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.43/0.61  cnf(c_0_31, plain, (r1_tarski(k5_relat_1(k1_xboole_0,X1),X2)|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_28])).
% 0.43/0.61  cnf(c_0_32, plain, (X1=k5_relat_1(X2,X3)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_13, c_0_29])).
% 0.43/0.61  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X6)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X4,X5),X3)|~r1_tarski(X2,X6)), inference(spm,[status(thm)],[c_0_13, c_0_30])).
% 0.43/0.61  cnf(c_0_34, plain, (X1!=k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)), inference(spm,[status(thm)],[c_0_23, c_0_31])).
% 0.43/0.61  cnf(c_0_35, plain, (X1=k5_relat_1(X2,X3)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,k2_zfmisc_1(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4))), inference(spm,[status(thm)],[c_0_18, c_0_32])).
% 0.43/0.61  cnf(c_0_36, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_tarski(X3,k2_zfmisc_1(k4_tarski(esk3_5(X2,X3,X1,X4,X5),X5),X6))), inference(spm,[status(thm)],[c_0_18, c_0_33])).
% 0.43/0.61  cnf(c_0_37, plain, (~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))), inference(er,[status(thm)],[c_0_34])).
% 0.43/0.61  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.43/0.61  cnf(c_0_39, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_24]), c_0_25])])).
% 0.43/0.61  cnf(c_0_40, plain, (X1!=k5_relat_1(X2,k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_25])])).
% 0.43/0.61  cnf(c_0_41, plain, (X1=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|r2_hidden(k4_tarski(esk4_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1),esk5_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1)),X1)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.43/0.61  cnf(c_0_42, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_39])).
% 0.43/0.61  cnf(c_0_43, plain, (X1=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|X1!=k5_relat_1(X5,k1_xboole_0)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(X1)|~v1_relat_1(X5)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.43/0.61  cnf(c_0_44, plain, (X1=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,k2_zfmisc_1(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3))), inference(spm,[status(thm)],[c_0_18, c_0_42])).
% 0.43/0.61  cnf(c_0_45, plain, (k5_relat_1(X1,k1_xboole_0)=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_43])).
% 0.43/0.61  cnf(c_0_46, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_25])])).
% 0.43/0.61  cnf(c_0_47, plain, (k5_relat_1(X1,k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))=k1_xboole_0|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_25])])).
% 0.43/0.61  cnf(c_0_48, plain, (k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2))=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_25])])).
% 0.43/0.61  cnf(c_0_49, negated_conjecture, (k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2))=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_22])).
% 0.43/0.61  cnf(c_0_50, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_25])])).
% 0.43/0.61  cnf(c_0_51, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.43/0.61  cnf(c_0_52, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_22])).
% 0.43/0.61  cnf(c_0_53, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_22])])).
% 0.43/0.61  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_22])]), ['proof']).
% 0.43/0.61  # SZS output end CNFRefutation
% 0.43/0.61  # Proof object total steps             : 55
% 0.43/0.61  # Proof object clause steps            : 40
% 0.43/0.61  # Proof object formula steps           : 15
% 0.43/0.61  # Proof object conjectures             : 11
% 0.43/0.61  # Proof object clause conjectures      : 8
% 0.43/0.61  # Proof object formula conjectures     : 3
% 0.43/0.61  # Proof object initial clauses used    : 12
% 0.43/0.61  # Proof object initial formulas used   : 7
% 0.43/0.61  # Proof object generating inferences   : 28
% 0.43/0.61  # Proof object simplifying inferences  : 18
% 0.43/0.61  # Training examples: 0 positive, 0 negative
% 0.43/0.61  # Parsed axioms                        : 7
% 0.43/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.61  # Initial clauses                      : 15
% 0.43/0.61  # Removed in clause preprocessing      : 0
% 0.43/0.61  # Initial clauses in saturation        : 15
% 0.43/0.61  # Processed clauses                    : 1014
% 0.43/0.61  # ...of these trivial                  : 1
% 0.43/0.61  # ...subsumed                          : 551
% 0.43/0.61  # ...remaining for further processing  : 462
% 0.43/0.61  # Other redundant clauses eliminated   : 0
% 0.43/0.61  # Clauses deleted for lack of memory   : 0
% 0.43/0.61  # Backward-subsumed                    : 13
% 0.43/0.61  # Backward-rewritten                   : 1
% 0.43/0.61  # Generated clauses                    : 5211
% 0.43/0.61  # ...of the previous two non-trivial   : 5135
% 0.43/0.61  # Contextual simplify-reflections      : 0
% 0.43/0.61  # Paramodulations                      : 5026
% 0.43/0.61  # Factorizations                       : 0
% 0.43/0.61  # Equation resolutions                 : 185
% 0.43/0.61  # Propositional unsat checks           : 0
% 0.43/0.61  #    Propositional check models        : 0
% 0.43/0.61  #    Propositional check unsatisfiable : 0
% 0.43/0.61  #    Propositional clauses             : 0
% 0.43/0.61  #    Propositional clauses after purity: 0
% 0.43/0.61  #    Propositional unsat core size     : 0
% 0.43/0.61  #    Propositional preprocessing time  : 0.000
% 0.43/0.61  #    Propositional encoding time       : 0.000
% 0.43/0.61  #    Propositional solver time         : 0.000
% 0.43/0.61  #    Success case prop preproc time    : 0.000
% 0.43/0.61  #    Success case prop encoding time   : 0.000
% 0.43/0.61  #    Success case prop solver time     : 0.000
% 0.43/0.61  # Current number of processed clauses  : 433
% 0.43/0.61  #    Positive orientable unit clauses  : 4
% 0.43/0.61  #    Positive unorientable unit clauses: 0
% 0.43/0.61  #    Negative unit clauses             : 3
% 0.43/0.61  #    Non-unit-clauses                  : 426
% 0.43/0.61  # Current number of unprocessed clauses: 4139
% 0.43/0.61  # ...number of literals in the above   : 52396
% 0.43/0.61  # Current number of archived formulas  : 0
% 0.43/0.61  # Current number of archived clauses   : 29
% 0.43/0.61  # Clause-clause subsumption calls (NU) : 89960
% 0.43/0.61  # Rec. Clause-clause subsumption calls : 13907
% 0.43/0.61  # Non-unit clause-clause subsumptions  : 558
% 0.43/0.61  # Unit Clause-clause subsumption calls : 95
% 0.43/0.61  # Rewrite failures with RHS unbound    : 0
% 0.43/0.61  # BW rewrite match attempts            : 1
% 0.43/0.61  # BW rewrite match successes           : 1
% 0.43/0.61  # Condensation attempts                : 0
% 0.43/0.61  # Condensation successes               : 0
% 0.43/0.61  # Termbank termtop insertions          : 163846
% 0.43/0.61  
% 0.43/0.61  # -------------------------------------------------
% 0.43/0.61  # User time                : 0.267 s
% 0.43/0.61  # System time              : 0.008 s
% 0.43/0.61  # Total time               : 0.274 s
% 0.43/0.61  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
