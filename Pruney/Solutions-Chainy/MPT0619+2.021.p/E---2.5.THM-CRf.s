%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 424 expanded)
%              Number of clauses        :   42 ( 167 expanded)
%              Number of leaves         :   11 ( 117 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 ( 921 expanded)
%              Number of equality atoms :  113 ( 598 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(c_0_11,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | k11_relat_1(X27,X28) = k9_relat_1(X27,k1_tarski(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_12,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_18,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & k1_relat_1(esk7_0) = k1_tarski(esk6_0)
    & k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_24,plain,(
    ! [X29] :
      ( ~ v1_relat_1(X29)
      | k9_relat_1(X29,k1_relat_1(X29)) = k2_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X32,X33,X34,X36,X37,X38,X40] :
      ( ( r2_hidden(esk3_3(X32,X33,X34),k1_relat_1(X32))
        | ~ r2_hidden(X34,X33)
        | X33 != k2_relat_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X34 = k1_funct_1(X32,esk3_3(X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k2_relat_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X37,k1_relat_1(X32))
        | X36 != k1_funct_1(X32,X37)
        | r2_hidden(X36,X33)
        | X33 != k2_relat_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(esk4_2(X32,X38),X38)
        | ~ r2_hidden(X40,k1_relat_1(X32))
        | esk4_2(X32,X38) != k1_funct_1(X32,X40)
        | X38 = k2_relat_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( r2_hidden(esk5_2(X32,X38),k1_relat_1(X32))
        | r2_hidden(esk4_2(X32,X38),X38)
        | X38 = k2_relat_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( esk4_2(X32,X38) = k1_funct_1(X32,esk5_2(X32,X38))
        | r2_hidden(esk4_2(X32,X38),X38)
        | X38 = k2_relat_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ( r2_hidden(esk2_2(X24,X25),X24)
        | X24 = k1_tarski(X25)
        | X24 = k1_xboole_0 )
      & ( esk2_2(X24,X25) != X25
        | X24 = k1_tarski(X25)
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_28,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X30,X31] :
      ( ( ~ r2_hidden(X30,k1_relat_1(X31))
        | k11_relat_1(X31,X30) != k1_xboole_0
        | ~ v1_relat_1(X31) )
      & ( k11_relat_1(X31,X30) = k1_xboole_0
        | r2_hidden(X30,k1_relat_1(X31))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk7_0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk7_0) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( k9_relat_1(esk7_0,k1_relat_1(esk7_0)) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_41,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_42,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k2_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_47,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_48,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_relat_1(X1) = k3_enumset1(X2,X2,X2,X2,X2)
    | k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk3_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_29]),c_0_46])])).

cnf(c_0_52,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_29])]),c_0_51])).

cnf(c_0_56,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2))) = esk2_2(k2_relat_1(X1),X2)
    | k2_relat_1(X1) = k3_enumset1(X2,X2,X2,X2,X2)
    | k2_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk7_0) != k3_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)) = esk6_0
    | k3_enumset1(X1,X1,X1,X1,X1) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1))) = esk2_2(k2_relat_1(esk7_0),X1)
    | k3_enumset1(X1,X1,X1,X1,X1) = k2_relat_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_50]),c_0_29])]),c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)) = k1_funct_1(esk7_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_60]),c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_57]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.47  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.028 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.20/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.47  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.20/0.47  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.47  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.20/0.47  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.47  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.20/0.47  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.20/0.47  fof(c_0_11, plain, ![X27, X28]:(~v1_relat_1(X27)|k11_relat_1(X27,X28)=k9_relat_1(X27,k1_tarski(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.20/0.47  fof(c_0_12, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.47  fof(c_0_13, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.47  fof(c_0_14, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.47  fof(c_0_15, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.47  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.20/0.47  fof(c_0_17, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.47  cnf(c_0_18, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.47  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  fof(c_0_23, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(k1_relat_1(esk7_0)=k1_tarski(esk6_0)&k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.47  fof(c_0_24, plain, ![X29]:(~v1_relat_1(X29)|k9_relat_1(X29,k1_relat_1(X29))=k2_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.20/0.47  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  fof(c_0_26, plain, ![X32, X33, X34, X36, X37, X38, X40]:((((r2_hidden(esk3_3(X32,X33,X34),k1_relat_1(X32))|~r2_hidden(X34,X33)|X33!=k2_relat_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(X34=k1_funct_1(X32,esk3_3(X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k2_relat_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(~r2_hidden(X37,k1_relat_1(X32))|X36!=k1_funct_1(X32,X37)|r2_hidden(X36,X33)|X33!=k2_relat_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&((~r2_hidden(esk4_2(X32,X38),X38)|(~r2_hidden(X40,k1_relat_1(X32))|esk4_2(X32,X38)!=k1_funct_1(X32,X40))|X38=k2_relat_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&((r2_hidden(esk5_2(X32,X38),k1_relat_1(X32))|r2_hidden(esk4_2(X32,X38),X38)|X38=k2_relat_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(esk4_2(X32,X38)=k1_funct_1(X32,esk5_2(X32,X38))|r2_hidden(esk4_2(X32,X38),X38)|X38=k2_relat_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.47  fof(c_0_27, plain, ![X24, X25]:((r2_hidden(esk2_2(X24,X25),X24)|(X24=k1_tarski(X25)|X24=k1_xboole_0))&(esk2_2(X24,X25)!=X25|(X24=k1_tarski(X25)|X24=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.20/0.47  cnf(c_0_28, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.47  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_30, negated_conjecture, (k1_relat_1(esk7_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_31, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.47  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.47  cnf(c_0_33, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_34, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  fof(c_0_36, plain, ![X30, X31]:((~r2_hidden(X30,k1_relat_1(X31))|k11_relat_1(X31,X30)!=k1_xboole_0|~v1_relat_1(X31))&(k11_relat_1(X31,X30)=k1_xboole_0|r2_hidden(X30,k1_relat_1(X31))|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.20/0.47  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk7_0,k3_enumset1(X1,X1,X1,X1,X1))=k11_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.47  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk7_0)=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.47  cnf(c_0_39, negated_conjecture, (k9_relat_1(esk7_0,k1_relat_1(esk7_0))=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.20/0.47  cnf(c_0_40, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 0.20/0.47  cnf(c_0_41, plain, (X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.47  cnf(c_0_42, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.47  cnf(c_0_43, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.47  cnf(c_0_44, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_45, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k2_relat_1(esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.20/0.47  cnf(c_0_47, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_48, plain, (X1=X2|X1=X3|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.47  cnf(c_0_49, plain, (k2_relat_1(X1)=k3_enumset1(X2,X2,X2,X2,X2)|k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk3_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.47  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_51, negated_conjecture, (k2_relat_1(esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_29]), c_0_46])])).
% 0.20/0.47  cnf(c_0_52, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_47])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_54, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_48, c_0_38])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (k3_enumset1(X1,X1,X1,X1,X1)=k2_relat_1(esk7_0)|r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_29])]), c_0_51])).
% 0.20/0.47  cnf(c_0_56, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)))=esk2_2(k2_relat_1(X1),X2)|k2_relat_1(X1)=k3_enumset1(X2,X2,X2,X2,X2)|k2_relat_1(X1)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_43])).
% 0.20/0.47  cnf(c_0_57, negated_conjecture, (k2_relat_1(esk7_0)!=k3_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1))=esk6_0|k3_enumset1(X1,X1,X1,X1,X1)=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.47  cnf(c_0_59, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_60, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),X1)))=esk2_2(k2_relat_1(esk7_0),X1)|k3_enumset1(X1,X1,X1,X1,X1)=k2_relat_1(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_50]), c_0_29])]), c_0_51])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)))=esk6_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.47  cnf(c_0_62, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_19]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.47  cnf(c_0_63, negated_conjecture, (esk2_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))=k1_funct_1(esk7_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_60]), c_0_61])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_57]), c_0_51]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 65
% 0.20/0.47  # Proof object clause steps            : 42
% 0.20/0.47  # Proof object formula steps           : 23
% 0.20/0.47  # Proof object conjectures             : 21
% 0.20/0.47  # Proof object clause conjectures      : 18
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 17
% 0.20/0.47  # Proof object initial formulas used   : 11
% 0.20/0.47  # Proof object generating inferences   : 14
% 0.20/0.47  # Proof object simplifying inferences  : 44
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 11
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 26
% 0.20/0.47  # Removed in clause preprocessing      : 4
% 0.20/0.47  # Initial clauses in saturation        : 22
% 0.20/0.47  # Processed clauses                    : 359
% 0.20/0.47  # ...of these trivial                  : 2
% 0.20/0.47  # ...subsumed                          : 124
% 0.20/0.47  # ...remaining for further processing  : 233
% 0.20/0.47  # Other redundant clauses eliminated   : 210
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 4
% 0.20/0.47  # Backward-rewritten                   : 3
% 0.20/0.47  # Generated clauses                    : 4185
% 0.20/0.47  # ...of the previous two non-trivial   : 3442
% 0.20/0.47  # Contextual simplify-reflections      : 8
% 0.20/0.47  # Paramodulations                      : 3956
% 0.20/0.47  # Factorizations                       : 22
% 0.20/0.47  # Equation resolutions                 : 210
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 198
% 0.20/0.47  #    Positive orientable unit clauses  : 12
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 2
% 0.20/0.47  #    Non-unit-clauses                  : 184
% 0.20/0.47  # Current number of unprocessed clauses: 3114
% 0.20/0.47  # ...number of literals in the above   : 17926
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 33
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 9603
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 1836
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 136
% 0.20/0.47  # Unit Clause-clause subsumption calls : 62
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 8
% 0.20/0.47  # BW rewrite match successes           : 2
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 98279
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.124 s
% 0.20/0.47  # System time              : 0.008 s
% 0.20/0.47  # Total time               : 0.132 s
% 0.20/0.47  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
