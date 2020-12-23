%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 349 expanded)
%              Number of clauses        :   45 ( 144 expanded)
%              Number of leaves         :   10 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 ( 795 expanded)
%              Number of equality atoms :   76 ( 461 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_10,plain,(
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

fof(c_0_11,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k1_relat_1(esk3_0) = k1_tarski(esk2_0)
    & k2_relat_1(esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X31 = k1_funct_1(X32,X30)
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X30,k1_relat_1(X32))
        | X31 != k1_funct_1(X32,X30)
        | r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X3,X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk3_0) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_16]),c_0_17]),c_0_18])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | k11_relat_1(X24,X25) = k9_relat_1(X24,k1_tarski(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_29,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r2_hidden(k4_tarski(X27,X28),X29)
        | r2_hidden(X28,k11_relat_1(X29,X27))
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(X28,k11_relat_1(X29,X27))
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | X1 != k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | esk1_3(X1,X2,X3) = X1
    | esk1_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk3_0,X1)),esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_24]),c_0_16]),c_0_17]),c_0_18])).

fof(c_0_40,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k9_relat_1(X26,k1_relat_1(X26)) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_41,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,plain,
    ( esk1_3(X1,X2,X3) = X2
    | esk1_3(X1,X2,X3) = X1
    | X3 = k3_enumset1(X1,X1,X1,X1,X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,k11_relat_1(esk3_0,X2))
    | ~ r2_hidden(k4_tarski(X2,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,k1_funct_1(esk3_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k11_relat_1(esk3_0,X1) = k9_relat_1(esk3_0,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,plain,
    ( X3 = k3_enumset1(X1,X1,X1,X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_50,plain,
    ( X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | esk1_3(X2,X2,X1) = X2
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_42])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(esk3_0) != k3_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_24]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk3_0) = k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk3_0)
    | ~ r2_hidden(X2,k11_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_32])).

cnf(c_0_56,plain,
    ( X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k3_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) != k9_relat_1(esk3_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,X1),esk3_0)
    | ~ r2_hidden(X1,k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_3(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k1_funct_1(esk3_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_31]),c_0_32])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk1_3(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk1_3(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))) = k1_funct_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_64]),c_0_57])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.19/0.39  # and selection function SelectNegativeLiterals.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.040 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.39  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.19/0.39  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.19/0.39  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.39  fof(c_0_10, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.39  fof(c_0_11, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_12, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_13, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.19/0.39  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_18, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  fof(c_0_19, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(k1_relat_1(esk3_0)=k1_tarski(esk2_0)&k2_relat_1(esk3_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.39  fof(c_0_20, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_21, plain, ![X30, X31, X32]:(((r2_hidden(X30,k1_relat_1(X32))|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(X31=k1_funct_1(X32,X30)|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(~r2_hidden(X30,k1_relat_1(X32))|X31!=k1_funct_1(X32,X30)|r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (k1_relat_1(esk3_0)=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_26, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X3,X3,X3,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk3_0)=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.39  fof(c_0_28, plain, ![X24, X25]:(~v1_relat_1(X24)|k11_relat_1(X24,X25)=k9_relat_1(X24,k1_tarski(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.19/0.39  fof(c_0_29, plain, ![X27, X28, X29]:((~r2_hidden(k4_tarski(X27,X28),X29)|r2_hidden(X28,k11_relat_1(X29,X27))|~v1_relat_1(X29))&(~r2_hidden(X28,k11_relat_1(X29,X27))|r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.19/0.39  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_0,X1)|X1!=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.39  cnf(c_0_34, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_35, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|esk1_3(X1,X2,X3)=X1|esk1_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_36, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk3_0,X1)),esk3_0)|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk3_0))), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_39, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_24]), c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.39  fof(c_0_40, plain, ![X26]:(~v1_relat_1(X26)|k9_relat_1(X26,k1_relat_1(X26))=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.39  cnf(c_0_41, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_42, plain, (esk1_3(X1,X2,X3)=X2|esk1_3(X1,X2,X3)=X1|X3=k3_enumset1(X1,X1,X1,X1,X2)|r2_hidden(esk1_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,k11_relat_1(esk3_0,X2))|~r2_hidden(k4_tarski(X2,X1),esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,k1_funct_1(esk3_0,esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k11_relat_1(esk3_0,X1)=k9_relat_1(esk3_0,k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (k2_relat_1(esk3_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_47, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.39  cnf(c_0_48, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_49, plain, (X3=k3_enumset1(X1,X1,X1,X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.39  cnf(c_0_50, plain, (X1=k3_enumset1(X2,X2,X2,X2,X2)|esk1_3(X2,X2,X1)=X2|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_42])])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_27])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (k2_relat_1(esk3_0)!=k3_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_24]), c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (k2_relat_1(esk3_0)=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk3_0)|~r2_hidden(X2,k11_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_48, c_0_32])).
% 0.19/0.39  cnf(c_0_56, plain, (X1=k3_enumset1(X2,X2,X2,X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (k3_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))!=k9_relat_1(esk3_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.39  cnf(c_0_59, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,X1),esk3_0)|~r2_hidden(X1,k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_55, c_0_52])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_3(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0))),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (X1=k1_funct_1(esk3_0,X2)|~r2_hidden(k4_tarski(X2,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_31]), c_0_32])])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk1_3(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))),esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (esk1_3(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_relat_1(esk3_0)))=k1_funct_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_64]), c_0_57])]), c_0_58]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 66
% 0.19/0.39  # Proof object clause steps            : 45
% 0.19/0.39  # Proof object formula steps           : 21
% 0.19/0.39  # Proof object conjectures             : 27
% 0.19/0.39  # Proof object clause conjectures      : 24
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 17
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 19
% 0.19/0.39  # Proof object simplifying inferences  : 33
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 10
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 21
% 0.19/0.39  # Removed in clause preprocessing      : 4
% 0.19/0.39  # Initial clauses in saturation        : 17
% 0.19/0.39  # Processed clauses                    : 66
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 2
% 0.19/0.39  # ...remaining for further processing  : 64
% 0.19/0.39  # Other redundant clauses eliminated   : 6
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 4
% 0.19/0.39  # Generated clauses                    : 65
% 0.19/0.39  # ...of the previous two non-trivial   : 51
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 51
% 0.19/0.39  # Factorizations                       : 2
% 0.19/0.39  # Equation resolutions                 : 12
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 41
% 0.19/0.39  #    Positive orientable unit clauses  : 11
% 0.19/0.39  #    Positive unorientable unit clauses: 1
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 28
% 0.19/0.39  # Current number of unprocessed clauses: 19
% 0.19/0.39  # ...number of literals in the above   : 53
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 25
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 70
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 45
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.39  # Unit Clause-clause subsumption calls : 2
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 7
% 0.19/0.39  # BW rewrite match successes           : 6
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 2704
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.047 s
% 0.19/0.39  # System time              : 0.002 s
% 0.19/0.39  # Total time               : 0.048 s
% 0.19/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
