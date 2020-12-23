%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:19 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 754 expanded)
%              Number of clauses        :   62 ( 323 expanded)
%              Number of leaves         :   14 ( 209 expanded)
%              Depth                    :   14
%              Number of atoms          :  243 (1487 expanded)
%              Number of equality atoms :   66 ( 642 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t37_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(t35_funct_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(c_0_14,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k1_relat_1(k5_relat_1(X25,X26)) = k10_relat_1(X25,k1_relat_1(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_17,plain,(
    ! [X27] :
      ( k1_relat_1(k6_relat_1(X27)) = X27
      & k2_relat_1(k6_relat_1(X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_18,plain,(
    ! [X32] :
      ( v1_relat_1(k6_relat_1(X32))
      & v1_funct_1(k6_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t37_funct_1])).

fof(c_0_20,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_24,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | k7_relat_1(X31,X30) = k5_relat_1(k6_relat_1(X30),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) != k3_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_29,plain,(
    ! [X16,X17] : k2_tarski(X16,X17) = k2_tarski(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_34,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | r1_tarski(k1_relat_1(k7_relat_1(X29,X28)),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_35,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) != k3_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X4,X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_26]),c_0_26])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) != k1_setfam_1(k2_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_31]),c_0_32])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_22]),c_0_22]),c_0_32]),c_0_32])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_31]),c_0_32])).

cnf(c_0_48,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))) != k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_32])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_54,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,k1_relat_1(X35))
        | ~ r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( r2_hidden(k1_funct_1(X35,X33),k1_relat_1(X34))
        | ~ r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( ~ r2_hidden(X33,k1_relat_1(X35))
        | ~ r2_hidden(k1_funct_1(X35,X33),k1_relat_1(X34))
        | r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_55,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | k1_funct_1(k6_relat_1(X37),X36) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_26])])).

cnf(c_0_58,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_31]),c_0_32])).

cnf(c_0_59,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_31]),c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))
    | r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),X2)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) != k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X2,X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_31]),c_0_32])).

cnf(c_0_63,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k1_funct_1(k6_relat_1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),X3))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))
    | r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),X1)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) != k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_58])).

cnf(c_0_68,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_31]),c_0_32])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))
    | r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),X1)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47])])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_26])]),c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))
    | r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_47])])).

cnf(c_0_75,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X3,X3,X3,X4))
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)
    | ~ r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_57]),c_0_71])]),c_0_72])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k10_relat_1(k6_relat_1(X3),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_35]),c_0_25]),c_0_65]),c_0_26]),c_0_26])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))
    | r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_57]),c_0_71])])).

cnf(c_0_80,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))
    | ~ r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))
    | ~ r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_44]),c_0_76])])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_64]),c_0_65]),c_0_26]),c_0_25])])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_24]),c_0_26])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))
    | r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))
    | ~ r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_71]),c_0_76])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_71])])).

cnf(c_0_87,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_88,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_51])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_57]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.27/3.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 3.27/3.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 3.27/3.45  #
% 3.27/3.45  # Preprocessing time       : 0.045 s
% 3.27/3.45  # Presaturation interreduction done
% 3.27/3.45  
% 3.27/3.45  # Proof found!
% 3.27/3.45  # SZS status Theorem
% 3.27/3.45  # SZS output start CNFRefutation
% 3.27/3.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.27/3.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/3.45  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.27/3.45  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.27/3.45  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.27/3.45  fof(t37_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 3.27/3.45  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.27/3.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.27/3.45  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.27/3.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.27/3.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.27/3.45  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.27/3.45  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 3.27/3.45  fof(t35_funct_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k1_funct_1(k6_relat_1(X2),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 3.27/3.45  fof(c_0_14, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.27/3.45  fof(c_0_15, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.27/3.45  fof(c_0_16, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|k1_relat_1(k5_relat_1(X25,X26))=k10_relat_1(X25,k1_relat_1(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 3.27/3.45  fof(c_0_17, plain, ![X27]:(k1_relat_1(k6_relat_1(X27))=X27&k2_relat_1(k6_relat_1(X27))=X27), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 3.27/3.45  fof(c_0_18, plain, ![X32]:(v1_relat_1(k6_relat_1(X32))&v1_funct_1(k6_relat_1(X32))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 3.27/3.45  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(k1_relat_1(X2),X1))), inference(assume_negation,[status(cth)],[t37_funct_1])).
% 3.27/3.45  fof(c_0_20, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 3.27/3.45  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.27/3.45  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.27/3.45  fof(c_0_23, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.27/3.45  cnf(c_0_24, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.27/3.45  cnf(c_0_25, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.27/3.45  cnf(c_0_26, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.27/3.45  fof(c_0_27, plain, ![X30, X31]:(~v1_relat_1(X31)|k7_relat_1(X31,X30)=k5_relat_1(k6_relat_1(X30),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 3.27/3.45  fof(c_0_28, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))!=k3_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 3.27/3.45  fof(c_0_29, plain, ![X16, X17]:k2_tarski(X16,X17)=k2_tarski(X17,X16), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 3.27/3.45  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.27/3.45  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 3.27/3.45  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.27/3.45  fof(c_0_33, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.27/3.45  fof(c_0_34, plain, ![X28, X29]:(~v1_relat_1(X29)|r1_tarski(k1_relat_1(k7_relat_1(X29,X28)),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 3.27/3.45  cnf(c_0_35, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 3.27/3.45  cnf(c_0_36, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.27/3.45  cnf(c_0_37, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))!=k3_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.27/3.45  cnf(c_0_38, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.27/3.45  cnf(c_0_39, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X4,X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.27/3.45  cnf(c_0_41, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.27/3.45  cnf(c_0_42, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k10_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_26]), c_0_26])])).
% 3.27/3.45  cnf(c_0_43, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))!=k1_setfam_1(k2_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_22]), c_0_22]), c_0_32]), c_0_32])).
% 3.27/3.45  cnf(c_0_45, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.27/3.45  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_39])).
% 3.27/3.45  cnf(c_0_47, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_48, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_26])])).
% 3.27/3.45  cnf(c_0_49, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.27/3.45  cnf(c_0_50, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.27/3.45  cnf(c_0_51, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))!=k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 3.27/3.45  cnf(c_0_52, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.27/3.45  fof(c_0_54, plain, ![X33, X34, X35]:(((r2_hidden(X33,k1_relat_1(X35))|~r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))|(~v1_relat_1(X35)|~v1_funct_1(X35))|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(r2_hidden(k1_funct_1(X35,X33),k1_relat_1(X34))|~r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))|(~v1_relat_1(X35)|~v1_funct_1(X35))|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(~r2_hidden(X33,k1_relat_1(X35))|~r2_hidden(k1_funct_1(X35,X33),k1_relat_1(X34))|r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))|(~v1_relat_1(X35)|~v1_funct_1(X35))|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 3.27/3.45  fof(c_0_55, plain, ![X36, X37]:(~r2_hidden(X36,X37)|k1_funct_1(k6_relat_1(X37),X36)=X36), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).
% 3.27/3.45  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.27/3.45  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_24]), c_0_26])])).
% 3.27/3.45  cnf(c_0_58, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_59, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.27/3.45  cnf(c_0_60, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))|r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),X2)|k1_setfam_1(k2_enumset1(X1,X1,X1,X2))!=k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 3.27/3.45  cnf(c_0_62, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X2,X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_63, plain, (r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.27/3.45  cnf(c_0_64, plain, (k1_funct_1(k6_relat_1(X2),X1)=X1|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 3.27/3.45  cnf(c_0_65, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.27/3.45  cnf(c_0_66, plain, (r2_hidden(X1,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 3.27/3.45  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))|r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),X1)|k1_setfam_1(k2_enumset1(X1,X1,X1,X2))!=k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_58])).
% 3.27/3.45  cnf(c_0_68, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_31]), c_0_32])).
% 3.27/3.45  cnf(c_0_69, plain, (r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_60])).
% 3.27/3.45  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))|r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),X1)|~r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47])])).
% 3.27/3.45  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.27/3.45  cnf(c_0_72, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(er,[status(thm)],[c_0_62])).
% 3.27/3.45  cnf(c_0_73, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_26])]), c_0_66])).
% 3.27/3.45  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))|r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))|~r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_47])])).
% 3.27/3.45  cnf(c_0_75, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X3,X3,X3,X4))|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X4)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)|~r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 3.27/3.45  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_57]), c_0_71])]), c_0_72])).
% 3.27/3.45  cnf(c_0_77, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.27/3.45  cnf(c_0_78, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k10_relat_1(k6_relat_1(X3),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_35]), c_0_25]), c_0_65]), c_0_26]), c_0_26])])).
% 3.27/3.45  cnf(c_0_79, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))))|r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_57]), c_0_71])])).
% 3.27/3.45  cnf(c_0_80, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))|~r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))|~r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_44]), c_0_76])])).
% 3.27/3.45  cnf(c_0_81, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)))|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_relat_1(X3))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_64]), c_0_65]), c_0_26]), c_0_25])])).
% 3.27/3.45  cnf(c_0_82, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.27/3.45  cnf(c_0_83, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_24]), c_0_26])])).
% 3.27/3.45  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))|r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_79])).
% 3.27/3.45  cnf(c_0_85, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))|~r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_71]), c_0_76])])).
% 3.27/3.45  cnf(c_0_86, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_71])])).
% 3.27/3.45  cnf(c_0_87, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 3.27/3.45  cnf(c_0_88, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 3.27/3.45  cnf(c_0_89, negated_conjecture, (~r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_51])).
% 3.27/3.45  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_57]), c_0_71])]), ['proof']).
% 3.27/3.45  # SZS output end CNFRefutation
% 3.27/3.45  # Proof object total steps             : 91
% 3.27/3.45  # Proof object clause steps            : 62
% 3.27/3.45  # Proof object formula steps           : 29
% 3.27/3.45  # Proof object conjectures             : 21
% 3.27/3.45  # Proof object clause conjectures      : 18
% 3.27/3.45  # Proof object formula conjectures     : 3
% 3.27/3.45  # Proof object initial clauses used    : 23
% 3.27/3.45  # Proof object initial formulas used   : 14
% 3.27/3.45  # Proof object generating inferences   : 24
% 3.27/3.45  # Proof object simplifying inferences  : 70
% 3.27/3.45  # Training examples: 0 positive, 0 negative
% 3.27/3.45  # Parsed axioms                        : 14
% 3.27/3.45  # Removed by relevancy pruning/SinE    : 0
% 3.27/3.45  # Initial clauses                      : 25
% 3.27/3.45  # Removed in clause preprocessing      : 3
% 3.27/3.45  # Initial clauses in saturation        : 22
% 3.27/3.45  # Processed clauses                    : 4776
% 3.27/3.45  # ...of these trivial                  : 13
% 3.27/3.45  # ...subsumed                          : 2056
% 3.27/3.45  # ...remaining for further processing  : 2707
% 3.27/3.45  # Other redundant clauses eliminated   : 688
% 3.27/3.45  # Clauses deleted for lack of memory   : 0
% 3.27/3.45  # Backward-subsumed                    : 572
% 3.27/3.45  # Backward-rewritten                   : 585
% 3.27/3.45  # Generated clauses                    : 216667
% 3.27/3.45  # ...of the previous two non-trivial   : 208390
% 3.27/3.45  # Contextual simplify-reflections      : 81
% 3.27/3.45  # Paramodulations                      : 215753
% 3.27/3.45  # Factorizations                       : 218
% 3.27/3.45  # Equation resolutions                 : 688
% 3.27/3.45  # Propositional unsat checks           : 0
% 3.27/3.45  #    Propositional check models        : 0
% 3.27/3.45  #    Propositional check unsatisfiable : 0
% 3.27/3.45  #    Propositional clauses             : 0
% 3.27/3.45  #    Propositional clauses after purity: 0
% 3.27/3.45  #    Propositional unsat core size     : 0
% 3.27/3.45  #    Propositional preprocessing time  : 0.000
% 3.27/3.45  #    Propositional encoding time       : 0.000
% 3.27/3.45  #    Propositional solver time         : 0.000
% 3.27/3.45  #    Success case prop preproc time    : 0.000
% 3.27/3.45  #    Success case prop encoding time   : 0.000
% 3.27/3.45  #    Success case prop solver time     : 0.000
% 3.27/3.45  # Current number of processed clauses  : 1517
% 3.27/3.45  #    Positive orientable unit clauses  : 44
% 3.27/3.45  #    Positive unorientable unit clauses: 1
% 3.27/3.45  #    Negative unit clauses             : 8
% 3.27/3.45  #    Non-unit-clauses                  : 1464
% 3.27/3.45  # Current number of unprocessed clauses: 202700
% 3.27/3.45  # ...number of literals in the above   : 1259387
% 3.27/3.45  # Current number of archived formulas  : 0
% 3.27/3.45  # Current number of archived clauses   : 1190
% 3.27/3.45  # Clause-clause subsumption calls (NU) : 927325
% 3.27/3.45  # Rec. Clause-clause subsumption calls : 442679
% 3.27/3.45  # Non-unit clause-clause subsumptions  : 2447
% 3.27/3.45  # Unit Clause-clause subsumption calls : 18615
% 3.27/3.45  # Rewrite failures with RHS unbound    : 0
% 3.27/3.45  # BW rewrite match attempts            : 1630
% 3.27/3.45  # BW rewrite match successes           : 96
% 3.27/3.45  # Condensation attempts                : 0
% 3.27/3.45  # Condensation successes               : 0
% 3.27/3.45  # Termbank termtop insertions          : 7558233
% 3.27/3.46  
% 3.27/3.46  # -------------------------------------------------
% 3.27/3.46  # User time                : 3.018 s
% 3.27/3.46  # System time              : 0.097 s
% 3.27/3.46  # Total time               : 3.116 s
% 3.27/3.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
