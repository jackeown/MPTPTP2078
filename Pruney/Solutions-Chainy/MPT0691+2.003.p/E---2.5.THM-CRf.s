%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:41 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 480 expanded)
%              Number of clauses        :   53 ( 213 expanded)
%              Number of leaves         :   16 ( 122 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 926 expanded)
%              Number of equality atoms :   69 ( 314 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

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

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_16,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | ~ r1_tarski(k1_relat_1(X48),X47)
      | k5_relat_1(k6_relat_1(X47),X48) = X48 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_17,plain,(
    ! [X46] :
      ( k1_relat_1(k6_relat_1(X46)) = X46
      & k2_relat_1(k6_relat_1(X46)) = X46 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_18,plain,(
    ! [X53] :
      ( v1_relat_1(k6_relat_1(X53))
      & v1_funct_1(k6_relat_1(X53)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_20,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X44)
      | ~ v1_relat_1(X45)
      | k1_relat_1(k5_relat_1(X44,X45)) = k10_relat_1(X44,k1_relat_1(X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_21,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | k7_relat_1(X52,X51) = k5_relat_1(k6_relat_1(X51),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_22,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_26,plain,(
    ! [X57,X58,X59] :
      ( ~ v1_relat_1(X59)
      | k10_relat_1(k7_relat_1(X59,X57),X58) = k3_xboole_0(X57,k10_relat_1(X59,X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_27,plain,(
    ! [X30,X31] : k1_setfam_1(k2_tarski(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_28,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X42)
      | ~ v1_relat_1(X43)
      | k10_relat_1(k5_relat_1(X42,X43),X41) = k10_relat_1(X42,k10_relat_1(X43,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

cnf(c_0_29,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k10_relat_1(X40,k2_relat_1(X40)) = k1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_36,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_23])).

cnf(c_0_39,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk2_0)),k6_relat_1(esk1_0)) = k6_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_41,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k10_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk2_0) = k7_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk2_0)) = k10_relat_1(X1,k1_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

fof(c_0_47,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | v1_relat_1(k7_relat_1(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_48,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0)) = k6_relat_1(esk1_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2))) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( k10_relat_1(k6_relat_1(X1),k10_relat_1(esk2_0,X2)) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k10_relat_1(k6_relat_1(X1),k1_relat_1(esk2_0)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_45])).

fof(c_0_55,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(X36,X37)
      | k9_relat_1(k7_relat_1(X35,X37),X36) = k9_relat_1(X35,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_56,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_57,plain,(
    ! [X34] :
      ( ~ v1_relat_1(X34)
      | k9_relat_1(X34,k1_relat_1(X34)) = k2_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_58,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k2_tarski(X1,k10_relat_1(k6_relat_1(X2),X3))) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k1_relat_1(esk2_0)),esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_23])).

cnf(c_0_61,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_39])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_50])).

fof(c_0_63,plain,(
    ! [X26,X27] : k2_tarski(X26,X27) = k2_tarski(X27,X26) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_64,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k1_relat_1(esk2_0))) = k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_54])).

cnf(c_0_66,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk2_0)),X1),esk1_0) = k1_setfam_1(k2_tarski(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k1_relat_1(esk2_0))) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),X2) = k9_relat_1(esk2_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_37])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_67,c_0_34])).

cnf(c_0_76,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1))) = k2_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_60]),c_0_72]),c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),X1) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_62])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1))) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,esk1_0)) = k9_relat_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_51])).

cnf(c_0_83,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:34:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.43/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.43/0.61  # and selection function SelectDivPreferIntoLits.
% 0.43/0.61  #
% 0.43/0.61  # Preprocessing time       : 0.028 s
% 0.43/0.61  # Presaturation interreduction done
% 0.43/0.61  
% 0.43/0.61  # Proof found!
% 0.43/0.61  # SZS status Theorem
% 0.43/0.61  # SZS output start CNFRefutation
% 0.43/0.61  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.43/0.61  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.43/0.61  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.43/0.61  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.43/0.61  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.43/0.61  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.43/0.61  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.43/0.61  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.43/0.61  fof(t181_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k10_relat_1(k5_relat_1(X2,X3),X1)=k10_relat_1(X2,k10_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 0.43/0.61  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.43/0.61  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.43/0.61  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.43/0.61  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.43/0.61  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.43/0.61  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.43/0.61  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.43/0.61  fof(c_0_16, plain, ![X47, X48]:(~v1_relat_1(X48)|(~r1_tarski(k1_relat_1(X48),X47)|k5_relat_1(k6_relat_1(X47),X48)=X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.43/0.61  fof(c_0_17, plain, ![X46]:(k1_relat_1(k6_relat_1(X46))=X46&k2_relat_1(k6_relat_1(X46))=X46), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.43/0.61  fof(c_0_18, plain, ![X53]:(v1_relat_1(k6_relat_1(X53))&v1_funct_1(k6_relat_1(X53))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.43/0.61  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.43/0.61  fof(c_0_20, plain, ![X44, X45]:(~v1_relat_1(X44)|(~v1_relat_1(X45)|k1_relat_1(k5_relat_1(X44,X45))=k10_relat_1(X44,k1_relat_1(X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.43/0.61  fof(c_0_21, plain, ![X51, X52]:(~v1_relat_1(X52)|k7_relat_1(X52,X51)=k5_relat_1(k6_relat_1(X51),X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.43/0.61  cnf(c_0_22, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.43/0.61  cnf(c_0_23, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.43/0.61  cnf(c_0_24, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.43/0.61  fof(c_0_25, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.43/0.61  fof(c_0_26, plain, ![X57, X58, X59]:(~v1_relat_1(X59)|k10_relat_1(k7_relat_1(X59,X57),X58)=k3_xboole_0(X57,k10_relat_1(X59,X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.43/0.61  fof(c_0_27, plain, ![X30, X31]:k1_setfam_1(k2_tarski(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.43/0.61  fof(c_0_28, plain, ![X41, X42, X43]:(~v1_relat_1(X42)|(~v1_relat_1(X43)|k10_relat_1(k5_relat_1(X42,X43),X41)=k10_relat_1(X42,k10_relat_1(X43,X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).
% 0.43/0.61  cnf(c_0_29, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.43/0.61  cnf(c_0_30, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.43/0.61  cnf(c_0_31, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.43/0.61  cnf(c_0_32, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.43/0.61  cnf(c_0_33, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.43/0.61  cnf(c_0_34, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.61  fof(c_0_35, plain, ![X40]:(~v1_relat_1(X40)|k10_relat_1(X40,k2_relat_1(X40))=k1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.43/0.61  cnf(c_0_36, plain, (k10_relat_1(k5_relat_1(X1,X2),X3)=k10_relat_1(X1,k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.43/0.61  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.43/0.61  cnf(c_0_38, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_23])).
% 0.43/0.61  cnf(c_0_39, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_24])).
% 0.43/0.61  cnf(c_0_40, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk2_0)),k6_relat_1(esk1_0))=k6_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.43/0.61  fof(c_0_41, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.43/0.61  cnf(c_0_42, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.43/0.61  cnf(c_0_43, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.43/0.61  cnf(c_0_44, plain, (k10_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k10_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_36, c_0_24])).
% 0.43/0.61  cnf(c_0_45, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk2_0)=k7_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.43/0.61  cnf(c_0_46, negated_conjecture, (k1_relat_1(k5_relat_1(X1,esk2_0))=k10_relat_1(X1,k1_relat_1(esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_37])).
% 0.43/0.61  fof(c_0_47, plain, ![X32, X33]:(~v1_relat_1(X32)|v1_relat_1(k7_relat_1(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.43/0.61  cnf(c_0_48, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k10_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_24]), c_0_39])).
% 0.43/0.61  cnf(c_0_49, negated_conjecture, (k7_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk2_0))=k6_relat_1(esk1_0)), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 0.43/0.61  cnf(c_0_50, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.43/0.61  cnf(c_0_51, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2)))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 0.43/0.61  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_37])).
% 0.43/0.61  cnf(c_0_53, negated_conjecture, (k10_relat_1(k6_relat_1(X1),k10_relat_1(esk2_0,X2))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_45])).
% 0.43/0.61  cnf(c_0_54, negated_conjecture, (k10_relat_1(k6_relat_1(X1),k1_relat_1(esk2_0))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_24]), c_0_45])).
% 0.43/0.61  fof(c_0_55, plain, ![X35, X36, X37]:(~v1_relat_1(X35)|(~r1_tarski(X36,X37)|k9_relat_1(k7_relat_1(X35,X37),X36)=k9_relat_1(X35,X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.43/0.61  fof(c_0_56, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.43/0.61  fof(c_0_57, plain, ![X34]:(~v1_relat_1(X34)|k9_relat_1(X34,k1_relat_1(X34))=k2_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.43/0.61  cnf(c_0_58, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.43/0.61  cnf(c_0_59, plain, (k1_setfam_1(k2_tarski(X1,k10_relat_1(k6_relat_1(X2),X3)))=k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3)), inference(spm,[status(thm)],[c_0_42, c_0_24])).
% 0.43/0.61  cnf(c_0_60, negated_conjecture, (k10_relat_1(k6_relat_1(k1_relat_1(esk2_0)),esk1_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_23])).
% 0.43/0.61  cnf(c_0_61, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_39])).
% 0.43/0.61  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_50])).
% 0.43/0.61  fof(c_0_63, plain, ![X26, X27]:k2_tarski(X26,X27)=k2_tarski(X27,X26), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.43/0.61  cnf(c_0_64, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k1_relat_1(esk2_0)))=k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.43/0.61  cnf(c_0_65, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_54])).
% 0.43/0.61  cnf(c_0_66, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.43/0.61  cnf(c_0_67, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.43/0.61  cnf(c_0_68, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.43/0.61  cnf(c_0_69, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_58, c_0_37])).
% 0.43/0.61  cnf(c_0_70, negated_conjecture, (k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk2_0)),X1),esk1_0)=k1_setfam_1(k2_tarski(X1,esk1_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.43/0.61  cnf(c_0_71, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.43/0.61  cnf(c_0_72, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.43/0.61  cnf(c_0_73, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k1_relat_1(esk2_0)))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.43/0.61  cnf(c_0_74, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),X2)=k9_relat_1(esk2_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_66, c_0_37])).
% 0.43/0.61  cnf(c_0_75, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_67, c_0_34])).
% 0.43/0.61  cnf(c_0_76, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1)))=k2_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.43/0.61  cnf(c_0_77, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_60]), c_0_72]), c_0_73])).
% 0.43/0.61  cnf(c_0_78, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),X1)=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_62])).
% 0.43/0.61  cnf(c_0_79, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_75, c_0_72])).
% 0.43/0.61  cnf(c_0_80, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1)))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_43, c_0_69])).
% 0.43/0.61  cnf(c_0_81, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,esk1_0))=k9_relat_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.43/0.61  cnf(c_0_82, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_79, c_0_51])).
% 0.43/0.61  cnf(c_0_83, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_77])).
% 0.43/0.61  cnf(c_0_84, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.43/0.61  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), ['proof']).
% 0.43/0.61  # SZS output end CNFRefutation
% 0.43/0.61  # Proof object total steps             : 86
% 0.43/0.61  # Proof object clause steps            : 53
% 0.43/0.61  # Proof object formula steps           : 33
% 0.43/0.61  # Proof object conjectures             : 29
% 0.43/0.61  # Proof object clause conjectures      : 26
% 0.43/0.61  # Proof object formula conjectures     : 3
% 0.43/0.61  # Proof object initial clauses used    : 18
% 0.43/0.61  # Proof object initial formulas used   : 16
% 0.43/0.61  # Proof object generating inferences   : 29
% 0.43/0.61  # Proof object simplifying inferences  : 20
% 0.43/0.61  # Training examples: 0 positive, 0 negative
% 0.43/0.61  # Parsed axioms                        : 29
% 0.43/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.61  # Initial clauses                      : 35
% 0.43/0.61  # Removed in clause preprocessing      : 2
% 0.43/0.61  # Initial clauses in saturation        : 33
% 0.43/0.61  # Processed clauses                    : 2315
% 0.43/0.61  # ...of these trivial                  : 401
% 0.43/0.61  # ...subsumed                          : 1071
% 0.43/0.61  # ...remaining for further processing  : 843
% 0.43/0.61  # Other redundant clauses eliminated   : 2
% 0.43/0.61  # Clauses deleted for lack of memory   : 0
% 0.43/0.61  # Backward-subsumed                    : 39
% 0.43/0.61  # Backward-rewritten                   : 116
% 0.43/0.61  # Generated clauses                    : 27765
% 0.43/0.61  # ...of the previous two non-trivial   : 21530
% 0.43/0.61  # Contextual simplify-reflections      : 0
% 0.43/0.61  # Paramodulations                      : 27763
% 0.43/0.61  # Factorizations                       : 0
% 0.43/0.61  # Equation resolutions                 : 2
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
% 0.43/0.61  # Current number of processed clauses  : 654
% 0.43/0.61  #    Positive orientable unit clauses  : 374
% 0.43/0.61  #    Positive unorientable unit clauses: 2
% 0.43/0.61  #    Negative unit clauses             : 1
% 0.43/0.61  #    Non-unit-clauses                  : 277
% 0.43/0.61  # Current number of unprocessed clauses: 19142
% 0.43/0.61  # ...number of literals in the above   : 20093
% 0.43/0.61  # Current number of archived formulas  : 0
% 0.43/0.61  # Current number of archived clauses   : 189
% 0.43/0.61  # Clause-clause subsumption calls (NU) : 13385
% 0.43/0.61  # Rec. Clause-clause subsumption calls : 13193
% 0.43/0.61  # Non-unit clause-clause subsumptions  : 1109
% 0.43/0.61  # Unit Clause-clause subsumption calls : 648
% 0.43/0.61  # Rewrite failures with RHS unbound    : 0
% 0.43/0.61  # BW rewrite match attempts            : 1951
% 0.43/0.61  # BW rewrite match successes           : 80
% 0.43/0.61  # Condensation attempts                : 0
% 0.43/0.61  # Condensation successes               : 0
% 0.43/0.61  # Termbank termtop insertions          : 355678
% 0.43/0.62  
% 0.43/0.62  # -------------------------------------------------
% 0.43/0.62  # User time                : 0.261 s
% 0.43/0.62  # System time              : 0.011 s
% 0.43/0.62  # Total time               : 0.272 s
% 0.43/0.62  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
