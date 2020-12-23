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
% DateTime   : Thu Dec  3 10:54:37 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 378 expanded)
%              Number of clauses        :   43 ( 168 expanded)
%              Number of leaves         :   17 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 747 expanded)
%              Number of equality atoms :   72 ( 314 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(t142_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t111_relat_1,axiom,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t171_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t52_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(t51_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(t174_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(c_0_17,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | v1_relat_1(k7_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_18,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k7_relat_1(X30,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
        <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_1])).

cnf(c_0_20,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ( ~ r2_hidden(esk2_0,k2_relat_1(esk3_0))
      | k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k1_xboole_0 )
    & ( r2_hidden(esk2_0,k2_relat_1(esk3_0))
      | k10_relat_1(esk3_0,k1_tarski(esk2_0)) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_23,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | r1_tarski(k1_relat_1(k7_relat_1(X38,X37)),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_24,plain,(
    ! [X31] : k7_relat_1(k1_xboole_0,X31) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t111_relat_1])).

cnf(c_0_25,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k10_relat_1(X33,X32) = k10_relat_1(X33,k3_xboole_0(k2_relat_1(X33),X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_28,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_29,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(X26,k1_tarski(X27)) != X26
        | ~ r2_hidden(X27,X26) )
      & ( r2_hidden(X27,X26)
        | k4_xboole_0(X26,k1_tarski(X27)) = X26 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_35,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k1_xboole_0
    | ~ r2_hidden(esk2_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X18,X19] : k4_xboole_0(k2_xboole_0(X18,X19),X19) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk3_0),k1_tarski(esk2_0)) = k2_relat_1(esk3_0)
    | k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(esk3_0,k4_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk3_0))) = k10_relat_1(esk3_0,k1_tarski(esk2_0))
    | k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26])])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k10_relat_1(esk3_0,k1_xboole_0)
    | k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_52,plain,(
    ! [X34] :
      ( ~ v1_relat_1(X34)
      | k10_relat_1(X34,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_relat_1])])).

fof(c_0_53,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_54,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | k3_xboole_0(X25,k1_tarski(X24)) = k1_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k1_xboole_0
    | k10_relat_1(esk3_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_57,plain,(
    ! [X22,X23] :
      ( k3_xboole_0(X22,k1_tarski(X23)) != k1_tarski(X23)
      | r2_hidden(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | X35 = k1_xboole_0
      | ~ r1_tarski(X35,k2_relat_1(X36))
      | k10_relat_1(X36,X35) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relat_1(esk3_0))
    | k10_relat_1(esk3_0,k1_tarski(esk2_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_26])])).

cnf(c_0_63,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_37])).

cnf(c_0_65,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | k10_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X2,k4_xboole_0(X2,k1_tarski(X1))) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_68,plain,
    ( r2_hidden(X2,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X2))) != k1_tarski(X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_37])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_64])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2)) = k1_xboole_0
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_44]),c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk3_0),k4_xboole_0(k2_relat_1(esk3_0),k1_tarski(esk2_0))) = k1_tarski(esk2_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),X2)))
    | k4_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),X2)),k1_xboole_0) != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k1_tarski(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_62]),c_0_71]),c_0_26])])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_48])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48])]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:55:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.21/0.38  # and selection function SelectNewComplexAHP.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.38  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 0.21/0.38  fof(t142_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 0.21/0.38  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.21/0.38  fof(t111_relat_1, axiom, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 0.21/0.38  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.21/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.38  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.21/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.38  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.21/0.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.21/0.38  fof(t171_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 0.21/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.21/0.38  fof(t52_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 0.21/0.38  fof(t51_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 0.21/0.38  fof(t174_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 0.21/0.38  fof(c_0_17, plain, ![X28, X29]:(~v1_relat_1(X28)|v1_relat_1(k7_relat_1(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.38  fof(c_0_18, plain, ![X30]:(~v1_relat_1(X30)|k7_relat_1(X30,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 0.21/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t142_funct_1])).
% 0.21/0.38  cnf(c_0_20, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  cnf(c_0_21, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  fof(c_0_22, negated_conjecture, (v1_relat_1(esk3_0)&((~r2_hidden(esk2_0,k2_relat_1(esk3_0))|k10_relat_1(esk3_0,k1_tarski(esk2_0))=k1_xboole_0)&(r2_hidden(esk2_0,k2_relat_1(esk3_0))|k10_relat_1(esk3_0,k1_tarski(esk2_0))!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.21/0.38  fof(c_0_23, plain, ![X37, X38]:(~v1_relat_1(X38)|r1_tarski(k1_relat_1(k7_relat_1(X38,X37)),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.21/0.38  fof(c_0_24, plain, ![X31]:k7_relat_1(k1_xboole_0,X31)=k1_xboole_0, inference(variable_rename,[status(thm)],[t111_relat_1])).
% 0.21/0.38  cnf(c_0_25, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  fof(c_0_27, plain, ![X32, X33]:(~v1_relat_1(X33)|k10_relat_1(X33,X32)=k10_relat_1(X33,k3_xboole_0(k2_relat_1(X33),X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.21/0.38  fof(c_0_28, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.38  fof(c_0_29, plain, ![X26, X27]:((k4_xboole_0(X26,k1_tarski(X27))!=X26|~r2_hidden(X27,X26))&(r2_hidden(X27,X26)|k4_xboole_0(X26,k1_tarski(X27))=X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.21/0.38  fof(c_0_30, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.38  cnf(c_0_31, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_32, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.38  cnf(c_0_33, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.38  fof(c_0_35, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.21/0.38  cnf(c_0_36, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk3_0,k1_tarski(esk2_0))=k1_xboole_0|~r2_hidden(esk2_0,k2_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_39, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.38  fof(c_0_40, plain, ![X18, X19]:k4_xboole_0(k2_xboole_0(X18,X19),X19)=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.21/0.38  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.38  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.21/0.38  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.38  cnf(c_0_44, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k2_relat_1(esk3_0),k1_tarski(esk2_0))=k2_relat_1(esk3_0)|k10_relat_1(esk3_0,k1_tarski(esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.38  cnf(c_0_46, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.38  cnf(c_0_47, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.38  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (k10_relat_1(esk3_0,k4_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk3_0)))=k10_relat_1(esk3_0,k1_tarski(esk2_0))|k10_relat_1(esk3_0,k1_tarski(esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26])])).
% 0.21/0.38  cnf(c_0_50, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.21/0.38  cnf(c_0_51, negated_conjecture, (k10_relat_1(esk3_0,k1_tarski(esk2_0))=k10_relat_1(esk3_0,k1_xboole_0)|k10_relat_1(esk3_0,k1_tarski(esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.38  fof(c_0_52, plain, ![X34]:(~v1_relat_1(X34)|k10_relat_1(X34,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_relat_1])])).
% 0.21/0.38  fof(c_0_53, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.21/0.38  fof(c_0_54, plain, ![X24, X25]:(~r2_hidden(X24,X25)|k3_xboole_0(X25,k1_tarski(X24))=k1_tarski(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (k10_relat_1(esk3_0,k1_tarski(esk2_0))=k1_xboole_0|k10_relat_1(esk3_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_51])).
% 0.21/0.38  cnf(c_0_56, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.38  fof(c_0_57, plain, ![X22, X23]:(k3_xboole_0(X22,k1_tarski(X23))!=k1_tarski(X23)|r2_hidden(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).
% 0.21/0.38  cnf(c_0_58, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.38  fof(c_0_59, plain, ![X35, X36]:(~v1_relat_1(X36)|(X35=k1_xboole_0|~r1_tarski(X35,k2_relat_1(X36))|k10_relat_1(X36,X35)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).
% 0.21/0.38  cnf(c_0_60, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_0,k2_relat_1(esk3_0))|k10_relat_1(esk3_0,k1_tarski(esk2_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_62, negated_conjecture, (k10_relat_1(esk3_0,k1_tarski(esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_26])])).
% 0.21/0.38  cnf(c_0_63, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.38  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_58, c_0_37])).
% 0.21/0.38  cnf(c_0_65, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k2_relat_1(X1))|k10_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.38  cnf(c_0_66, plain, (k4_xboole_0(X2,k4_xboole_0(X2,k1_tarski(X1)))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_60, c_0_37])).
% 0.21/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_0,k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.21/0.38  cnf(c_0_68, plain, (r2_hidden(X2,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X2)))!=k1_tarski(X2)), inference(rw,[status(thm)],[c_0_63, c_0_37])).
% 0.21/0.38  cnf(c_0_69, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_64])).
% 0.21/0.38  cnf(c_0_70, plain, (k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2))=k1_xboole_0|k10_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_44]), c_0_64])])).
% 0.21/0.38  cnf(c_0_71, negated_conjecture, (k4_xboole_0(k2_relat_1(esk3_0),k4_xboole_0(k2_relat_1(esk3_0),k1_tarski(esk2_0)))=k1_tarski(esk2_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.38  cnf(c_0_72, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.38  cnf(c_0_73, plain, (r2_hidden(X1,k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),X2)))|k4_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),X2)),k1_xboole_0)!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.38  cnf(c_0_74, negated_conjecture, (k1_tarski(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_62]), c_0_71]), c_0_26])])).
% 0.21/0.38  cnf(c_0_75, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_48])).
% 0.21/0.38  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48])]), c_0_75]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 77
% 0.21/0.38  # Proof object clause steps            : 43
% 0.21/0.38  # Proof object formula steps           : 34
% 0.21/0.38  # Proof object conjectures             : 16
% 0.21/0.38  # Proof object clause conjectures      : 13
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 20
% 0.21/0.38  # Proof object initial formulas used   : 17
% 0.21/0.38  # Proof object generating inferences   : 17
% 0.21/0.38  # Proof object simplifying inferences  : 27
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 20
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 27
% 0.21/0.38  # Removed in clause preprocessing      : 1
% 0.21/0.38  # Initial clauses in saturation        : 26
% 0.21/0.38  # Processed clauses                    : 198
% 0.21/0.38  # ...of these trivial                  : 14
% 0.21/0.38  # ...subsumed                          : 64
% 0.21/0.38  # ...remaining for further processing  : 120
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 1
% 0.21/0.38  # Backward-rewritten                   : 22
% 0.21/0.38  # Generated clauses                    : 933
% 0.21/0.38  # ...of the previous two non-trivial   : 653
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 930
% 0.21/0.38  # Factorizations                       : 3
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 97
% 0.21/0.38  #    Positive orientable unit clauses  : 31
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 65
% 0.21/0.38  # Current number of unprocessed clauses: 465
% 0.21/0.38  # ...number of literals in the above   : 1106
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 24
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 328
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 305
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 26
% 0.21/0.38  # Unit Clause-clause subsumption calls : 68
% 0.21/0.38  # Rewrite failures with RHS unbound    : 2
% 0.21/0.38  # BW rewrite match attempts            : 46
% 0.21/0.38  # BW rewrite match successes           : 7
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 13826
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.041 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.045 s
% 0.21/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
