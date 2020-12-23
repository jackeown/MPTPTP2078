%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:48 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 639 expanded)
%              Number of clauses        :   48 ( 285 expanded)
%              Number of leaves         :   16 ( 170 expanded)
%              Depth                    :   16
%              Number of atoms          :  145 ( 928 expanded)
%              Number of equality atoms :   57 ( 535 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t2_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
         => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_16,plain,(
    ! [X36,X37] : k1_setfam_1(k2_tarski(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & v1_zfmisc_1(X1) )
       => ! [X2] :
            ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
           => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t2_tex_2])).

fof(c_0_19,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X34,X35] : k3_tarski(k2_tarski(X34,X35)) = k2_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & v1_zfmisc_1(esk3_0)
    & ~ v1_xboole_0(k3_xboole_0(esk3_0,esk4_0))
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_26,plain,(
    ! [X38,X39] :
      ( v1_xboole_0(X38)
      | v1_xboole_0(X39)
      | ~ v1_zfmisc_1(X39)
      | ~ r1_tarski(X38,X39)
      | X38 = X39 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X27,X28] : k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28)) = X27 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_28]),c_0_29])).

fof(c_0_39,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(X18,k2_xboole_0(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_40,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_28]),c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk3_0
    | v1_xboole_0(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) = esk3_0
    | v1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_51,plain,(
    ! [X23] : k3_xboole_0(X23,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_42]),c_0_29])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_57,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k4_xboole_0(esk3_0,esk4_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_28]),c_0_29])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_62,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_38]),c_0_61])).

cnf(c_0_65,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0
    | v1_xboole_0(k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_63])).

fof(c_0_67,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_61]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0
    | ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0
    | r1_tarski(k4_xboole_0(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0
    | k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_75,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_74])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_74]),c_0_64]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:21:24 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.17/0.36  # and selection function SelectCQIArNpEqFirst.
% 0.17/0.36  #
% 0.17/0.36  # Preprocessing time       : 0.027 s
% 0.17/0.36  # Presaturation interreduction done
% 0.17/0.36  
% 0.17/0.36  # Proof found!
% 0.17/0.36  # SZS status Theorem
% 0.17/0.36  # SZS output start CNFRefutation
% 0.17/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.17/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.36  fof(t2_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 0.17/0.36  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.17/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.17/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.17/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.17/0.36  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.17/0.36  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.17/0.36  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.17/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.17/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.17/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.17/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.17/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.17/0.36  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.17/0.36  fof(c_0_16, plain, ![X36, X37]:k1_setfam_1(k2_tarski(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.17/0.36  fof(c_0_17, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.36  fof(c_0_18, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t2_tex_2])).
% 0.17/0.36  fof(c_0_19, plain, ![X21, X22]:r1_tarski(k3_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.17/0.36  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.36  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.36  fof(c_0_22, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.17/0.36  fof(c_0_23, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.17/0.36  fof(c_0_24, plain, ![X34, X35]:k3_tarski(k2_tarski(X34,X35))=k2_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.17/0.36  fof(c_0_25, negated_conjecture, ((~v1_xboole_0(esk3_0)&v1_zfmisc_1(esk3_0))&(~v1_xboole_0(k3_xboole_0(esk3_0,esk4_0))&~r1_tarski(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.17/0.36  fof(c_0_26, plain, ![X38, X39]:(v1_xboole_0(X38)|(v1_xboole_0(X39)|~v1_zfmisc_1(X39)|(~r1_tarski(X38,X39)|X38=X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.17/0.36  cnf(c_0_27, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.36  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.17/0.36  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.36  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.36  fof(c_0_31, plain, ![X27, X28]:k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))=X27, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.17/0.36  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.36  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_34, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.36  cnf(c_0_35, negated_conjecture, (v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_36, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_37, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.17/0.36  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_28]), c_0_29])).
% 0.17/0.36  fof(c_0_39, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|r1_tarski(X18,k2_xboole_0(X20,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.17/0.36  fof(c_0_40, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.17/0.36  cnf(c_0_41, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.36  cnf(c_0_42, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_21])).
% 0.17/0.36  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_28]), c_0_29])).
% 0.17/0.36  cnf(c_0_44, negated_conjecture, (X1=esk3_0|v1_xboole_0(X1)|~r1_tarski(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.17/0.36  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.36  cnf(c_0_46, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.17/0.36  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.17/0.36  cnf(c_0_48, plain, (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29])).
% 0.17/0.36  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_43, c_0_38])).
% 0.17/0.36  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))=esk3_0|v1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.17/0.36  fof(c_0_51, plain, ![X23]:k3_xboole_0(X23,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.17/0.36  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_42]), c_0_29])).
% 0.17/0.36  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.17/0.36  cnf(c_0_54, plain, (k3_tarski(k2_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_38]), c_0_38]), c_0_38])).
% 0.17/0.36  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.17/0.36  cnf(c_0_56, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.17/0.36  fof(c_0_57, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.17/0.36  cnf(c_0_58, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.17/0.36  cnf(c_0_59, negated_conjecture, (k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k4_xboole_0(esk3_0,esk4_0)))=esk3_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.17/0.36  cnf(c_0_60, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_28]), c_0_29])).
% 0.17/0.36  cnf(c_0_61, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.17/0.36  fof(c_0_62, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.17/0.36  cnf(c_0_63, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.17/0.36  cnf(c_0_64, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_38]), c_0_61])).
% 0.17/0.36  cnf(c_0_65, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.17/0.36  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0|v1_xboole_0(k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_63])).
% 0.17/0.36  fof(c_0_67, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.17/0.36  cnf(c_0_68, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.17/0.36  cnf(c_0_69, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_61]), c_0_64])).
% 0.17/0.36  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0|~r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.17/0.36  cnf(c_0_71, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.17/0.36  cnf(c_0_72, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.17/0.36  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0|r1_tarski(k4_xboole_0(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.17/0.36  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0|k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.17/0.36  fof(c_0_75, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.17/0.36  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(ef,[status(thm)],[c_0_74])).
% 0.17/0.36  cnf(c_0_77, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.17/0.36  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_74]), c_0_64]), c_0_76])).
% 0.17/0.36  cnf(c_0_79, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), ['proof']).
% 0.17/0.36  # SZS output end CNFRefutation
% 0.17/0.36  # Proof object total steps             : 81
% 0.17/0.36  # Proof object clause steps            : 48
% 0.17/0.36  # Proof object formula steps           : 33
% 0.17/0.36  # Proof object conjectures             : 21
% 0.17/0.36  # Proof object clause conjectures      : 18
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 20
% 0.17/0.36  # Proof object initial formulas used   : 16
% 0.17/0.36  # Proof object generating inferences   : 15
% 0.17/0.36  # Proof object simplifying inferences  : 31
% 0.17/0.36  # Training examples: 0 positive, 0 negative
% 0.17/0.36  # Parsed axioms                        : 16
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 25
% 0.17/0.36  # Removed in clause preprocessing      : 4
% 0.17/0.36  # Initial clauses in saturation        : 21
% 0.17/0.36  # Processed clauses                    : 194
% 0.17/0.36  # ...of these trivial                  : 17
% 0.17/0.36  # ...subsumed                          : 75
% 0.17/0.36  # ...remaining for further processing  : 102
% 0.17/0.36  # Other redundant clauses eliminated   : 3
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 14
% 0.17/0.36  # Backward-rewritten                   : 27
% 0.17/0.36  # Generated clauses                    : 344
% 0.17/0.36  # ...of the previous two non-trivial   : 228
% 0.17/0.36  # Contextual simplify-reflections      : 3
% 0.17/0.36  # Paramodulations                      : 340
% 0.17/0.36  # Factorizations                       : 1
% 0.17/0.36  # Equation resolutions                 : 3
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 39
% 0.17/0.36  #    Positive orientable unit clauses  : 16
% 0.17/0.36  #    Positive unorientable unit clauses: 0
% 0.17/0.36  #    Negative unit clauses             : 3
% 0.17/0.36  #    Non-unit-clauses                  : 20
% 0.17/0.36  # Current number of unprocessed clauses: 49
% 0.17/0.36  # ...number of literals in the above   : 99
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 65
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 267
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 235
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 89
% 0.17/0.36  # Unit Clause-clause subsumption calls : 19
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 28
% 0.17/0.36  # BW rewrite match successes           : 8
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 4600
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.032 s
% 0.17/0.36  # System time              : 0.006 s
% 0.17/0.36  # Total time               : 0.038 s
% 0.17/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
