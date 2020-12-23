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
% DateTime   : Thu Dec  3 10:48:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 484 expanded)
%              Number of clauses        :   46 ( 215 expanded)
%              Number of leaves         :   17 ( 132 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 ( 767 expanded)
%              Number of equality atoms :   25 ( 309 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_17,plain,(
    ! [X40,X41] : k1_setfam_1(k2_tarski(X40,X41)) = k3_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X35,X36,X37,X38] : k3_enumset1(X35,X35,X36,X37,X38) = k2_enumset1(X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X42,X43] :
      ( ( ~ m1_subset_1(X42,k1_zfmisc_1(X43))
        | r1_tarski(X42,X43) )
      & ( ~ r1_tarski(X42,X43)
        | m1_subset_1(X42,k1_zfmisc_1(X43)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_25,plain,(
    ! [X39] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X29] : r1_xboole_0(X29,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_31,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_37,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k3_xboole_0(X24,X25)) = X24 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X26,X27,X28] : r1_tarski(k2_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)),k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_xboole_0(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X3))),k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_51,plain,(
    ! [X19,X20] : r1_tarski(k3_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_53,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(X47))
      | v1_relat_1(X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_48]),c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_57,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X49)
      | ~ v1_relat_1(X50)
      | ~ r1_tarski(X49,X50)
      | r1_tarski(k3_relat_1(X49),k3_relat_1(X50)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_58,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

cnf(c_0_59,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_27]),c_0_28]),c_0_29])).

fof(c_0_62,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X21,X23)
      | r1_tarski(X21,k3_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_61])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_66])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0))),k3_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_55])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0))),k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k3_relat_1(esk4_0))))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0))),X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1))),k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_61])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k3_enumset1(k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.41  # and selection function SelectNegativeLiterals.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.028 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.41  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.41  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.13/0.41  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.13/0.41  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.13/0.41  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 0.13/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.41  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.13/0.41  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.13/0.41  fof(c_0_17, plain, ![X40, X41]:k1_setfam_1(k2_tarski(X40,X41))=k3_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.41  fof(c_0_18, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.41  fof(c_0_19, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.41  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.41  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.41  fof(c_0_22, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.41  fof(c_0_23, plain, ![X35, X36, X37, X38]:k3_enumset1(X35,X35,X36,X37,X38)=k2_enumset1(X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.41  fof(c_0_24, plain, ![X42, X43]:((~m1_subset_1(X42,k1_zfmisc_1(X43))|r1_tarski(X42,X43))&(~r1_tarski(X42,X43)|m1_subset_1(X42,k1_zfmisc_1(X43)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.41  fof(c_0_25, plain, ![X39]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.41  cnf(c_0_26, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.41  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.41  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  fof(c_0_30, plain, ![X29]:r1_xboole_0(X29,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.41  fof(c_0_31, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.41  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.41  cnf(c_0_33, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.41  cnf(c_0_34, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.41  cnf(c_0_35, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.41  fof(c_0_36, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.41  fof(c_0_37, plain, ![X24, X25]:k2_xboole_0(X24,k3_xboole_0(X24,X25))=X24, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.13/0.41  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.41  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.41  cnf(c_0_40, plain, (~r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.41  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.41  fof(c_0_42, plain, ![X26, X27, X28]:r1_tarski(k2_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)),k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.13/0.41  cnf(c_0_43, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_44, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.41  cnf(c_0_45, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.41  cnf(c_0_46, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.41  cnf(c_0_47, plain, (k2_xboole_0(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.41  cnf(c_0_48, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.41  cnf(c_0_49, plain, (r1_tarski(k2_xboole_0(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X3))),k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.13/0.41  cnf(c_0_50, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.41  fof(c_0_51, plain, ![X19, X20]:r1_tarski(k3_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.13/0.41  fof(c_0_52, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.13/0.41  fof(c_0_53, plain, ![X47, X48]:(~v1_relat_1(X47)|(~m1_subset_1(X48,k1_zfmisc_1(X47))|v1_relat_1(X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.41  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.41  cnf(c_0_55, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_48]), c_0_50])).
% 0.13/0.41  cnf(c_0_56, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.41  fof(c_0_57, plain, ![X49, X50]:(~v1_relat_1(X49)|(~v1_relat_1(X50)|(~r1_tarski(X49,X50)|r1_tarski(k3_relat_1(X49),k3_relat_1(X50))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.13/0.41  fof(c_0_58, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 0.13/0.41  cnf(c_0_59, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.41  cnf(c_0_60, plain, (m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.41  cnf(c_0_61, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.41  fof(c_0_62, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_tarski(X21,X23)|r1_tarski(X21,k3_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.13/0.41  cnf(c_0_63, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.41  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.41  cnf(c_0_65, plain, (v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.41  cnf(c_0_66, plain, (m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_61])).
% 0.13/0.41  cnf(c_0_67, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.41  cnf(c_0_68, negated_conjecture, (r1_tarski(k3_relat_1(X1),k3_relat_1(esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.41  cnf(c_0_69, negated_conjecture, (v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0)))), inference(spm,[status(thm)],[c_0_65, c_0_64])).
% 0.13/0.41  cnf(c_0_70, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.41  cnf(c_0_71, plain, (v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_59, c_0_66])).
% 0.13/0.41  cnf(c_0_72, plain, (r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.41  cnf(c_0_73, negated_conjecture, (r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0))),k3_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_55])])).
% 0.13/0.41  cnf(c_0_74, negated_conjecture, (r1_tarski(k3_relat_1(X1),k3_relat_1(esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_70])).
% 0.13/0.41  cnf(c_0_75, negated_conjecture, (v1_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))), inference(spm,[status(thm)],[c_0_71, c_0_70])).
% 0.13/0.41  cnf(c_0_76, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.41  cnf(c_0_77, negated_conjecture, (r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0))),k1_setfam_1(k3_enumset1(X2,X2,X2,X2,k3_relat_1(esk4_0))))|~r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,esk4_0))),X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.41  cnf(c_0_78, negated_conjecture, (r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1))),k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_61])])).
% 0.13/0.41  cnf(c_0_79, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k3_enumset1(k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.13/0.41  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 81
% 0.13/0.41  # Proof object clause steps            : 46
% 0.13/0.41  # Proof object formula steps           : 35
% 0.13/0.41  # Proof object conjectures             : 15
% 0.13/0.41  # Proof object clause conjectures      : 12
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 20
% 0.13/0.41  # Proof object initial formulas used   : 17
% 0.13/0.41  # Proof object generating inferences   : 19
% 0.13/0.41  # Proof object simplifying inferences  : 32
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 18
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 26
% 0.13/0.41  # Removed in clause preprocessing      : 4
% 0.13/0.41  # Initial clauses in saturation        : 22
% 0.13/0.41  # Processed clauses                    : 369
% 0.13/0.41  # ...of these trivial                  : 5
% 0.13/0.41  # ...subsumed                          : 122
% 0.13/0.41  # ...remaining for further processing  : 242
% 0.13/0.41  # Other redundant clauses eliminated   : 2
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 0
% 0.13/0.41  # Backward-rewritten                   : 12
% 0.13/0.41  # Generated clauses                    : 1311
% 0.13/0.41  # ...of the previous two non-trivial   : 1095
% 0.13/0.41  # Contextual simplify-reflections      : 0
% 0.13/0.41  # Paramodulations                      : 1309
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 2
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 207
% 0.13/0.41  #    Positive orientable unit clauses  : 71
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 2
% 0.13/0.41  #    Non-unit-clauses                  : 134
% 0.13/0.41  # Current number of unprocessed clauses: 747
% 0.13/0.41  # ...number of literals in the above   : 1323
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 37
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 1781
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 1723
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 118
% 0.13/0.41  # Unit Clause-clause subsumption calls : 102
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 438
% 0.13/0.41  # BW rewrite match successes           : 8
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 37177
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.055 s
% 0.13/0.41  # System time              : 0.006 s
% 0.13/0.41  # Total time               : 0.062 s
% 0.13/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
