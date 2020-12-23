%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 598 expanded)
%              Number of clauses        :   48 ( 271 expanded)
%              Number of leaves         :   19 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 829 expanded)
%              Number of equality atoms :   37 ( 475 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_19,plain,(
    ! [X41,X42] : k1_setfam_1(k2_tarski(X41,X42)) = k3_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk2_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X25] : r1_tarski(k1_xboole_0,X25) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X29] : k4_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X32,X33] : r1_xboole_0(k4_xboole_0(X32,X33),X33) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_39,plain,(
    ! [X39,X40] : k3_tarski(k2_tarski(X39,X40)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_46,plain,(
    ! [X30,X31] : k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) = X30 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_47,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_30])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_41]),c_0_30])).

fof(c_0_51,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

fof(c_0_52,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X22,X24)
      | r1_tarski(X22,k3_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_53,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | v1_relat_1(X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_54,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X43,k1_zfmisc_1(X44))
        | r1_tarski(X43,X44) )
      & ( ~ r1_tarski(X43,X44)
        | m1_subset_1(X43,k1_zfmisc_1(X44)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_61,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X47)
      | ~ v1_relat_1(X48)
      | ~ r1_tarski(X47,X48)
      | r1_tarski(k3_relat_1(X47),k3_relat_1(X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

cnf(c_0_62,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_64,plain,(
    ! [X26,X27,X28] : r1_tarski(k2_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)),k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_65,plain,
    ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_29]),c_0_29]),c_0_41]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k2_enumset1(k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_29]),c_0_30])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_71,plain,(
    ! [X20,X21] : r1_tarski(k3_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_49]),c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k3_relat_1(esk4_0))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k3_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_77,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X3)))),k3_tarski(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_56]),c_0_56]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_79,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_73,c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k3_relat_1(esk3_0))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_81,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_29]),c_0_30])).

cnf(c_0_83,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k3_tarski(k2_enumset1(X3,X3,X3,X2)))
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_49]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_75]),c_0_81]),c_0_82])])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_79]),c_0_58])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.031 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.40  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.40  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.40  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 0.20/0.40  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.40  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.20/0.40  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.20/0.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.40  fof(c_0_19, plain, ![X41, X42]:k1_setfam_1(k2_tarski(X41,X42))=k3_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.40  fof(c_0_20, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_21, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk2_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  fof(c_0_24, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_25, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.40  fof(c_0_26, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  fof(c_0_27, plain, ![X25]:r1_tarski(k1_xboole_0,X25), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.40  cnf(c_0_28, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.40  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  fof(c_0_31, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.40  fof(c_0_32, plain, ![X29]:k4_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.40  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_36, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  fof(c_0_38, plain, ![X32, X33]:r1_xboole_0(k4_xboole_0(X32,X33),X33), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.40  fof(c_0_39, plain, ![X39, X40]:k3_tarski(k2_tarski(X39,X40))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.40  cnf(c_0_40, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.40  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_29])).
% 0.20/0.40  cnf(c_0_42, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_43, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  cnf(c_0_44, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  fof(c_0_45, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.20/0.40  fof(c_0_46, plain, ![X30, X31]:k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31))=X30, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.40  cnf(c_0_47, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_30])).
% 0.20/0.40  cnf(c_0_49, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.40  cnf(c_0_50, plain, (r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_41]), c_0_30])).
% 0.20/0.40  fof(c_0_51, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.20/0.40  fof(c_0_52, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|~r1_tarski(X22,X24)|r1_tarski(X22,k3_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.40  fof(c_0_53, plain, ![X45, X46]:(~v1_relat_1(X45)|(~m1_subset_1(X46,k1_zfmisc_1(X45))|v1_relat_1(X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.40  fof(c_0_54, plain, ![X43, X44]:((~m1_subset_1(X43,k1_zfmisc_1(X44))|r1_tarski(X43,X44))&(~r1_tarski(X43,X44)|m1_subset_1(X43,k1_zfmisc_1(X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.40  cnf(c_0_55, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_56, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_23])).
% 0.20/0.40  cnf(c_0_57, plain, (k5_xboole_0(X1,k1_xboole_0)=X1|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.40  cnf(c_0_58, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_60, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.40  fof(c_0_61, plain, ![X47, X48]:(~v1_relat_1(X47)|(~v1_relat_1(X48)|(~r1_tarski(X47,X48)|r1_tarski(k3_relat_1(X47),k3_relat_1(X48))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.20/0.40  cnf(c_0_62, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.40  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.40  fof(c_0_64, plain, ![X26, X27, X28]:r1_tarski(k2_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)),k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.20/0.40  cnf(c_0_65, plain, (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_29]), c_0_29]), c_0_41]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.40  cnf(c_0_66, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k2_enumset1(k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 0.20/0.40  cnf(c_0_68, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_69, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.40  cnf(c_0_70, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.40  fof(c_0_71, plain, ![X20, X21]:r1_tarski(k3_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.40  cnf(c_0_72, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.40  cnf(c_0_73, plain, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_49]), c_0_66])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k3_relat_1(esk4_0))|~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k3_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.40  cnf(c_0_75, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_77, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.40  cnf(c_0_78, plain, (r1_tarski(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k1_setfam_1(k2_enumset1(X1,X1,X1,X3)))),k3_tarski(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_56]), c_0_56]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.40  cnf(c_0_79, plain, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_73, c_0_58])).
% 0.20/0.40  cnf(c_0_80, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))),k3_relat_1(esk3_0))|~r1_tarski(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_82, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_83, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k3_tarski(k2_enumset1(X3,X3,X3,X2)))|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_49]), c_0_79])).
% 0.20/0.40  cnf(c_0_84, negated_conjecture, (~r1_tarski(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_75]), c_0_81]), c_0_82])])).
% 0.20/0.40  cnf(c_0_85, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_79]), c_0_58])])).
% 0.20/0.40  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 87
% 0.20/0.40  # Proof object clause steps            : 48
% 0.20/0.40  # Proof object formula steps           : 39
% 0.20/0.40  # Proof object conjectures             : 11
% 0.20/0.40  # Proof object clause conjectures      : 8
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 21
% 0.20/0.40  # Proof object initial formulas used   : 19
% 0.20/0.40  # Proof object generating inferences   : 13
% 0.20/0.40  # Proof object simplifying inferences  : 49
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 19
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 27
% 0.20/0.40  # Removed in clause preprocessing      : 5
% 0.20/0.40  # Initial clauses in saturation        : 22
% 0.20/0.40  # Processed clauses                    : 403
% 0.20/0.40  # ...of these trivial                  : 9
% 0.20/0.40  # ...subsumed                          : 241
% 0.20/0.40  # ...remaining for further processing  : 153
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 10
% 0.20/0.40  # Backward-rewritten                   : 6
% 0.20/0.40  # Generated clauses                    : 915
% 0.20/0.40  # ...of the previous two non-trivial   : 823
% 0.20/0.40  # Contextual simplify-reflections      : 10
% 0.20/0.40  # Paramodulations                      : 913
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 114
% 0.20/0.40  #    Positive orientable unit clauses  : 19
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 7
% 0.20/0.40  #    Non-unit-clauses                  : 88
% 0.20/0.40  # Current number of unprocessed clauses: 437
% 0.20/0.40  # ...number of literals in the above   : 1665
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 42
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 2520
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1420
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 111
% 0.20/0.40  # Unit Clause-clause subsumption calls : 161
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 23
% 0.20/0.40  # BW rewrite match successes           : 8
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 16161
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.061 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.064 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
