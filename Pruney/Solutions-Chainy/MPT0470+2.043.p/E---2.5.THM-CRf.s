%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:01 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 184 expanded)
%              Number of clauses        :   37 (  78 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 290 expanded)
%              Number of equality atoms :   73 ( 174 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t22_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_19,plain,(
    ! [X41,X42] : k1_setfam_1(k2_tarski(X41,X42)) = k3_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X43] :
      ( ~ v1_xboole_0(X43)
      | v1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_22,plain,(
    ! [X46] :
      ( ~ v1_relat_1(X46)
      | k3_xboole_0(X46,k2_zfmisc_1(k1_relat_1(X46),k2_relat_1(X46))) = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38) = k5_enumset1(X32,X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X49)
      | ~ v1_relat_1(X50)
      | ~ r1_tarski(k1_relat_1(X49),k2_relat_1(X50))
      | k2_relat_1(k5_relat_1(X50,X49)) = k2_relat_1(X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_33,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_34,plain,(
    ! [X39,X40] :
      ( ( k2_zfmisc_1(X39,X40) != k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0 )
      & ( X39 != k1_xboole_0
        | k2_zfmisc_1(X39,X40) = k1_xboole_0 )
      & ( X40 != k1_xboole_0
        | k2_zfmisc_1(X39,X40) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_35,plain,(
    ! [X10] : k3_xboole_0(X10,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_36,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X47)
      | ~ v1_relat_1(X48)
      | r1_tarski(k1_relat_1(k5_relat_1(X47,X48)),k1_relat_1(X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_46,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_47,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_51,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) = X1
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_55,plain,
    ( k2_relat_1(k5_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

fof(c_0_58,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X44)
      | ~ v1_relat_1(X45)
      | v1_relat_1(k5_relat_1(X44,X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_45]),c_0_47])])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_62,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0
      | k5_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

cnf(c_0_63,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_64,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X1)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_48])])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0
    | k5_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_47])])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_65]),c_0_66]),c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_72,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_64]),c_0_47])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.040 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.14/0.39  fof(t22_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 0.14/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.39  fof(t47_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X1),k2_relat_1(X2))=>k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 0.14/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.14/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.39  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 0.14/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.39  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.14/0.39  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.14/0.39  fof(c_0_19, plain, ![X41, X42]:k1_setfam_1(k2_tarski(X41,X42))=k3_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.39  fof(c_0_20, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.39  fof(c_0_21, plain, ![X43]:(~v1_xboole_0(X43)|v1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.14/0.39  fof(c_0_22, plain, ![X46]:(~v1_relat_1(X46)|k3_xboole_0(X46,k2_zfmisc_1(k1_relat_1(X46),k2_relat_1(X46)))=X46), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).
% 0.14/0.39  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  fof(c_0_25, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.39  fof(c_0_26, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.39  fof(c_0_27, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.39  fof(c_0_28, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.39  fof(c_0_29, plain, ![X32, X33, X34, X35, X36, X37, X38]:k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38)=k5_enumset1(X32,X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.39  fof(c_0_30, plain, ![X49, X50]:(~v1_relat_1(X49)|(~v1_relat_1(X50)|(~r1_tarski(k1_relat_1(X49),k2_relat_1(X50))|k2_relat_1(k5_relat_1(X50,X49))=k2_relat_1(X49)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).
% 0.14/0.39  cnf(c_0_31, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_32, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.39  fof(c_0_33, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.39  fof(c_0_34, plain, ![X39, X40]:((k2_zfmisc_1(X39,X40)!=k1_xboole_0|(X39=k1_xboole_0|X40=k1_xboole_0))&((X39!=k1_xboole_0|k2_zfmisc_1(X39,X40)=k1_xboole_0)&(X40!=k1_xboole_0|k2_zfmisc_1(X39,X40)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.14/0.39  fof(c_0_35, plain, ![X10]:k3_xboole_0(X10,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.39  fof(c_0_36, plain, ![X47, X48]:(~v1_relat_1(X47)|(~v1_relat_1(X48)|r1_tarski(k1_relat_1(k5_relat_1(X47,X48)),k1_relat_1(X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.14/0.39  cnf(c_0_37, plain, (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_38, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.39  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.39  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.39  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.39  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.39  cnf(c_0_44, plain, (k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k2_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_45, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.39  cnf(c_0_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.39  cnf(c_0_47, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.39  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.39  cnf(c_0_49, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  cnf(c_0_50, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  fof(c_0_51, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.39  cnf(c_0_52, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.39  fof(c_0_53, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.14/0.39  cnf(c_0_54, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))=X1|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.14/0.39  cnf(c_0_55, plain, (k2_relat_1(k5_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48])])).
% 0.14/0.39  cnf(c_0_56, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.14/0.39  cnf(c_0_57, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.14/0.39  fof(c_0_58, plain, ![X44, X45]:(~v1_relat_1(X44)|~v1_relat_1(X45)|v1_relat_1(k5_relat_1(X44,X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.14/0.39  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.39  cnf(c_0_60, plain, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_45]), c_0_47])])).
% 0.14/0.39  cnf(c_0_61, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  fof(c_0_62, negated_conjecture, (v1_relat_1(esk1_0)&(k5_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0|k5_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).
% 0.14/0.39  cnf(c_0_63, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])).
% 0.14/0.39  cnf(c_0_64, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.39  cnf(c_0_65, plain, (k1_relat_1(k5_relat_1(k1_xboole_0,X1))=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_48])])).
% 0.14/0.39  cnf(c_0_66, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_61])).
% 0.14/0.39  cnf(c_0_67, negated_conjecture, (k5_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0|k5_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.14/0.39  cnf(c_0_68, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_47])])).
% 0.14/0.39  cnf(c_0_69, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.14/0.39  cnf(c_0_70, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_65]), c_0_66]), c_0_57])).
% 0.14/0.39  cnf(c_0_71, negated_conjecture, (k5_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.14/0.39  cnf(c_0_72, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_64]), c_0_47])])).
% 0.14/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_69])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 74
% 0.14/0.39  # Proof object clause steps            : 37
% 0.14/0.39  # Proof object formula steps           : 37
% 0.14/0.39  # Proof object conjectures             : 7
% 0.14/0.39  # Proof object clause conjectures      : 4
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 22
% 0.14/0.39  # Proof object initial formulas used   : 19
% 0.14/0.39  # Proof object generating inferences   : 10
% 0.14/0.39  # Proof object simplifying inferences  : 35
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 19
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 25
% 0.14/0.39  # Removed in clause preprocessing      : 7
% 0.14/0.39  # Initial clauses in saturation        : 18
% 0.14/0.39  # Processed clauses                    : 49
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 1
% 0.14/0.39  # ...remaining for further processing  : 48
% 0.14/0.39  # Other redundant clauses eliminated   : 4
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 2
% 0.14/0.39  # Backward-rewritten                   : 0
% 0.14/0.39  # Generated clauses                    : 35
% 0.14/0.39  # ...of the previous two non-trivial   : 19
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 31
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 4
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 25
% 0.14/0.39  #    Positive orientable unit clauses  : 10
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 1
% 0.14/0.39  #    Non-unit-clauses                  : 14
% 0.14/0.39  # Current number of unprocessed clauses: 5
% 0.14/0.39  # ...number of literals in the above   : 20
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 26
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 24
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 24
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.39  # Unit Clause-clause subsumption calls : 1
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 2
% 0.14/0.39  # BW rewrite match successes           : 0
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1834
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.043 s
% 0.14/0.39  # System time              : 0.002 s
% 0.14/0.39  # Total time               : 0.045 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
