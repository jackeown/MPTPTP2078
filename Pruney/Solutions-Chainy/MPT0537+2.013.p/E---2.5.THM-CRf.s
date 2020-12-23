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
% DateTime   : Thu Dec  3 10:50:16 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 216 expanded)
%              Number of clauses        :   31 (  84 expanded)
%              Number of leaves         :   16 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 303 expanded)
%              Number of equality atoms :   63 ( 216 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t22_zfmisc_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t137_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(fc18_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X2) )
     => ( v1_xboole_0(k8_relat_1(X2,X1))
        & v1_relat_1(k8_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

fof(t103_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_16,plain,(
    ! [X32,X33] : k3_xboole_0(k1_tarski(X32),k2_tarski(X32,X33)) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X23] : k2_enumset1(X23,X23,X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_18,plain,(
    ! [X17,X18] : k2_enumset1(X17,X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_19,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22] : k4_enumset1(X19,X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_21,plain,(
    ! [X11,X12,X13,X14,X15,X16] : k5_enumset1(X11,X11,X12,X13,X14,X15,X16) = k4_enumset1(X11,X12,X13,X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X34,X35] : k4_xboole_0(k1_tarski(X34),k2_tarski(X34,X35)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t22_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r2_hidden(X36,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) != k2_tarski(X36,X37) )
      & ( ~ r2_hidden(X37,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) != k2_tarski(X36,X37) )
      & ( r2_hidden(X36,X38)
        | r2_hidden(X37,X38)
        | k4_xboole_0(k2_tarski(X36,X37),X38) = k2_tarski(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_24,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X30,X31] :
      ( ( k2_zfmisc_1(X30,X31) != k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0 )
      & ( X30 != k1_xboole_0
        | k2_zfmisc_1(X30,X31) = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k2_zfmisc_1(X30,X31) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t137_relat_1])).

fof(c_0_36,plain,(
    ! [X7] :
      ( X7 = k1_xboole_0
      | r2_hidden(esk1_1(X7),X7) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_37,plain,(
    ! [X39,X40] :
      ( ( v1_xboole_0(k8_relat_1(X40,X39))
        | ~ v1_relat_1(X39)
        | ~ v1_xboole_0(X40) )
      & ( v1_relat_1(k8_relat_1(X40,X39))
        | ~ v1_relat_1(X39)
        | ~ v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc18_relat_1])])])).

fof(c_0_38,plain,(
    ! [X24,X25,X26,X27] :
      ( ( r2_hidden(esk2_4(X24,X25,X26,X27),X25)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26))
        | ~ r2_hidden(X27,X24) )
      & ( r2_hidden(esk3_4(X24,X25,X26,X27),X26)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26))
        | ~ r2_hidden(X27,X24) )
      & ( X27 = k4_tarski(esk2_4(X24,X25,X26,X27),esk3_4(X24,X25,X26,X27))
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X26))
        | ~ r2_hidden(X27,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2) != k5_enumset1(X3,X3,X3,X3,X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_26]),c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | r1_tarski(k2_relat_1(k8_relat_1(X41,X42)),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

fof(c_0_43,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & k8_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

fof(c_0_44,plain,(
    ! [X43] :
      ( ( k1_relat_1(X43) != k1_xboole_0
        | X43 = k1_xboole_0
        | ~ v1_relat_1(X43) )
      & ( k2_relat_1(X43) != k1_xboole_0
        | X43 = k1_xboole_0
        | ~ v1_relat_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r2_hidden(esk1_1(X2),X2)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_45])).

cnf(c_0_55,plain,
    ( v1_relat_1(k8_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(k2_relat_1(X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54])]),c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(k8_relat_1(k1_xboole_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k8_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(k8_relat_1(k1_xboole_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 3.73/3.89  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.73/3.89  # and selection function SelectNegativeLiterals.
% 3.73/3.89  #
% 3.73/3.89  # Preprocessing time       : 0.027 s
% 3.73/3.89  # Presaturation interreduction done
% 3.73/3.89  
% 3.73/3.89  # Proof found!
% 3.73/3.89  # SZS status Theorem
% 3.73/3.89  # SZS output start CNFRefutation
% 3.73/3.89  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.73/3.89  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 3.73/3.89  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 3.73/3.89  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.73/3.89  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 3.73/3.89  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.73/3.89  fof(t22_zfmisc_1, axiom, ![X1, X2]:k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 3.73/3.89  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.73/3.89  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.73/3.89  fof(t137_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 3.73/3.89  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.73/3.89  fof(fc18_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_xboole_0(X2))=>(v1_xboole_0(k8_relat_1(X2,X1))&v1_relat_1(k8_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc18_relat_1)).
% 3.73/3.89  fof(t103_zfmisc_1, axiom, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 3.73/3.89  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 3.73/3.89  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.73/3.89  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.73/3.89  fof(c_0_16, plain, ![X32, X33]:k3_xboole_0(k1_tarski(X32),k2_tarski(X32,X33))=k1_tarski(X32), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 3.73/3.89  fof(c_0_17, plain, ![X23]:k2_enumset1(X23,X23,X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 3.73/3.89  fof(c_0_18, plain, ![X17, X18]:k2_enumset1(X17,X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 3.73/3.89  fof(c_0_19, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 3.73/3.89  fof(c_0_20, plain, ![X19, X20, X21, X22]:k4_enumset1(X19,X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 3.73/3.89  fof(c_0_21, plain, ![X11, X12, X13, X14, X15, X16]:k5_enumset1(X11,X11,X12,X13,X14,X15,X16)=k4_enumset1(X11,X12,X13,X14,X15,X16), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 3.73/3.89  fof(c_0_22, plain, ![X34, X35]:k4_xboole_0(k1_tarski(X34),k2_tarski(X34,X35))=k1_xboole_0, inference(variable_rename,[status(thm)],[t22_zfmisc_1])).
% 3.73/3.89  fof(c_0_23, plain, ![X36, X37, X38]:(((~r2_hidden(X36,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)!=k2_tarski(X36,X37))&(~r2_hidden(X37,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)!=k2_tarski(X36,X37)))&(r2_hidden(X36,X38)|r2_hidden(X37,X38)|k4_xboole_0(k2_tarski(X36,X37),X38)=k2_tarski(X36,X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 3.73/3.89  cnf(c_0_24, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.73/3.89  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.73/3.89  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.73/3.89  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.73/3.89  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.73/3.89  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.73/3.89  cnf(c_0_30, plain, (k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.73/3.89  fof(c_0_31, plain, ![X30, X31]:((k2_zfmisc_1(X30,X31)!=k1_xboole_0|(X30=k1_xboole_0|X31=k1_xboole_0))&((X30!=k1_xboole_0|k2_zfmisc_1(X30,X31)=k1_xboole_0)&(X31!=k1_xboole_0|k2_zfmisc_1(X30,X31)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 3.73/3.89  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.73/3.89  cnf(c_0_33, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 3.73/3.89  cnf(c_0_34, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_26]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 3.73/3.89  fof(c_0_35, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t137_relat_1])).
% 3.73/3.89  fof(c_0_36, plain, ![X7]:(X7=k1_xboole_0|r2_hidden(esk1_1(X7),X7)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 3.73/3.89  fof(c_0_37, plain, ![X39, X40]:((v1_xboole_0(k8_relat_1(X40,X39))|(~v1_relat_1(X39)|~v1_xboole_0(X40)))&(v1_relat_1(k8_relat_1(X40,X39))|(~v1_relat_1(X39)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc18_relat_1])])])).
% 3.73/3.89  fof(c_0_38, plain, ![X24, X25, X26, X27]:(((r2_hidden(esk2_4(X24,X25,X26,X27),X25)|(~r1_tarski(X24,k2_zfmisc_1(X25,X26))|~r2_hidden(X27,X24)))&(r2_hidden(esk3_4(X24,X25,X26,X27),X26)|(~r1_tarski(X24,k2_zfmisc_1(X25,X26))|~r2_hidden(X27,X24))))&(X27=k4_tarski(esk2_4(X24,X25,X26,X27),esk3_4(X24,X25,X26,X27))|(~r1_tarski(X24,k2_zfmisc_1(X25,X26))|~r2_hidden(X27,X24)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).
% 3.73/3.89  cnf(c_0_39, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.73/3.89  cnf(c_0_40, plain, (k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2)!=k5_enumset1(X3,X3,X3,X3,X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_26]), c_0_26]), c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 3.73/3.89  cnf(c_0_41, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_xboole_0)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 3.73/3.89  fof(c_0_42, plain, ![X41, X42]:(~v1_relat_1(X42)|r1_tarski(k2_relat_1(k8_relat_1(X41,X42)),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 3.73/3.89  fof(c_0_43, negated_conjecture, (v1_relat_1(esk4_0)&k8_relat_1(k1_xboole_0,esk4_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 3.73/3.89  fof(c_0_44, plain, ![X43]:((k1_relat_1(X43)!=k1_xboole_0|X43=k1_xboole_0|~v1_relat_1(X43))&(k2_relat_1(X43)!=k1_xboole_0|X43=k1_xboole_0|~v1_relat_1(X43))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 3.73/3.89  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.73/3.89  cnf(c_0_46, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.73/3.89  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 3.73/3.89  cnf(c_0_48, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.73/3.89  cnf(c_0_49, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_39])).
% 3.73/3.89  cnf(c_0_50, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.73/3.89  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.73/3.89  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.73/3.89  cnf(c_0_53, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.73/3.89  cnf(c_0_54, plain, (X1=X2|r2_hidden(esk1_1(X2),X2)|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_45])).
% 3.73/3.89  cnf(c_0_55, plain, (v1_relat_1(k8_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.73/3.89  cnf(c_0_56, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 3.73/3.89  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 3.73/3.89  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(k2_relat_1(X1)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54])]), c_0_50])).
% 3.73/3.89  cnf(c_0_59, negated_conjecture, (v1_relat_1(k8_relat_1(k1_xboole_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_52])).
% 3.73/3.89  cnf(c_0_60, negated_conjecture, (k8_relat_1(k1_xboole_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.73/3.89  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,k2_relat_1(k8_relat_1(k1_xboole_0,esk4_0)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 3.73/3.89  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), ['proof']).
% 3.73/3.89  # SZS output end CNFRefutation
% 3.73/3.89  # Proof object total steps             : 63
% 3.73/3.89  # Proof object clause steps            : 31
% 3.73/3.89  # Proof object formula steps           : 32
% 3.73/3.89  # Proof object conjectures             : 9
% 3.73/3.89  # Proof object clause conjectures      : 6
% 3.73/3.89  # Proof object formula conjectures     : 3
% 3.73/3.89  # Proof object initial clauses used    : 17
% 3.73/3.89  # Proof object initial formulas used   : 16
% 3.73/3.89  # Proof object generating inferences   : 9
% 3.73/3.89  # Proof object simplifying inferences  : 31
% 3.73/3.89  # Training examples: 0 positive, 0 negative
% 3.73/3.89  # Parsed axioms                        : 16
% 3.73/3.89  # Removed by relevancy pruning/SinE    : 0
% 3.73/3.89  # Initial clauses                      : 25
% 3.73/3.89  # Removed in clause preprocessing      : 5
% 3.73/3.89  # Initial clauses in saturation        : 20
% 3.73/3.89  # Processed clauses                    : 5881
% 3.73/3.89  # ...of these trivial                  : 4
% 3.73/3.89  # ...subsumed                          : 2871
% 3.73/3.89  # ...remaining for further processing  : 3005
% 3.73/3.89  # Other redundant clauses eliminated   : 240
% 3.73/3.89  # Clauses deleted for lack of memory   : 0
% 3.73/3.89  # Backward-subsumed                    : 0
% 3.73/3.89  # Backward-rewritten                   : 0
% 3.73/3.89  # Generated clauses                    : 717901
% 3.73/3.89  # ...of the previous two non-trivial   : 610054
% 3.73/3.89  # Contextual simplify-reflections      : 0
% 3.73/3.89  # Paramodulations                      : 717647
% 3.73/3.89  # Factorizations                       : 14
% 3.73/3.89  # Equation resolutions                 : 240
% 3.73/3.89  # Propositional unsat checks           : 0
% 3.73/3.89  #    Propositional check models        : 0
% 3.73/3.89  #    Propositional check unsatisfiable : 0
% 3.73/3.89  #    Propositional clauses             : 0
% 3.73/3.89  #    Propositional clauses after purity: 0
% 3.73/3.89  #    Propositional unsat core size     : 0
% 3.73/3.89  #    Propositional preprocessing time  : 0.000
% 3.73/3.89  #    Propositional encoding time       : 0.000
% 3.73/3.89  #    Propositional solver time         : 0.000
% 3.73/3.89  #    Success case prop preproc time    : 0.000
% 3.73/3.89  #    Success case prop encoding time   : 0.000
% 3.73/3.89  #    Success case prop solver time     : 0.000
% 3.73/3.89  # Current number of processed clauses  : 2983
% 3.73/3.89  #    Positive orientable unit clauses  : 2271
% 3.73/3.89  #    Positive unorientable unit clauses: 0
% 3.73/3.89  #    Negative unit clauses             : 35
% 3.73/3.89  #    Non-unit-clauses                  : 677
% 3.73/3.89  # Current number of unprocessed clauses: 604213
% 3.73/3.89  # ...number of literals in the above   : 1253183
% 3.73/3.89  # Current number of archived formulas  : 0
% 3.73/3.89  # Current number of archived clauses   : 25
% 3.73/3.89  # Clause-clause subsumption calls (NU) : 117550
% 3.73/3.89  # Rec. Clause-clause subsumption calls : 83295
% 3.73/3.89  # Non-unit clause-clause subsumptions  : 2344
% 3.73/3.89  # Unit Clause-clause subsumption calls : 36164
% 3.73/3.89  # Rewrite failures with RHS unbound    : 0
% 3.73/3.89  # BW rewrite match attempts            : 1293155
% 3.73/3.89  # BW rewrite match successes           : 0
% 3.73/3.89  # Condensation attempts                : 0
% 3.73/3.89  # Condensation successes               : 0
% 3.73/3.89  # Termbank termtop insertions          : 16050973
% 3.73/3.92  
% 3.73/3.92  # -------------------------------------------------
% 3.73/3.92  # User time                : 3.320 s
% 3.73/3.92  # System time              : 0.250 s
% 3.73/3.92  # Total time               : 3.569 s
% 3.73/3.92  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
