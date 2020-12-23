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
% DateTime   : Thu Dec  3 10:50:45 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 215 expanded)
%              Number of clauses        :   40 (  94 expanded)
%              Number of leaves         :   12 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 624 expanded)
%              Number of equality atoms :   38 ( 189 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t151_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k9_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t151_relat_1])).

fof(c_0_13,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | k2_relat_1(k7_relat_1(X40,X39)) = k9_relat_1(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( k9_relat_1(esk8_0,esk7_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk8_0),esk7_0) )
    & ( k9_relat_1(esk8_0,esk7_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk8_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X41,X42] :
      ( ( k7_relat_1(X42,X41) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X42),X41)
        | ~ v1_relat_1(X42) )
      & ( ~ r1_xboole_0(k1_relat_1(X42),X41)
        | k7_relat_1(X42,X41) = k1_xboole_0
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_16,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k9_relat_1(esk8_0,esk7_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk8_0,X1)) = k9_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k9_relat_1(esk8_0,esk7_0) = k1_xboole_0
    | k7_relat_1(esk8_0,esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17])])).

cnf(c_0_22,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_23,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( k9_relat_1(esk8_0,esk7_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( k9_relat_1(esk8_0,esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

fof(c_0_26,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_27,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(k4_tarski(X25,esk3_3(X23,X24,X25)),X23)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X27,X28),X23)
        | r2_hidden(X27,X24)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(esk4_2(X29,X30),X30)
        | ~ r2_hidden(k4_tarski(esk4_2(X29,X30),X32),X29)
        | X30 = k1_relat_1(X29) )
      & ( r2_hidden(esk4_2(X29,X30),X30)
        | r2_hidden(k4_tarski(esk4_2(X29,X30),esk5_2(X29,X30)),X29)
        | X30 = k1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X34,X35,X36,X38] :
      ( ( r2_hidden(esk6_3(X34,X35,X36),k1_relat_1(X36))
        | ~ r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(k4_tarski(esk6_3(X34,X35,X36),X34),X36)
        | ~ r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(esk6_3(X34,X35,X36),X35)
        | ~ r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) )
      & ( ~ r2_hidden(X38,k1_relat_1(X36))
        | ~ r2_hidden(k4_tarski(X38,X34),X36)
        | ~ r2_hidden(X38,X35)
        | r2_hidden(X34,k9_relat_1(X36,X35))
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_32])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_43,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_44,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k1_relat_1(esk8_0)),X1)
    | ~ r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k1_relat_1(esk8_0)),k1_relat_1(esk8_0))
    | ~ r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_51,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k1_relat_1(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k1_relat_1(esk8_0)),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,esk7_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk1_2(esk7_0,k1_relat_1(esk8_0)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk7_0,k1_relat_1(esk8_0)),esk3_3(esk8_0,k1_relat_1(esk8_0),esk1_2(esk7_0,k1_relat_1(esk8_0)))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25]),c_0_17])]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 17:56:41 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.14/0.37  # and selection function SelectCQArNTNpEqFirst.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t151_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.14/0.37  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.14/0.37  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.14/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.14/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.37  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.14/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.14/0.37  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.14/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t151_relat_1])).
% 0.14/0.37  fof(c_0_13, plain, ![X39, X40]:(~v1_relat_1(X40)|k2_relat_1(k7_relat_1(X40,X39))=k9_relat_1(X40,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.14/0.37  fof(c_0_14, negated_conjecture, (v1_relat_1(esk8_0)&((k9_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk8_0),esk7_0))&(k9_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk8_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.14/0.37  fof(c_0_15, plain, ![X41, X42]:((k7_relat_1(X42,X41)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X42),X41)|~v1_relat_1(X42))&(~r1_xboole_0(k1_relat_1(X42),X41)|k7_relat_1(X42,X41)=k1_xboole_0|~v1_relat_1(X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.14/0.37  cnf(c_0_16, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_18, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (k9_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (k2_relat_1(k7_relat_1(esk8_0,X1))=k9_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (k9_relat_1(esk8_0,esk7_0)=k1_xboole_0|k7_relat_1(esk8_0,esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_17])])).
% 0.14/0.37  cnf(c_0_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.37  fof(c_0_23, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (k9_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (k9_relat_1(esk8_0,esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.14/0.37  fof(c_0_26, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.37  fof(c_0_27, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.37  fof(c_0_28, plain, ![X23, X24, X25, X27, X28, X29, X30, X32]:(((~r2_hidden(X25,X24)|r2_hidden(k4_tarski(X25,esk3_3(X23,X24,X25)),X23)|X24!=k1_relat_1(X23))&(~r2_hidden(k4_tarski(X27,X28),X23)|r2_hidden(X27,X24)|X24!=k1_relat_1(X23)))&((~r2_hidden(esk4_2(X29,X30),X30)|~r2_hidden(k4_tarski(esk4_2(X29,X30),X32),X29)|X30=k1_relat_1(X29))&(r2_hidden(esk4_2(X29,X30),X30)|r2_hidden(k4_tarski(esk4_2(X29,X30),esk5_2(X29,X30)),X29)|X30=k1_relat_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.14/0.37  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.14/0.37  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  fof(c_0_33, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.14/0.37  cnf(c_0_34, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.37  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.37  fof(c_0_36, plain, ![X34, X35, X36, X38]:((((r2_hidden(esk6_3(X34,X35,X36),k1_relat_1(X36))|~r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36))&(r2_hidden(k4_tarski(esk6_3(X34,X35,X36),X34),X36)|~r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36)))&(r2_hidden(esk6_3(X34,X35,X36),X35)|~r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36)))&(~r2_hidden(X38,k1_relat_1(X36))|~r2_hidden(k4_tarski(X38,X34),X36)|~r2_hidden(X38,X35)|r2_hidden(X34,k9_relat_1(X36,X35))|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.14/0.37  cnf(c_0_37, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.37  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.14/0.37  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_32])).
% 0.14/0.37  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.37  cnf(c_0_42, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.37  fof(c_0_43, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.37  fof(c_0_44, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.37  cnf(c_0_45, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.37  cnf(c_0_46, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_37])).
% 0.14/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(X1,k1_relat_1(esk8_0)),X1)|~r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.37  cnf(c_0_49, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(X1,k1_relat_1(esk8_0)),k1_relat_1(esk8_0))|~r2_hidden(esk1_2(k1_relat_1(esk8_0),esk7_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.14/0.37  cnf(c_0_51, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.37  cnf(c_0_52, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.37  cnf(c_0_53, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.37  cnf(c_0_54, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.37  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k1_relat_1(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.37  cnf(c_0_56, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_49])).
% 0.14/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k1_relat_1(esk8_0)),k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.14/0.37  cnf(c_0_58, plain, (~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.37  cnf(c_0_59, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_53, c_0_42])).
% 0.14/0.37  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,esk7_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk1_2(esk7_0,k1_relat_1(esk8_0)),X1),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.37  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk7_0,k1_relat_1(esk8_0)),esk3_3(esk8_0,k1_relat_1(esk8_0),esk1_2(esk7_0,k1_relat_1(esk8_0)))),esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.37  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.14/0.37  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_25]), c_0_17])]), c_0_62]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 64
% 0.14/0.37  # Proof object clause steps            : 40
% 0.14/0.37  # Proof object formula steps           : 24
% 0.14/0.37  # Proof object conjectures             : 19
% 0.14/0.37  # Proof object clause conjectures      : 16
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 17
% 0.14/0.37  # Proof object initial formulas used   : 12
% 0.14/0.37  # Proof object generating inferences   : 15
% 0.14/0.37  # Proof object simplifying inferences  : 17
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 12
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 25
% 0.14/0.37  # Removed in clause preprocessing      : 2
% 0.14/0.37  # Initial clauses in saturation        : 23
% 0.14/0.37  # Processed clauses                    : 113
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 20
% 0.14/0.37  # ...remaining for further processing  : 93
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 1
% 0.14/0.37  # Backward-rewritten                   : 6
% 0.14/0.37  # Generated clauses                    : 134
% 0.14/0.37  # ...of the previous two non-trivial   : 106
% 0.14/0.37  # Contextual simplify-reflections      : 1
% 0.14/0.37  # Paramodulations                      : 132
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 61
% 0.14/0.37  #    Positive orientable unit clauses  : 18
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 41
% 0.14/0.37  # Current number of unprocessed clauses: 32
% 0.14/0.37  # ...number of literals in the above   : 78
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 32
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 223
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 194
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.14/0.37  # Unit Clause-clause subsumption calls : 17
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 4
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3897
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.031 s
% 0.14/0.37  # System time              : 0.006 s
% 0.14/0.37  # Total time               : 0.037 s
% 0.14/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
