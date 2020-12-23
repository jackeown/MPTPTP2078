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
% DateTime   : Thu Dec  3 10:40:32 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 270 expanded)
%              Number of clauses        :   36 ( 110 expanded)
%              Number of leaves         :   15 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 382 expanded)
%              Number of equality atoms :   44 ( 232 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X40,X41] : k3_tarski(k2_tarski(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    & k2_xboole_0(k1_tarski(esk2_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X34,X35,X36,X37] : k3_enumset1(X34,X34,X35,X36,X37) = k2_enumset1(X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_28,plain,(
    ! [X38,X39] :
      ( ( ~ r1_tarski(k1_tarski(X38),X39)
        | r2_hidden(X38,X39) )
      & ( ~ r2_hidden(X38,X39)
        | r1_tarski(k1_tarski(X38),X39) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_29,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_30,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X15)
        | r2_hidden(X13,X14)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_21]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_45,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_46,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_33]),c_0_34]),c_0_35])).

fof(c_0_48,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_32]),c_0_21]),c_0_34]),c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_33]),c_0_43]),c_0_34]),c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X1
    | r2_hidden(esk1_2(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))
    | r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_61]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_65]),c_0_47])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.48/2.67  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.48/2.67  # and selection function SelectNegativeLiterals.
% 2.48/2.67  #
% 2.48/2.67  # Preprocessing time       : 0.027 s
% 2.48/2.67  # Presaturation interreduction done
% 2.48/2.67  
% 2.48/2.67  # Proof found!
% 2.48/2.67  # SZS status Theorem
% 2.48/2.67  # SZS output start CNFRefutation
% 2.48/2.67  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.48/2.67  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.48/2.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.48/2.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.48/2.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.48/2.67  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.48/2.67  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.48/2.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.48/2.67  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.48/2.67  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.48/2.67  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.48/2.67  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.48/2.67  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.48/2.67  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.48/2.67  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.48/2.67  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 2.48/2.67  fof(c_0_16, plain, ![X40, X41]:k3_tarski(k2_tarski(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 2.48/2.67  fof(c_0_17, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.48/2.67  fof(c_0_18, negated_conjecture, (r2_hidden(esk2_0,esk3_0)&k2_xboole_0(k1_tarski(esk2_0),esk3_0)!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 2.48/2.67  fof(c_0_19, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.48/2.67  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.48/2.67  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.48/2.67  fof(c_0_22, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.48/2.67  fof(c_0_23, plain, ![X34, X35, X36, X37]:k3_enumset1(X34,X34,X35,X36,X37)=k2_enumset1(X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.48/2.67  fof(c_0_24, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.48/2.67  fof(c_0_25, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.48/2.67  fof(c_0_26, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.48/2.67  fof(c_0_27, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.48/2.67  fof(c_0_28, plain, ![X38, X39]:((~r1_tarski(k1_tarski(X38),X39)|r2_hidden(X38,X39))&(~r2_hidden(X38,X39)|r1_tarski(k1_tarski(X38),X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 2.48/2.67  fof(c_0_29, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(X26,k4_xboole_0(X27,X26)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.48/2.67  fof(c_0_30, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.48/2.67  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),esk3_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.48/2.67  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.48/2.67  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 2.48/2.67  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.48/2.67  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.48/2.67  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.48/2.67  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.48/2.67  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.48/2.67  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.48/2.67  cnf(c_0_40, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.48/2.67  fof(c_0_41, plain, ![X13, X14, X15]:(((~r2_hidden(X13,X14)|~r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15)))&(r2_hidden(X13,X14)|r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15))))&((~r2_hidden(X13,X14)|r2_hidden(X13,X15)|r2_hidden(X13,k5_xboole_0(X14,X15)))&(~r2_hidden(X13,X15)|r2_hidden(X13,X14)|r2_hidden(X13,k5_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 2.48/2.67  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.48/2.67  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.48/2.67  cnf(c_0_44, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_21]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 2.48/2.67  cnf(c_0_45, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 2.48/2.67  cnf(c_0_46, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.48/2.67  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_33]), c_0_34]), c_0_35])).
% 2.48/2.67  fof(c_0_48, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.48/2.67  cnf(c_0_49, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_32]), c_0_21]), c_0_34]), c_0_35])).
% 2.48/2.67  cnf(c_0_50, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.48/2.67  cnf(c_0_51, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.48/2.67  cnf(c_0_52, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_33]), c_0_43]), c_0_34]), c_0_35])).
% 2.48/2.67  cnf(c_0_53, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))!=esk3_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 2.48/2.67  cnf(c_0_54, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X1|r2_hidden(esk1_2(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.48/2.67  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.48/2.67  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.48/2.67  cnf(c_0_57, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.48/2.67  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 2.48/2.67  cnf(c_0_59, negated_conjecture, (k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.48/2.67  cnf(c_0_60, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.48/2.67  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))|r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 2.48/2.67  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_56])).
% 2.48/2.67  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.48/2.67  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_61]), c_0_62])).
% 2.48/2.67  cnf(c_0_65, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 2.48/2.67  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_65]), c_0_47])]), c_0_53]), ['proof']).
% 2.48/2.67  # SZS output end CNFRefutation
% 2.48/2.67  # Proof object total steps             : 67
% 2.48/2.67  # Proof object clause steps            : 36
% 2.48/2.67  # Proof object formula steps           : 31
% 2.48/2.67  # Proof object conjectures             : 15
% 2.48/2.67  # Proof object clause conjectures      : 12
% 2.48/2.67  # Proof object formula conjectures     : 3
% 2.48/2.67  # Proof object initial clauses used    : 18
% 2.48/2.67  # Proof object initial formulas used   : 15
% 2.48/2.67  # Proof object generating inferences   : 11
% 2.48/2.67  # Proof object simplifying inferences  : 34
% 2.48/2.67  # Training examples: 0 positive, 0 negative
% 2.48/2.67  # Parsed axioms                        : 16
% 2.48/2.67  # Removed by relevancy pruning/SinE    : 0
% 2.48/2.67  # Initial clauses                      : 25
% 2.48/2.67  # Removed in clause preprocessing      : 6
% 2.48/2.67  # Initial clauses in saturation        : 19
% 2.48/2.67  # Processed clauses                    : 9465
% 2.48/2.67  # ...of these trivial                  : 286
% 2.48/2.67  # ...subsumed                          : 6817
% 2.48/2.67  # ...remaining for further processing  : 2362
% 2.48/2.67  # Other redundant clauses eliminated   : 37
% 2.48/2.67  # Clauses deleted for lack of memory   : 0
% 2.48/2.67  # Backward-subsumed                    : 65
% 2.48/2.67  # Backward-rewritten                   : 89
% 2.48/2.67  # Generated clauses                    : 257763
% 2.48/2.67  # ...of the previous two non-trivial   : 210175
% 2.48/2.67  # Contextual simplify-reflections      : 45
% 2.48/2.67  # Paramodulations                      : 257556
% 2.48/2.67  # Factorizations                       : 170
% 2.48/2.67  # Equation resolutions                 : 37
% 2.48/2.67  # Propositional unsat checks           : 0
% 2.48/2.67  #    Propositional check models        : 0
% 2.48/2.67  #    Propositional check unsatisfiable : 0
% 2.48/2.67  #    Propositional clauses             : 0
% 2.48/2.67  #    Propositional clauses after purity: 0
% 2.48/2.67  #    Propositional unsat core size     : 0
% 2.48/2.67  #    Propositional preprocessing time  : 0.000
% 2.48/2.67  #    Propositional encoding time       : 0.000
% 2.48/2.67  #    Propositional solver time         : 0.000
% 2.48/2.67  #    Success case prop preproc time    : 0.000
% 2.48/2.67  #    Success case prop encoding time   : 0.000
% 2.48/2.67  #    Success case prop solver time     : 0.000
% 2.48/2.67  # Current number of processed clauses  : 2188
% 2.48/2.67  #    Positive orientable unit clauses  : 497
% 2.48/2.67  #    Positive unorientable unit clauses: 4
% 2.48/2.67  #    Negative unit clauses             : 192
% 2.48/2.67  #    Non-unit-clauses                  : 1495
% 2.48/2.67  # Current number of unprocessed clauses: 199851
% 2.48/2.67  # ...number of literals in the above   : 728612
% 2.48/2.67  # Current number of archived formulas  : 0
% 2.48/2.67  # Current number of archived clauses   : 178
% 2.48/2.67  # Clause-clause subsumption calls (NU) : 118929
% 2.48/2.67  # Rec. Clause-clause subsumption calls : 78134
% 2.48/2.67  # Non-unit clause-clause subsumptions  : 4202
% 2.48/2.67  # Unit Clause-clause subsumption calls : 3299
% 2.48/2.67  # Rewrite failures with RHS unbound    : 0
% 2.48/2.67  # BW rewrite match attempts            : 8085
% 2.48/2.67  # BW rewrite match successes           : 110
% 2.48/2.67  # Condensation attempts                : 0
% 2.48/2.67  # Condensation successes               : 0
% 2.48/2.67  # Termbank termtop insertions          : 7722888
% 2.48/2.68  
% 2.48/2.68  # -------------------------------------------------
% 2.48/2.68  # User time                : 2.235 s
% 2.48/2.68  # System time              : 0.100 s
% 2.48/2.68  # Total time               : 2.335 s
% 2.48/2.68  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
