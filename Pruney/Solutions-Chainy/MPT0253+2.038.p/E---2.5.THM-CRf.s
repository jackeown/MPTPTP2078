%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:57 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  106 (1511 expanded)
%              Number of clauses        :   65 ( 568 expanded)
%              Number of leaves         :   20 ( 470 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 (1710 expanded)
%              Number of equality atoms :   93 (1502 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(t137_enumset1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t48_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_20,plain,(
    ! [X76,X77] : k3_tarski(k2_tarski(X76,X77)) = k2_xboole_0(X76,X77) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X59,X60] : k1_enumset1(X59,X59,X60) = k2_tarski(X59,X60) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X41] : k2_xboole_0(X41,k1_xboole_0) = X41 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X61,X62,X63] : k2_enumset1(X61,X61,X62,X63) = k1_enumset1(X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X64,X65,X66,X67] : k3_enumset1(X64,X64,X65,X66,X67) = k2_enumset1(X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X68,X69,X70,X71,X72] : k4_enumset1(X68,X68,X69,X70,X71,X72) = k3_enumset1(X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X73,X74,X75] : k1_enumset1(X73,X74,X75) = k1_enumset1(X73,X75,X74) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

fof(c_0_29,plain,(
    ! [X51,X52,X53] : k2_xboole_0(k2_tarski(X52,X51),k2_tarski(X53,X51)) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t137_enumset1])).

fof(c_0_30,plain,(
    ! [X47,X48,X49,X50] : k2_enumset1(X47,X48,X49,X50) = k2_xboole_0(k2_tarski(X47,X48),k2_tarski(X49,X50)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X2)) = k1_enumset1(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X54,X55,X56,X57] : k2_enumset1(X54,X55,X56,X57) = k2_xboole_0(k1_enumset1(X54,X55,X56),k1_tarski(X57)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_40,plain,(
    ! [X58] : k2_tarski(X58,X58) = k1_tarski(X58) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk3_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk3_3(X24,X25,X26),X24)
        | r2_hidden(esk3_3(X24,X25,X26),X25)
        | X26 = k4_xboole_0(X24,X25) )
      & ( r2_hidden(esk3_3(X24,X25,X26),X24)
        | r2_hidden(esk3_3(X24,X25,X26),X26)
        | X26 = k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk3_3(X24,X25,X26),X25)
        | r2_hidden(esk3_3(X24,X25,X26),X26)
        | X26 = k4_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_42,plain,(
    ! [X39,X40] : k4_xboole_0(X39,X40) = k5_xboole_0(X39,k3_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_43,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X1,X1,X2,X3) = k4_enumset1(X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_45,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X2))) = k4_enumset1(X2,X2,X2,X2,X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_24]),c_0_24]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_24]),c_0_24]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X42,X43] :
      ( ~ r1_tarski(X42,X43)
      | k3_xboole_0(X42,X43) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_52,plain,(
    ! [X44] : r1_tarski(k1_xboole_0,X44) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_53,plain,(
    ! [X45,X46] : k2_xboole_0(X45,k4_xboole_0(X46,X45)) = k2_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_54,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X2) = k4_enumset1(X2,X2,X2,X2,X1,X3) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_24]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

fof(c_0_57,plain,(
    ! [X78,X79,X80] :
      ( ( r2_hidden(X78,X80)
        | ~ r1_tarski(k2_tarski(X78,X79),X80) )
      & ( r2_hidden(X79,X80)
        | ~ r1_tarski(k2_tarski(X78,X79),X80) )
      & ( ~ r2_hidden(X78,X80)
        | ~ r2_hidden(X79,X80)
        | r1_tarski(k2_tarski(X78,X79),X80) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_58,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r2_hidden(X3,X2) )
       => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t48_zfmisc_1])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_60,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X3) = k4_enumset1(X1,X1,X1,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_46])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_67,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    & r2_hidden(esk8_0,esk7_0)
    & k2_xboole_0(k2_tarski(esk6_0,esk8_0),esk7_0) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_59,c_0_50])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_32]),c_0_32]),c_0_50]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_72,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_73,plain,(
    ! [X37,X38] :
      ( ( r1_tarski(X37,X38)
        | X37 != X38 )
      & ( r1_tarski(X38,X37)
        | X37 != X38 )
      & ( ~ r1_tarski(X37,X38)
        | ~ r1_tarski(X38,X37)
        | X37 = X38 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_74,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_24]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_70]),c_0_43])).

cnf(c_0_79,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_72,c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk6_0,esk8_0),esk7_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_84,plain,(
    ! [X28,X29] :
      ( ( ~ r2_hidden(esk4_2(X28,X29),X28)
        | ~ r2_hidden(esk4_2(X28,X29),X29)
        | X28 = X29 )
      & ( r2_hidden(esk4_2(X28,X29),X28)
        | r2_hidden(esk4_2(X28,X29),X29)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_70]),c_0_77])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k3_tarski(k4_enumset1(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0)) != esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_24]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_91,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk4_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k3_tarski(k4_enumset1(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0))) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_87,c_0_44])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_61,c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0) = k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_89])).

cnf(c_0_96,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_62])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk4_2(X1,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_91]),c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0))) != esk7_0 ),
    inference(rw,[status(thm)],[c_0_93,c_0_55])).

cnf(c_0_99,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k5_xboole_0(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0)))) = k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_95])).

cnf(c_0_101,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk4_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,k1_xboole_0,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_65])).

cnf(c_0_103,negated_conjecture,
    ( k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0))) != esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_65]),c_0_65])).

cnf(c_0_104,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_94]),c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_44]),c_0_65]),c_0_102]),c_0_103]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:03:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.57  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.40/0.57  # and selection function SelectNegativeLiterals.
% 0.40/0.57  #
% 0.40/0.57  # Preprocessing time       : 0.028 s
% 0.40/0.57  # Presaturation interreduction done
% 0.40/0.57  
% 0.40/0.57  # Proof found!
% 0.40/0.57  # SZS status Theorem
% 0.40/0.57  # SZS output start CNFRefutation
% 0.40/0.57  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.40/0.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.40/0.57  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.40/0.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.40/0.57  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.40/0.57  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.40/0.57  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 0.40/0.57  fof(t137_enumset1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.40/0.57  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.40/0.57  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.40/0.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.40/0.57  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.40/0.57  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.40/0.57  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.40/0.57  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.40/0.57  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.40/0.57  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.40/0.57  fof(t48_zfmisc_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 0.40/0.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.40/0.57  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.40/0.57  fof(c_0_20, plain, ![X76, X77]:k3_tarski(k2_tarski(X76,X77))=k2_xboole_0(X76,X77), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.40/0.57  fof(c_0_21, plain, ![X59, X60]:k1_enumset1(X59,X59,X60)=k2_tarski(X59,X60), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.40/0.57  fof(c_0_22, plain, ![X41]:k2_xboole_0(X41,k1_xboole_0)=X41, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.40/0.57  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.57  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.57  fof(c_0_25, plain, ![X61, X62, X63]:k2_enumset1(X61,X61,X62,X63)=k1_enumset1(X61,X62,X63), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.40/0.57  fof(c_0_26, plain, ![X64, X65, X66, X67]:k3_enumset1(X64,X64,X65,X66,X67)=k2_enumset1(X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.40/0.57  fof(c_0_27, plain, ![X68, X69, X70, X71, X72]:k4_enumset1(X68,X68,X69,X70,X71,X72)=k3_enumset1(X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.40/0.57  fof(c_0_28, plain, ![X73, X74, X75]:k1_enumset1(X73,X74,X75)=k1_enumset1(X73,X75,X74), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.40/0.57  fof(c_0_29, plain, ![X51, X52, X53]:k2_xboole_0(k2_tarski(X52,X51),k2_tarski(X53,X51))=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t137_enumset1])).
% 0.40/0.57  fof(c_0_30, plain, ![X47, X48, X49, X50]:k2_enumset1(X47,X48,X49,X50)=k2_xboole_0(k2_tarski(X47,X48),k2_tarski(X49,X50)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.40/0.57  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.40/0.57  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.40/0.57  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.40/0.57  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.40/0.57  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.40/0.57  cnf(c_0_36, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.40/0.57  cnf(c_0_37, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X2))=k1_enumset1(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.40/0.57  cnf(c_0_38, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.40/0.57  fof(c_0_39, plain, ![X54, X55, X56, X57]:k2_enumset1(X54,X55,X56,X57)=k2_xboole_0(k1_enumset1(X54,X55,X56),k1_tarski(X57)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.40/0.57  fof(c_0_40, plain, ![X58]:k2_tarski(X58,X58)=k1_tarski(X58), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.40/0.57  fof(c_0_41, plain, ![X19, X20, X21, X22, X23, X24, X25, X26]:((((r2_hidden(X22,X19)|~r2_hidden(X22,X21)|X21!=k4_xboole_0(X19,X20))&(~r2_hidden(X22,X20)|~r2_hidden(X22,X21)|X21!=k4_xboole_0(X19,X20)))&(~r2_hidden(X23,X19)|r2_hidden(X23,X20)|r2_hidden(X23,X21)|X21!=k4_xboole_0(X19,X20)))&((~r2_hidden(esk3_3(X24,X25,X26),X26)|(~r2_hidden(esk3_3(X24,X25,X26),X24)|r2_hidden(esk3_3(X24,X25,X26),X25))|X26=k4_xboole_0(X24,X25))&((r2_hidden(esk3_3(X24,X25,X26),X24)|r2_hidden(esk3_3(X24,X25,X26),X26)|X26=k4_xboole_0(X24,X25))&(~r2_hidden(esk3_3(X24,X25,X26),X25)|r2_hidden(esk3_3(X24,X25,X26),X26)|X26=k4_xboole_0(X24,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.40/0.57  fof(c_0_42, plain, ![X39, X40]:k4_xboole_0(X39,X40)=k5_xboole_0(X39,k3_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.40/0.57  cnf(c_0_43, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.40/0.57  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X1,X1,X2,X3)=k4_enumset1(X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.40/0.57  cnf(c_0_45, plain, (k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X2)))=k4_enumset1(X2,X2,X2,X2,X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_24]), c_0_24]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.40/0.57  cnf(c_0_46, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_24]), c_0_24]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.40/0.57  cnf(c_0_47, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.40/0.57  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.40/0.57  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.40/0.57  cnf(c_0_50, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.40/0.57  fof(c_0_51, plain, ![X42, X43]:(~r1_tarski(X42,X43)|k3_xboole_0(X42,X43)=X42), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.40/0.57  fof(c_0_52, plain, ![X44]:r1_tarski(k1_xboole_0,X44), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.40/0.57  fof(c_0_53, plain, ![X45, X46]:k2_xboole_0(X45,k4_xboole_0(X46,X45))=k2_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.40/0.57  cnf(c_0_54, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.40/0.57  cnf(c_0_55, plain, (k4_enumset1(X1,X1,X1,X2,X3,X2)=k4_enumset1(X2,X2,X2,X2,X1,X3)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.40/0.57  cnf(c_0_56, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_24]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.40/0.57  fof(c_0_57, plain, ![X78, X79, X80]:(((r2_hidden(X78,X80)|~r1_tarski(k2_tarski(X78,X79),X80))&(r2_hidden(X79,X80)|~r1_tarski(k2_tarski(X78,X79),X80)))&(~r2_hidden(X78,X80)|~r2_hidden(X79,X80)|r1_tarski(k2_tarski(X78,X79),X80))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.40/0.57  fof(c_0_58, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2)), inference(assume_negation,[status(cth)],[t48_zfmisc_1])).
% 0.40/0.57  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.40/0.57  cnf(c_0_60, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.40/0.57  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.40/0.57  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.40/0.57  cnf(c_0_63, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.40/0.57  cnf(c_0_64, plain, (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.40/0.57  cnf(c_0_65, plain, (k4_enumset1(X1,X1,X1,X2,X3,X3)=k4_enumset1(X1,X1,X1,X1,X2,X3)), inference(spm,[status(thm)],[c_0_56, c_0_46])).
% 0.40/0.57  cnf(c_0_66, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.40/0.57  fof(c_0_67, negated_conjecture, ((r2_hidden(esk6_0,esk7_0)&r2_hidden(esk8_0,esk7_0))&k2_xboole_0(k2_tarski(esk6_0,esk8_0),esk7_0)!=esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).
% 0.40/0.57  cnf(c_0_68, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_59, c_0_50])).
% 0.40/0.57  cnf(c_0_69, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_60])).
% 0.40/0.57  cnf(c_0_70, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.40/0.57  cnf(c_0_71, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_32]), c_0_32]), c_0_50]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.40/0.57  cnf(c_0_72, plain, (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1,X1))=X1), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.40/0.57  fof(c_0_73, plain, ![X37, X38]:(((r1_tarski(X37,X38)|X37!=X38)&(r1_tarski(X38,X37)|X37!=X38))&(~r1_tarski(X37,X38)|~r1_tarski(X38,X37)|X37=X38)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.40/0.57  cnf(c_0_74, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_24]), c_0_33]), c_0_34]), c_0_35])).
% 0.40/0.57  cnf(c_0_75, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.40/0.57  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_68])).
% 0.40/0.57  cnf(c_0_77, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.40/0.57  cnf(c_0_78, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_70]), c_0_43])).
% 0.40/0.57  cnf(c_0_79, plain, (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_72, c_0_65])).
% 0.40/0.57  cnf(c_0_80, negated_conjecture, (k2_xboole_0(k2_tarski(esk6_0,esk8_0),esk7_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.40/0.57  cnf(c_0_81, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.40/0.57  cnf(c_0_82, negated_conjecture, (r1_tarski(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,X1),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.40/0.57  cnf(c_0_83, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.40/0.57  fof(c_0_84, plain, ![X28, X29]:((~r2_hidden(esk4_2(X28,X29),X28)|~r2_hidden(esk4_2(X28,X29),X29)|X28=X29)&(r2_hidden(esk4_2(X28,X29),X28)|r2_hidden(esk4_2(X28,X29),X29)|X28=X29)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.40/0.57  cnf(c_0_85, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_70]), c_0_77])).
% 0.40/0.57  cnf(c_0_86, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.40/0.57  cnf(c_0_87, negated_conjecture, (k3_tarski(k4_enumset1(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0))!=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_24]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.40/0.57  cnf(c_0_88, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_81])).
% 0.40/0.57  cnf(c_0_89, negated_conjecture, (r1_tarski(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.40/0.57  cnf(c_0_90, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.40/0.57  cnf(c_0_91, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk4_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.40/0.57  cnf(c_0_92, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.40/0.57  cnf(c_0_93, negated_conjecture, (k3_tarski(k4_enumset1(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0)))!=esk7_0), inference(rw,[status(thm)],[c_0_87, c_0_44])).
% 0.40/0.57  cnf(c_0_94, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_61, c_0_88])).
% 0.40/0.57  cnf(c_0_95, negated_conjecture, (k3_xboole_0(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),esk7_0)=k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_61, c_0_89])).
% 0.40/0.57  cnf(c_0_96, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_62])).
% 0.40/0.57  cnf(c_0_97, plain, (r1_tarski(X1,X2)|r2_hidden(esk4_2(X1,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_91]), c_0_92])).
% 0.40/0.57  cnf(c_0_98, negated_conjecture, (k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0)))!=esk7_0), inference(rw,[status(thm)],[c_0_93, c_0_55])).
% 0.40/0.57  cnf(c_0_99, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_94])).
% 0.40/0.57  cnf(c_0_100, negated_conjecture, (k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k5_xboole_0(k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0),k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0))))=k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0)))), inference(spm,[status(thm)],[c_0_71, c_0_95])).
% 0.40/0.57  cnf(c_0_101, plain, (k1_xboole_0=X1|r2_hidden(esk4_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.40/0.57  cnf(c_0_102, plain, (k3_tarski(k4_enumset1(X1,X1,X1,k1_xboole_0,X1,X1))=X1), inference(spm,[status(thm)],[c_0_54, c_0_65])).
% 0.40/0.57  cnf(c_0_103, negated_conjecture, (k3_tarski(k4_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk8_0)))!=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_65]), c_0_65])).
% 0.40/0.57  cnf(c_0_104, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_94]), c_0_99])).
% 0.40/0.57  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_44]), c_0_65]), c_0_102]), c_0_103]), c_0_104]), ['proof']).
% 0.40/0.57  # SZS output end CNFRefutation
% 0.40/0.57  # Proof object total steps             : 106
% 0.40/0.57  # Proof object clause steps            : 65
% 0.40/0.57  # Proof object formula steps           : 41
% 0.40/0.57  # Proof object conjectures             : 15
% 0.40/0.57  # Proof object clause conjectures      : 12
% 0.40/0.57  # Proof object formula conjectures     : 3
% 0.40/0.57  # Proof object initial clauses used    : 24
% 0.40/0.57  # Proof object initial formulas used   : 20
% 0.40/0.57  # Proof object generating inferences   : 22
% 0.40/0.57  # Proof object simplifying inferences  : 119
% 0.40/0.57  # Training examples: 0 positive, 0 negative
% 0.40/0.57  # Parsed axioms                        : 23
% 0.40/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.57  # Initial clauses                      : 43
% 0.40/0.57  # Removed in clause preprocessing      : 7
% 0.40/0.57  # Initial clauses in saturation        : 36
% 0.40/0.57  # Processed clauses                    : 1141
% 0.40/0.57  # ...of these trivial                  : 218
% 0.40/0.57  # ...subsumed                          : 411
% 0.40/0.57  # ...remaining for further processing  : 512
% 0.40/0.57  # Other redundant clauses eliminated   : 13
% 0.40/0.57  # Clauses deleted for lack of memory   : 0
% 0.40/0.57  # Backward-subsumed                    : 10
% 0.40/0.57  # Backward-rewritten                   : 12
% 0.40/0.57  # Generated clauses                    : 19242
% 0.40/0.57  # ...of the previous two non-trivial   : 15835
% 0.40/0.57  # Contextual simplify-reflections      : 3
% 0.40/0.57  # Paramodulations                      : 19217
% 0.40/0.57  # Factorizations                       : 12
% 0.40/0.57  # Equation resolutions                 : 13
% 0.40/0.57  # Propositional unsat checks           : 0
% 0.40/0.57  #    Propositional check models        : 0
% 0.40/0.57  #    Propositional check unsatisfiable : 0
% 0.40/0.57  #    Propositional clauses             : 0
% 0.40/0.57  #    Propositional clauses after purity: 0
% 0.40/0.57  #    Propositional unsat core size     : 0
% 0.40/0.57  #    Propositional preprocessing time  : 0.000
% 0.40/0.57  #    Propositional encoding time       : 0.000
% 0.40/0.57  #    Propositional solver time         : 0.000
% 0.40/0.57  #    Success case prop preproc time    : 0.000
% 0.40/0.57  #    Success case prop encoding time   : 0.000
% 0.40/0.57  #    Success case prop solver time     : 0.000
% 0.40/0.57  # Current number of processed clauses  : 447
% 0.40/0.57  #    Positive orientable unit clauses  : 129
% 0.40/0.57  #    Positive unorientable unit clauses: 4
% 0.40/0.57  #    Negative unit clauses             : 3
% 0.40/0.57  #    Non-unit-clauses                  : 311
% 0.40/0.57  # Current number of unprocessed clauses: 14036
% 0.40/0.57  # ...number of literals in the above   : 39884
% 0.40/0.57  # Current number of archived formulas  : 0
% 0.40/0.57  # Current number of archived clauses   : 64
% 0.40/0.57  # Clause-clause subsumption calls (NU) : 13712
% 0.40/0.57  # Rec. Clause-clause subsumption calls : 12644
% 0.40/0.57  # Non-unit clause-clause subsumptions  : 353
% 0.40/0.57  # Unit Clause-clause subsumption calls : 794
% 0.40/0.57  # Rewrite failures with RHS unbound    : 0
% 0.40/0.57  # BW rewrite match attempts            : 796
% 0.40/0.57  # BW rewrite match successes           : 193
% 0.40/0.57  # Condensation attempts                : 0
% 0.40/0.57  # Condensation successes               : 0
% 0.40/0.57  # Termbank termtop insertions          : 389973
% 0.40/0.57  
% 0.40/0.57  # -------------------------------------------------
% 0.40/0.57  # User time                : 0.226 s
% 0.40/0.57  # System time              : 0.010 s
% 0.40/0.57  # Total time               : 0.236 s
% 0.40/0.57  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
