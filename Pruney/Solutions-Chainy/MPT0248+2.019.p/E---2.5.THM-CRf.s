%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  164 (226773 expanded)
%              Number of clauses        :  107 (88290 expanded)
%              Number of leaves         :   28 (68449 expanded)
%              Depth                    :   28
%              Number of atoms          :  327 (299453 expanded)
%              Number of equality atoms :  191 (255602 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t105_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & k4_xboole_0(X2,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_28,plain,(
    ! [X88,X89] : k3_tarski(k2_tarski(X88,X89)) = k2_xboole_0(X88,X89) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X59,X60] : k1_enumset1(X59,X59,X60) = k2_tarski(X59,X60) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X43,X44] : r1_tarski(X43,k2_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X61,X62,X63] : k2_enumset1(X61,X61,X62,X63) = k1_enumset1(X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,plain,(
    ! [X64,X65,X66,X67] : k3_enumset1(X64,X64,X65,X66,X67) = k2_enumset1(X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_36,plain,(
    ! [X68,X69,X70,X71,X72] : k4_enumset1(X68,X68,X69,X70,X71,X72) = k3_enumset1(X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_37,plain,(
    ! [X73,X74,X75,X76,X77,X78] : k5_enumset1(X73,X73,X74,X75,X76,X77,X78) = k4_enumset1(X73,X74,X75,X76,X77,X78) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_38,plain,(
    ! [X79,X80,X81,X82,X83,X84,X85] : k6_enumset1(X79,X79,X80,X81,X82,X83,X84,X85) = k5_enumset1(X79,X80,X81,X82,X83,X84,X85) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_39,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_xboole_0
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

fof(c_0_40,plain,(
    ! [X58] : k2_tarski(X58,X58) = k1_tarski(X58) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X51,X52,X53,X54,X55,X56] :
      ( ( ~ r2_hidden(X53,X52)
        | X53 = X51
        | X52 != k1_tarski(X51) )
      & ( X54 != X51
        | r2_hidden(X54,X52)
        | X52 != k1_tarski(X51) )
      & ( ~ r2_hidden(esk4_2(X55,X56),X56)
        | esk4_2(X55,X56) != X55
        | X56 = k1_tarski(X55) )
      & ( r2_hidden(esk4_2(X55,X56),X56)
        | esk4_2(X55,X56) = X55
        | X56 = k1_tarski(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_42,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk1_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk1_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_43,plain,(
    ! [X31] :
      ( X31 = k1_xboole_0
      | r2_hidden(esk3_1(X31),X31) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_33]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

fof(c_0_58,plain,(
    ! [X49,X50] : k3_xboole_0(X49,X50) = k5_xboole_0(k5_xboole_0(X49,X50),k2_xboole_0(X49,X50)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_59,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_52]),c_0_33]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_62,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk2_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk2_3(X23,X24,X25),X24)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X24)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_64,plain,(
    ! [X86,X87] :
      ( ( ~ r1_tarski(k1_tarski(X86),X87)
        | r2_hidden(X86,X87) )
      & ( ~ r2_hidden(X86,X87)
        | r1_tarski(k1_tarski(X86),X87) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_67,plain,(
    ! [X39,X40] :
      ( ~ r1_tarski(X39,X40)
      | k2_xboole_0(X39,X40) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_68,plain,(
    ! [X30] : k3_xboole_0(X30,X30) = X30 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_69,plain,(
    ! [X29] : k2_xboole_0(X29,X29) = X29 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_45]),c_0_46]),c_0_47])).

fof(c_0_72,plain,(
    ! [X45,X46,X47] : k5_xboole_0(k5_xboole_0(X45,X46),X47) = k5_xboole_0(X45,k5_xboole_0(X46,X47)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( esk3_1(esk6_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_75,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_78,plain,(
    ! [X48] : k5_xboole_0(X48,X48) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(k5_xboole_0(X2,X4),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_52]),c_0_33]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_83,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_74])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_71]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_92,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_61])).

fof(c_0_93,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k5_xboole_0(esk6_0,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_57])).

cnf(c_0_96,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_90]),c_0_91]),c_0_92])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_87]),c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_96])).

cnf(c_0_101,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_102,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_55])).

fof(c_0_103,plain,(
    ! [X37,X38] :
      ( ~ r2_xboole_0(X37,X38)
      | k4_xboole_0(X38,X37) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).

fof(c_0_104,plain,(
    ! [X35,X36] : k4_xboole_0(X35,X36) = k5_xboole_0(X35,k3_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_106,negated_conjecture,
    ( esk1_2(esk6_0,X1) = esk5_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( esk3_1(esk7_0) = esk5_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_102])).

cnf(c_0_108,plain,
    ( ~ r2_xboole_0(X1,X2)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != k1_xboole_0
    | ~ r2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109]),c_0_71]),c_0_48]),c_0_49]),c_0_50])).

fof(c_0_114,plain,(
    ! [X27,X28] :
      ( ( r1_tarski(X27,X28)
        | ~ r2_xboole_0(X27,X28) )
      & ( X27 != X28
        | ~ r2_xboole_0(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | X27 = X28
        | r2_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_115,plain,(
    ! [X41,X42] : k2_xboole_0(X41,k2_xboole_0(X41,X42)) = k2_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_116,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_117,negated_conjecture,
    ( esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_52]),c_0_52]),c_0_33]),c_0_33]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != k1_xboole_0
    | ~ r2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_113,c_0_81])).

cnf(c_0_119,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_122,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_116]),c_0_57])).

cnf(c_0_123,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_96])).

cnf(c_0_124,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_125,plain,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != k1_xboole_0
    | ~ r2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_118,c_0_98])).

cnf(c_0_126,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | r2_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_56])).

cnf(c_0_127,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_128,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_52]),c_0_33]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_129,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_122]),c_0_123])).

cnf(c_0_130,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_131,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(k5_xboole_0(X4,X2),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_71]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_132,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_91]),c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_96])).

cnf(c_0_134,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_52]),c_0_33]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_135,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X3,k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))))) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_81])])).

cnf(c_0_136,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_94,c_0_97])).

cnf(c_0_137,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_132,c_0_91])).

cnf(c_0_138,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133]),c_0_133])).

cnf(c_0_139,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_133])])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_92]),c_0_87]),c_0_136])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_133]),c_0_133]),c_0_94])).

cnf(c_0_142,negated_conjecture,
    ( k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_139])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k5_xboole_0(esk6_0,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_57])).

cnf(c_0_144,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_140,c_0_133])).

cnf(c_0_145,negated_conjecture,
    ( r2_hidden(esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_55]),c_0_142])).

cnf(c_0_146,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143,c_0_133]),c_0_94])).

cnf(c_0_147,negated_conjecture,
    ( r2_hidden(esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

fof(c_0_148,plain,(
    ! [X33,X34] :
      ( ( r1_tarski(X33,X34)
        | X33 != X34 )
      & ( r1_tarski(X34,X33)
        | X33 != X34 )
      & ( ~ r1_tarski(X33,X34)
        | ~ r1_tarski(X34,X33)
        | X33 = X34 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_149,negated_conjecture,
    ( r2_hidden(esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_55]),c_0_142])).

cnf(c_0_150,negated_conjecture,
    ( esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_147])).

cnf(c_0_151,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_153,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | ~ r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_151,c_0_61])).

cnf(c_0_154,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_145,c_0_150])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_152])).

cnf(c_0_156,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | ~ r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_133]),c_0_133])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_154])).

cnf(c_0_158,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_155]),c_0_91])).

cnf(c_0_159,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_157])])).

cnf(c_0_160,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158,c_0_159]),c_0_91])).

cnf(c_0_161,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_138,c_0_159])).

cnf(c_0_162,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_139,c_0_159])).

cnf(c_0_163,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_162]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.46  # and selection function GSelectMinInfpos.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.029 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.46  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.19/0.46  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.46  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.46  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.46  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.46  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.46  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.46  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.46  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.46  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.46  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.46  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.46  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.46  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.46  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.46  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.46  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.46  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.46  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.46  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.46  fof(t105_xboole_1, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&k4_xboole_0(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 0.19/0.46  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.46  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.46  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.19/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.46  fof(c_0_28, plain, ![X88, X89]:k3_tarski(k2_tarski(X88,X89))=k2_xboole_0(X88,X89), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.46  fof(c_0_29, plain, ![X59, X60]:k1_enumset1(X59,X59,X60)=k2_tarski(X59,X60), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.46  fof(c_0_30, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.19/0.46  fof(c_0_31, plain, ![X43, X44]:r1_tarski(X43,k2_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.46  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.46  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.46  fof(c_0_34, plain, ![X61, X62, X63]:k2_enumset1(X61,X61,X62,X63)=k1_enumset1(X61,X62,X63), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.46  fof(c_0_35, plain, ![X64, X65, X66, X67]:k3_enumset1(X64,X64,X65,X66,X67)=k2_enumset1(X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.46  fof(c_0_36, plain, ![X68, X69, X70, X71, X72]:k4_enumset1(X68,X68,X69,X70,X71,X72)=k3_enumset1(X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.46  fof(c_0_37, plain, ![X73, X74, X75, X76, X77, X78]:k5_enumset1(X73,X73,X74,X75,X76,X77,X78)=k4_enumset1(X73,X74,X75,X76,X77,X78), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.46  fof(c_0_38, plain, ![X79, X80, X81, X82, X83, X84, X85]:k6_enumset1(X79,X79,X80,X81,X82,X83,X84,X85)=k5_enumset1(X79,X80,X81,X82,X83,X84,X85), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.46  fof(c_0_39, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.19/0.46  fof(c_0_40, plain, ![X58]:k2_tarski(X58,X58)=k1_tarski(X58), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.46  fof(c_0_41, plain, ![X51, X52, X53, X54, X55, X56]:(((~r2_hidden(X53,X52)|X53=X51|X52!=k1_tarski(X51))&(X54!=X51|r2_hidden(X54,X52)|X52!=k1_tarski(X51)))&((~r2_hidden(esk4_2(X55,X56),X56)|esk4_2(X55,X56)!=X55|X56=k1_tarski(X55))&(r2_hidden(esk4_2(X55,X56),X56)|esk4_2(X55,X56)=X55|X56=k1_tarski(X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.46  fof(c_0_42, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk1_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk1_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.46  fof(c_0_43, plain, ![X31]:(X31=k1_xboole_0|r2_hidden(esk3_1(X31),X31)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.46  cnf(c_0_44, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  cnf(c_0_45, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.46  cnf(c_0_46, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.46  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.46  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.46  cnf(c_0_49, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.46  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.46  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.46  cnf(c_0_53, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.46  cnf(c_0_54, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.46  cnf(c_0_55, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_56, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_57, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_33]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.19/0.46  fof(c_0_58, plain, ![X49, X50]:k3_xboole_0(X49,X50)=k5_xboole_0(k5_xboole_0(X49,X50),k2_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.46  cnf(c_0_59, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_52]), c_0_33]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_60, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.46  cnf(c_0_61, negated_conjecture, (r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.46  fof(c_0_62, plain, ![X18, X19, X20, X21, X22, X23, X24, X25]:((((r2_hidden(X21,X18)|~r2_hidden(X21,X20)|X20!=k3_xboole_0(X18,X19))&(r2_hidden(X21,X19)|~r2_hidden(X21,X20)|X20!=k3_xboole_0(X18,X19)))&(~r2_hidden(X22,X18)|~r2_hidden(X22,X19)|r2_hidden(X22,X20)|X20!=k3_xboole_0(X18,X19)))&((~r2_hidden(esk2_3(X23,X24,X25),X25)|(~r2_hidden(esk2_3(X23,X24,X25),X23)|~r2_hidden(esk2_3(X23,X24,X25),X24))|X25=k3_xboole_0(X23,X24))&((r2_hidden(esk2_3(X23,X24,X25),X23)|r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k3_xboole_0(X23,X24))&(r2_hidden(esk2_3(X23,X24,X25),X24)|r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k3_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.46  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.46  fof(c_0_64, plain, ![X86, X87]:((~r1_tarski(k1_tarski(X86),X87)|r2_hidden(X86,X87))&(~r2_hidden(X86,X87)|r1_tarski(k1_tarski(X86),X87))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.46  cnf(c_0_65, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.19/0.46  cnf(c_0_66, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.46  fof(c_0_67, plain, ![X39, X40]:(~r1_tarski(X39,X40)|k2_xboole_0(X39,X40)=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.46  fof(c_0_68, plain, ![X30]:k3_xboole_0(X30,X30)=X30, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.46  fof(c_0_69, plain, ![X29]:k2_xboole_0(X29,X29)=X29, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.46  cnf(c_0_70, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.46  cnf(c_0_71, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_45]), c_0_46]), c_0_47])).
% 0.19/0.46  fof(c_0_72, plain, ![X45, X46, X47]:k5_xboole_0(k5_xboole_0(X45,X46),X47)=k5_xboole_0(X45,k5_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.46  cnf(c_0_73, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.46  cnf(c_0_74, negated_conjecture, (esk3_1(esk6_0)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.46  fof(c_0_75, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.46  cnf(c_0_76, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.46  cnf(c_0_77, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.46  fof(c_0_78, plain, ![X48]:k5_xboole_0(X48,X48)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.46  cnf(c_0_79, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.46  cnf(c_0_80, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(k5_xboole_0(X2,X4),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_81, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.46  cnf(c_0_82, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_52]), c_0_33]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_83, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_74])).
% 0.19/0.46  cnf(c_0_84, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.46  cnf(c_0_85, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_86, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_71]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_87, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.46  cnf(c_0_88, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_89, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.19/0.46  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.46  cnf(c_0_91, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.19/0.46  cnf(c_0_92, negated_conjecture, (k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_85, c_0_61])).
% 0.19/0.46  fof(c_0_93, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.46  cnf(c_0_94, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 0.19/0.46  cnf(c_0_95, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k5_xboole_0(esk6_0,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_89, c_0_57])).
% 0.19/0.46  cnf(c_0_96, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_90]), c_0_91]), c_0_92])).
% 0.19/0.46  cnf(c_0_97, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.19/0.46  cnf(c_0_98, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_87]), c_0_94])).
% 0.19/0.46  cnf(c_0_99, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), c_0_98])).
% 0.19/0.46  cnf(c_0_100, negated_conjecture, (esk6_0=k1_xboole_0|X1=esk5_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_96])).
% 0.19/0.46  cnf(c_0_101, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.46  cnf(c_0_102, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk3_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_99, c_0_55])).
% 0.19/0.46  fof(c_0_103, plain, ![X37, X38]:(~r2_xboole_0(X37,X38)|k4_xboole_0(X38,X37)!=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).
% 0.19/0.46  fof(c_0_104, plain, ![X35, X36]:k4_xboole_0(X35,X36)=k5_xboole_0(X35,k3_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.46  cnf(c_0_105, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.46  cnf(c_0_106, negated_conjecture, (esk1_2(esk6_0,X1)=esk5_0|esk6_0=k1_xboole_0|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.46  cnf(c_0_107, negated_conjecture, (esk3_1(esk7_0)=esk5_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_102])).
% 0.19/0.46  cnf(c_0_108, plain, (~r2_xboole_0(X1,X2)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.19/0.46  cnf(c_0_109, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.19/0.46  cnf(c_0_110, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.19/0.46  cnf(c_0_111, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_55, c_0_107])).
% 0.19/0.46  cnf(c_0_112, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.46  cnf(c_0_113, plain, (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))!=k1_xboole_0|~r2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109]), c_0_71]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  fof(c_0_114, plain, ![X27, X28]:(((r1_tarski(X27,X28)|~r2_xboole_0(X27,X28))&(X27!=X28|~r2_xboole_0(X27,X28)))&(~r1_tarski(X27,X28)|X27=X28|r2_xboole_0(X27,X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.46  fof(c_0_115, plain, ![X41, X42]:k2_xboole_0(X41,k2_xboole_0(X41,X42))=k2_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.19/0.46  cnf(c_0_116, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.19/0.46  cnf(c_0_117, negated_conjecture, (esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_52]), c_0_52]), c_0_33]), c_0_33]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 0.19/0.46  cnf(c_0_118, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))!=k1_xboole_0|~r2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_113, c_0_81])).
% 0.19/0.46  cnf(c_0_119, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.19/0.46  cnf(c_0_120, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.19/0.46  cnf(c_0_121, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.46  cnf(c_0_122, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_116]), c_0_57])).
% 0.19/0.46  cnf(c_0_123, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=esk6_0), inference(spm,[status(thm)],[c_0_117, c_0_96])).
% 0.19/0.46  cnf(c_0_124, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.46  cnf(c_0_125, plain, (k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))!=k1_xboole_0|~r2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_118, c_0_98])).
% 0.19/0.46  cnf(c_0_126, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|r2_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_119, c_0_56])).
% 0.19/0.46  cnf(c_0_127, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50])).
% 0.19/0.46  cnf(c_0_128, negated_conjecture, (esk7_0!=k1_xboole_0|esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_52]), c_0_33]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_129, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_122]), c_0_123])).
% 0.19/0.46  cnf(c_0_130, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.46  cnf(c_0_131, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(k5_xboole_0(X4,X2),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_71]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_132, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_91]), c_0_127])).
% 0.19/0.46  cnf(c_0_133, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_96])).
% 0.19/0.46  cnf(c_0_134, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_52]), c_0_33]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.46  cnf(c_0_135, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X3,k5_xboole_0(X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))))), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_81])])).
% 0.19/0.46  cnf(c_0_136, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_94, c_0_97])).
% 0.19/0.46  cnf(c_0_137, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_132, c_0_91])).
% 0.19/0.46  cnf(c_0_138, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_133]), c_0_133]), c_0_133]), c_0_133]), c_0_133]), c_0_133]), c_0_133])).
% 0.19/0.46  cnf(c_0_139, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_133])])).
% 0.19/0.46  cnf(c_0_140, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_92]), c_0_87]), c_0_136])).
% 0.19/0.46  cnf(c_0_141, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_133]), c_0_133]), c_0_94])).
% 0.19/0.46  cnf(c_0_142, negated_conjecture, (k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_139])).
% 0.19/0.46  cnf(c_0_143, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k5_xboole_0(esk6_0,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_135, c_0_57])).
% 0.19/0.46  cnf(c_0_144, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_140, c_0_133])).
% 0.19/0.46  cnf(c_0_145, negated_conjecture, (r2_hidden(esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_55]), c_0_142])).
% 0.19/0.46  cnf(c_0_146, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143, c_0_133]), c_0_94])).
% 0.19/0.46  cnf(c_0_147, negated_conjecture, (r2_hidden(esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.19/0.46  fof(c_0_148, plain, ![X33, X34]:(((r1_tarski(X33,X34)|X33!=X34)&(r1_tarski(X34,X33)|X33!=X34))&(~r1_tarski(X33,X34)|~r1_tarski(X34,X33)|X33=X34)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.46  cnf(c_0_149, negated_conjecture, (r2_hidden(esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_55]), c_0_142])).
% 0.19/0.46  cnf(c_0_150, negated_conjecture, (esk3_1(k5_xboole_0(esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk5_0), inference(spm,[status(thm)],[c_0_65, c_0_147])).
% 0.19/0.46  cnf(c_0_151, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_148])).
% 0.19/0.46  cnf(c_0_152, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_149, c_0_150])).
% 0.19/0.46  cnf(c_0_153, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|~r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_151, c_0_61])).
% 0.19/0.46  cnf(c_0_154, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_145, c_0_150])).
% 0.19/0.46  cnf(c_0_155, negated_conjecture, (r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_152])).
% 0.19/0.46  cnf(c_0_156, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|~r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_153, c_0_133]), c_0_133])).
% 0.19/0.46  cnf(c_0_157, negated_conjecture, (r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_154])).
% 0.19/0.46  cnf(c_0_158, negated_conjecture, (k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_155]), c_0_91])).
% 0.19/0.46  cnf(c_0_159, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_157])])).
% 0.19/0.46  cnf(c_0_160, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0))=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158, c_0_159]), c_0_91])).
% 0.19/0.46  cnf(c_0_161, negated_conjecture, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk7_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_138, c_0_159])).
% 0.19/0.46  cnf(c_0_162, negated_conjecture, (esk7_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_139, c_0_159])).
% 0.19/0.46  cnf(c_0_163, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_162]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 164
% 0.19/0.46  # Proof object clause steps            : 107
% 0.19/0.46  # Proof object formula steps           : 57
% 0.19/0.46  # Proof object conjectures             : 55
% 0.19/0.46  # Proof object clause conjectures      : 52
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 34
% 0.19/0.46  # Proof object initial formulas used   : 28
% 0.19/0.46  # Proof object generating inferences   : 38
% 0.19/0.46  # Proof object simplifying inferences  : 175
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 28
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 46
% 0.19/0.46  # Removed in clause preprocessing      : 10
% 0.19/0.46  # Initial clauses in saturation        : 36
% 0.19/0.46  # Processed clauses                    : 564
% 0.19/0.46  # ...of these trivial                  : 11
% 0.19/0.46  # ...subsumed                          : 313
% 0.19/0.46  # ...remaining for further processing  : 240
% 0.19/0.46  # Other redundant clauses eliminated   : 142
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 16
% 0.19/0.46  # Backward-rewritten                   : 95
% 0.19/0.46  # Generated clauses                    : 2897
% 0.19/0.46  # ...of the previous two non-trivial   : 2405
% 0.19/0.46  # Contextual simplify-reflections      : 3
% 0.19/0.46  # Paramodulations                      : 2734
% 0.19/0.46  # Factorizations                       : 22
% 0.19/0.46  # Equation resolutions                 : 142
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 86
% 0.19/0.46  #    Positive orientable unit clauses  : 22
% 0.19/0.46  #    Positive unorientable unit clauses: 4
% 0.19/0.46  #    Negative unit clauses             : 3
% 0.19/0.46  #    Non-unit-clauses                  : 57
% 0.19/0.46  # Current number of unprocessed clauses: 1838
% 0.19/0.46  # ...number of literals in the above   : 7728
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 156
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 2101
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 967
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 305
% 0.19/0.46  # Unit Clause-clause subsumption calls : 181
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 95
% 0.19/0.46  # BW rewrite match successes           : 64
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 57283
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.114 s
% 0.19/0.46  # System time              : 0.006 s
% 0.19/0.46  # Total time               : 0.120 s
% 0.19/0.46  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
