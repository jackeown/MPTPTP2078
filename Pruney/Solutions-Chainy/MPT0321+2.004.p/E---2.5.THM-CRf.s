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
% DateTime   : Thu Dec  3 10:43:59 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  152 (2180 expanded)
%              Number of clauses        :  111 ( 973 expanded)
%              Number of leaves         :   20 ( 582 expanded)
%              Depth                    :   25
%              Number of atoms          :  279 (3919 expanded)
%              Number of equality atoms :  156 (2922 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_21,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k4_xboole_0(X38,X39)) = k3_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(X26,X27) != k1_xboole_0
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | k4_xboole_0(X26,X27) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_27,plain,(
    ! [X40,X41] : r1_tarski(X40,k2_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X35] : k4_xboole_0(X35,k1_xboole_0) = X35 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_37,plain,(
    ! [X36,X37] : k4_xboole_0(k2_xboole_0(X36,X37),X37) = k4_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_40,plain,(
    ! [X34] : k3_xboole_0(X34,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X32,X33] : k2_xboole_0(X32,k3_xboole_0(X32,X33)) = X32 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_47,plain,(
    ! [X49,X50,X51] :
      ( k2_zfmisc_1(k2_xboole_0(X49,X50),X51) = k2_xboole_0(k2_zfmisc_1(X49,X51),k2_zfmisc_1(X50,X51))
      & k2_zfmisc_1(X51,k2_xboole_0(X49,X50)) = k2_xboole_0(k2_zfmisc_1(X51,X49),k2_zfmisc_1(X51,X50)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_44]),c_0_45])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_52,plain,(
    ! [X52,X53,X54,X55] : k2_zfmisc_1(k3_xboole_0(X52,X53),k3_xboole_0(X54,X55)) = k3_xboole_0(k2_zfmisc_1(X52,X54),k2_zfmisc_1(X53,X55)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
    ! [X42,X43] :
      ( ( ~ r1_xboole_0(X42,X43)
        | k4_xboole_0(X42,X43) = X42 )
      & ( k4_xboole_0(X42,X43) != X42
        | r1_xboole_0(X42,X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k2_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_51,c_0_25])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1)) = k2_zfmisc_1(esk5_0,k2_xboole_0(X1,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_35])).

fof(c_0_62,plain,(
    ! [X44,X45] :
      ( ( k2_zfmisc_1(X44,X45) != k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 )
      & ( X45 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_63,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_43])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_42]),c_0_43]),c_0_35])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_29])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_29])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,X2),X3),k2_zfmisc_1(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),esk4_0) = k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_35]),c_0_68])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_43])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k2_xboole_0(X2,X4)))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_34]),c_0_43])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,k2_xboole_0(X1,esk6_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_61])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,esk4_0)) = k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_83,plain,
    ( X1 = X2
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X2)
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_73])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4),k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)),esk4_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_43])).

fof(c_0_87,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,esk4_0))
    | k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_82]),c_0_82]),c_0_82]),c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_93,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_53])).

fof(c_0_94,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X47,X46),k2_zfmisc_1(X48,X46))
        | X46 = k1_xboole_0
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(k2_zfmisc_1(X46,X47),k2_zfmisc_1(X46,X48))
        | X46 = k1_xboole_0
        | r1_tarski(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,k2_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_61])).

cnf(c_0_96,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])])).

fof(c_0_97,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k2_xboole_0(X28,X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_98,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(esk3_0,esk4_0)) = k2_zfmisc_1(k2_xboole_0(X1,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

cnf(c_0_102,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])).

cnf(c_0_104,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_43])).

cnf(c_0_105,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),esk6_0) = k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_101]),c_0_35])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0)) = k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_105]),c_0_54]),c_0_54])).

cnf(c_0_109,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_54])).

cnf(c_0_110,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X4))) = k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_34]),c_0_43])).

cnf(c_0_111,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k2_xboole_0(X1,esk5_0),esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_101])).

cnf(c_0_112,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_107])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109]),c_0_65])).

cnf(c_0_116,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_43])).

cnf(c_0_117,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_43])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_119,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_71]),c_0_100])).

cnf(c_0_120,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_73]),c_0_84])).

cnf(c_0_121,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_122,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_54])).

cnf(c_0_123,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_54])).

cnf(c_0_124,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk6_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_115]),c_0_43]),c_0_116]),c_0_117])).

cnf(c_0_125,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_118])).

cnf(c_0_126,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_127,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = k1_xboole_0
    | k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_86]),c_0_100])).

cnf(c_0_128,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_103])).

fof(c_0_129,plain,(
    ! [X30,X31] : r1_tarski(k3_xboole_0(X30,X31),X30) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,X1,esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_104]),c_0_82])]),c_0_121])).

cnf(c_0_131,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_99])).

cnf(c_0_132,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125])])).

cnf(c_0_133,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_126])).

cnf(c_0_134,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128]),c_0_43]),c_0_121])).

cnf(c_0_135,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_60])).

cnf(c_0_136,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_84])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_132]),c_0_133]),c_0_134])).

cnf(c_0_139,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(k2_zfmisc_1(X1,X4),k4_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5)))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_69])).

cnf(c_0_140,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_135,c_0_105])).

cnf(c_0_141,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_136,c_0_25])).

cnf(c_0_142,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_144,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_138]),c_0_103])])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_65]),c_0_43]),c_0_42]),c_0_43]),c_0_65]),c_0_43]),c_0_43]),c_0_121])).

cnf(c_0_146,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_141])).

cnf(c_0_147,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_142]),c_0_43])).

cnf(c_0_148,negated_conjecture,
    ( esk6_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_143,c_0_144])])).

cnf(c_0_149,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_145,c_0_124])).

cnf(c_0_150,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_148])).

cnf(c_0_151,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_125]),c_0_150]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.54/0.75  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.54/0.75  # and selection function SelectNegativeLiterals.
% 0.54/0.75  #
% 0.54/0.75  # Preprocessing time       : 0.028 s
% 0.54/0.75  # Presaturation interreduction done
% 0.54/0.75  
% 0.54/0.75  # Proof found!
% 0.54/0.75  # SZS status Theorem
% 0.54/0.75  # SZS output start CNFRefutation
% 0.54/0.75  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.54/0.75  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.54/0.75  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.54/0.75  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.54/0.75  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.54/0.75  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.54/0.75  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.54/0.75  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.54/0.75  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.54/0.75  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.54/0.75  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.54/0.75  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.54/0.75  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.54/0.75  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.54/0.75  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.54/0.75  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.54/0.75  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.54/0.75  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.54/0.75  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.54/0.75  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.54/0.75  fof(c_0_20, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.54/0.75  fof(c_0_21, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.54/0.75  fof(c_0_22, plain, ![X38, X39]:k4_xboole_0(X38,k4_xboole_0(X38,X39))=k3_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.54/0.75  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.75  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.75  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.54/0.75  fof(c_0_26, plain, ![X26, X27]:((k4_xboole_0(X26,X27)!=k1_xboole_0|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|k4_xboole_0(X26,X27)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.54/0.75  fof(c_0_27, plain, ![X40, X41]:r1_tarski(X40,k2_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.54/0.75  cnf(c_0_28, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_23])).
% 0.54/0.75  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.54/0.75  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.75  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.54/0.75  fof(c_0_32, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.54/0.75  cnf(c_0_33, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.54/0.75  cnf(c_0_34, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.54/0.75  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.54/0.75  fof(c_0_36, plain, ![X35]:k4_xboole_0(X35,k1_xboole_0)=X35, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.54/0.75  fof(c_0_37, plain, ![X36, X37]:k4_xboole_0(k2_xboole_0(X36,X37),X37)=k4_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.54/0.75  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.75  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.54/0.75  fof(c_0_40, plain, ![X34]:k3_xboole_0(X34,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.54/0.75  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))|~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2))), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 0.54/0.75  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.54/0.75  cnf(c_0_43, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.54/0.75  cnf(c_0_44, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.54/0.75  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_38])).
% 0.54/0.75  fof(c_0_46, plain, ![X32, X33]:k2_xboole_0(X32,k3_xboole_0(X32,X33))=X32, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.54/0.75  fof(c_0_47, plain, ![X49, X50, X51]:(k2_zfmisc_1(k2_xboole_0(X49,X50),X51)=k2_xboole_0(k2_zfmisc_1(X49,X51),k2_zfmisc_1(X50,X51))&k2_zfmisc_1(X51,k2_xboole_0(X49,X50))=k2_xboole_0(k2_zfmisc_1(X51,X49),k2_zfmisc_1(X51,X50))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.54/0.75  fof(c_0_48, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(esk3_0!=esk5_0|esk4_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.54/0.75  cnf(c_0_49, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.54/0.75  cnf(c_0_50, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3)))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_44]), c_0_45])).
% 0.54/0.75  cnf(c_0_51, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.54/0.75  fof(c_0_52, plain, ![X52, X53, X54, X55]:k2_zfmisc_1(k3_xboole_0(X52,X53),k3_xboole_0(X54,X55))=k3_xboole_0(k2_zfmisc_1(X52,X54),k2_zfmisc_1(X53,X55)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.54/0.75  cnf(c_0_53, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.54/0.75  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.54/0.75  fof(c_0_55, plain, ![X42, X43]:((~r1_xboole_0(X42,X43)|k4_xboole_0(X42,X43)=X42)&(k4_xboole_0(X42,X43)!=X42|r1_xboole_0(X42,X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.54/0.75  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_25])).
% 0.54/0.75  cnf(c_0_57, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k2_xboole_0(X3,k4_xboole_0(X3,X2))))), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 0.54/0.75  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_51, c_0_25])).
% 0.54/0.75  cnf(c_0_59, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.54/0.75  cnf(c_0_60, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.54/0.75  cnf(c_0_61, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1))=k2_zfmisc_1(esk5_0,k2_xboole_0(X1,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_35])).
% 0.54/0.75  fof(c_0_62, plain, ![X44, X45]:((k2_zfmisc_1(X44,X45)!=k1_xboole_0|(X44=k1_xboole_0|X45=k1_xboole_0))&((X44!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0)&(X45!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.54/0.75  fof(c_0_63, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk2_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk2_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.54/0.75  cnf(c_0_64, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.54/0.75  cnf(c_0_65, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_43])).
% 0.54/0.75  cnf(c_0_66, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_44]), c_0_42]), c_0_43]), c_0_35])).
% 0.54/0.75  cnf(c_0_67, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_58, c_0_29])).
% 0.54/0.75  cnf(c_0_68, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_58, c_0_29])).
% 0.54/0.75  cnf(c_0_69, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_25]), c_0_25]), c_0_25])).
% 0.54/0.75  cnf(c_0_70, plain, (k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,X2),X3),k2_zfmisc_1(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 0.54/0.75  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),esk4_0)=k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.54/0.75  cnf(c_0_72, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.54/0.75  cnf(c_0_73, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.75  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.54/0.75  cnf(c_0_75, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65])])).
% 0.54/0.75  cnf(c_0_76, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_35]), c_0_68])).
% 0.54/0.75  cnf(c_0_77, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_65]), c_0_43])).
% 0.54/0.75  cnf(c_0_78, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k2_xboole_0(X2,X4))))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_34]), c_0_43])).
% 0.54/0.75  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,k2_xboole_0(X1,esk6_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_61])).
% 0.54/0.75  cnf(c_0_80, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.75  cnf(c_0_81, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,esk4_0))=k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.54/0.75  cnf(c_0_82, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_72])).
% 0.54/0.75  cnf(c_0_83, plain, (X1=X2|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X2)|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_73])).
% 0.54/0.75  cnf(c_0_84, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.54/0.75  cnf(c_0_85, plain, (~r2_hidden(X1,k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4),k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.54/0.75  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)),esk4_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_43])).
% 0.54/0.75  fof(c_0_87, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.54/0.75  cnf(c_0_88, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,esk4_0))|k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.54/0.75  cnf(c_0_89, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_82]), c_0_82]), c_0_82]), c_0_84])).
% 0.54/0.75  cnf(c_0_90, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.54/0.75  cnf(c_0_91, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.54/0.75  cnf(c_0_92, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.54/0.75  cnf(c_0_93, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_31, c_0_53])).
% 0.54/0.75  fof(c_0_94, plain, ![X46, X47, X48]:((~r1_tarski(k2_zfmisc_1(X47,X46),k2_zfmisc_1(X48,X46))|X46=k1_xboole_0|r1_tarski(X47,X48))&(~r1_tarski(k2_zfmisc_1(X46,X47),k2_zfmisc_1(X46,X48))|X46=k1_xboole_0|r1_tarski(X47,X48))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.54/0.75  cnf(c_0_95, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,k2_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_31, c_0_61])).
% 0.54/0.75  cnf(c_0_96, negated_conjecture, (k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])])).
% 0.54/0.75  fof(c_0_97, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k2_xboole_0(X28,X29)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.54/0.75  cnf(c_0_98, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.54/0.75  cnf(c_0_99, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.54/0.75  cnf(c_0_100, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.54/0.75  cnf(c_0_101, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(X1,esk6_0),k2_zfmisc_1(esk3_0,esk4_0))=k2_zfmisc_1(k2_xboole_0(X1,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 0.54/0.75  cnf(c_0_102, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.54/0.75  cnf(c_0_103, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])).
% 0.54/0.75  cnf(c_0_104, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_43])).
% 0.54/0.75  cnf(c_0_105, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),esk6_0)=k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_101]), c_0_35])).
% 0.54/0.75  cnf(c_0_106, negated_conjecture, (k2_xboole_0(esk3_0,esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.54/0.75  cnf(c_0_107, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_35, c_0_104])).
% 0.54/0.75  cnf(c_0_108, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))=k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_105]), c_0_54]), c_0_54])).
% 0.54/0.75  cnf(c_0_109, negated_conjecture, (k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_54])).
% 0.54/0.75  cnf(c_0_110, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X4)))=k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_34]), c_0_43])).
% 0.54/0.75  cnf(c_0_111, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(k2_xboole_0(X1,esk5_0),esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_101])).
% 0.54/0.75  cnf(c_0_112, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.54/0.75  cnf(c_0_113, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_107])).
% 0.54/0.75  cnf(c_0_114, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.54/0.75  cnf(c_0_115, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109]), c_0_65])).
% 0.54/0.75  cnf(c_0_116, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))=k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_65]), c_0_43])).
% 0.54/0.75  cnf(c_0_117, negated_conjecture, (k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_43])).
% 0.54/0.75  cnf(c_0_118, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.54/0.75  cnf(c_0_119, negated_conjecture, (k2_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,k2_xboole_0(esk4_0,esk6_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_71]), c_0_100])).
% 0.54/0.75  cnf(c_0_120, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_73]), c_0_84])).
% 0.54/0.75  cnf(c_0_121, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.54/0.75  cnf(c_0_122, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_114, c_0_54])).
% 0.54/0.75  cnf(c_0_123, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_98, c_0_54])).
% 0.54/0.75  cnf(c_0_124, negated_conjecture, (k2_zfmisc_1(esk3_0,esk6_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_115]), c_0_43]), c_0_116]), c_0_117])).
% 0.54/0.75  cnf(c_0_125, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_118])).
% 0.54/0.75  cnf(c_0_126, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.54/0.75  cnf(c_0_127, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))=k1_xboole_0|k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_86]), c_0_100])).
% 0.54/0.75  cnf(c_0_128, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_103])).
% 0.54/0.75  fof(c_0_129, plain, ![X30, X31]:r1_tarski(k3_xboole_0(X30,X31),X30), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.54/0.75  cnf(c_0_130, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,X1,esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_104]), c_0_82])]), c_0_121])).
% 0.54/0.75  cnf(c_0_131, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_122, c_0_99])).
% 0.54/0.75  cnf(c_0_132, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_125])])).
% 0.54/0.75  cnf(c_0_133, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_126])).
% 0.54/0.75  cnf(c_0_134, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128]), c_0_43]), c_0_121])).
% 0.54/0.75  cnf(c_0_135, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_60])).
% 0.54/0.75  cnf(c_0_136, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.54/0.75  cnf(c_0_137, negated_conjecture, (r1_tarski(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_84])).
% 0.54/0.75  cnf(c_0_138, negated_conjecture, (r1_tarski(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_132]), c_0_133]), c_0_134])).
% 0.54/0.75  cnf(c_0_139, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))|~r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(k2_zfmisc_1(X1,X4),k4_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5))))), inference(spm,[status(thm)],[c_0_114, c_0_69])).
% 0.54/0.75  cnf(c_0_140, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk6_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_135, c_0_105])).
% 0.54/0.75  cnf(c_0_141, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_136, c_0_25])).
% 0.54/0.75  cnf(c_0_142, negated_conjecture, (k4_xboole_0(esk6_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_137])).
% 0.54/0.75  cnf(c_0_143, negated_conjecture, (esk3_0!=esk5_0|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.54/0.75  cnf(c_0_144, negated_conjecture, (esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_138]), c_0_103])])).
% 0.54/0.75  cnf(c_0_145, negated_conjecture, (r1_tarski(X1,esk6_0)|~r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_65]), c_0_43]), c_0_42]), c_0_43]), c_0_65]), c_0_43]), c_0_43]), c_0_121])).
% 0.54/0.75  cnf(c_0_146, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_91, c_0_141])).
% 0.54/0.75  cnf(c_0_147, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_142]), c_0_43])).
% 0.54/0.75  cnf(c_0_148, negated_conjecture, (esk6_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_143, c_0_144])])).
% 0.54/0.75  cnf(c_0_149, negated_conjecture, (r1_tarski(X1,esk6_0)|~r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_145, c_0_124])).
% 0.54/0.75  cnf(c_0_150, negated_conjecture, (~r1_tarski(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_148])).
% 0.54/0.75  cnf(c_0_151, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_125]), c_0_150]), ['proof']).
% 0.54/0.75  # SZS output end CNFRefutation
% 0.54/0.75  # Proof object total steps             : 152
% 0.54/0.75  # Proof object clause steps            : 111
% 0.54/0.75  # Proof object formula steps           : 41
% 0.54/0.75  # Proof object conjectures             : 48
% 0.54/0.75  # Proof object clause conjectures      : 45
% 0.54/0.75  # Proof object formula conjectures     : 3
% 0.54/0.75  # Proof object initial clauses used    : 31
% 0.54/0.75  # Proof object initial formulas used   : 20
% 0.54/0.75  # Proof object generating inferences   : 64
% 0.54/0.75  # Proof object simplifying inferences  : 81
% 0.54/0.75  # Training examples: 0 positive, 0 negative
% 0.54/0.75  # Parsed axioms                        : 20
% 0.54/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.75  # Initial clauses                      : 38
% 0.54/0.75  # Removed in clause preprocessing      : 1
% 0.54/0.75  # Initial clauses in saturation        : 37
% 0.54/0.75  # Processed clauses                    : 1942
% 0.54/0.75  # ...of these trivial                  : 147
% 0.54/0.75  # ...subsumed                          : 1331
% 0.54/0.75  # ...remaining for further processing  : 464
% 0.54/0.75  # Other redundant clauses eliminated   : 340
% 0.54/0.75  # Clauses deleted for lack of memory   : 0
% 0.54/0.75  # Backward-subsumed                    : 17
% 0.54/0.75  # Backward-rewritten                   : 177
% 0.54/0.75  # Generated clauses                    : 33252
% 0.54/0.75  # ...of the previous two non-trivial   : 27827
% 0.54/0.75  # Contextual simplify-reflections      : 7
% 0.54/0.75  # Paramodulations                      : 32907
% 0.54/0.75  # Factorizations                       : 0
% 0.54/0.75  # Equation resolutions                 : 340
% 0.54/0.75  # Propositional unsat checks           : 0
% 0.54/0.75  #    Propositional check models        : 0
% 0.54/0.75  #    Propositional check unsatisfiable : 0
% 0.54/0.75  #    Propositional clauses             : 0
% 0.54/0.75  #    Propositional clauses after purity: 0
% 0.54/0.75  #    Propositional unsat core size     : 0
% 0.54/0.75  #    Propositional preprocessing time  : 0.000
% 0.54/0.75  #    Propositional encoding time       : 0.000
% 0.54/0.75  #    Propositional solver time         : 0.000
% 0.54/0.75  #    Success case prop preproc time    : 0.000
% 0.54/0.75  #    Success case prop encoding time   : 0.000
% 0.54/0.75  #    Success case prop solver time     : 0.000
% 0.54/0.75  # Current number of processed clauses  : 222
% 0.54/0.75  #    Positive orientable unit clauses  : 77
% 0.54/0.75  #    Positive unorientable unit clauses: 6
% 0.54/0.75  #    Negative unit clauses             : 30
% 0.54/0.75  #    Non-unit-clauses                  : 109
% 0.54/0.75  # Current number of unprocessed clauses: 25395
% 0.54/0.75  # ...number of literals in the above   : 77795
% 0.54/0.75  # Current number of archived formulas  : 0
% 0.54/0.75  # Current number of archived clauses   : 236
% 0.54/0.75  # Clause-clause subsumption calls (NU) : 7216
% 0.54/0.75  # Rec. Clause-clause subsumption calls : 5032
% 0.54/0.75  # Non-unit clause-clause subsumptions  : 260
% 0.54/0.75  # Unit Clause-clause subsumption calls : 1171
% 0.54/0.75  # Rewrite failures with RHS unbound    : 0
% 0.54/0.75  # BW rewrite match attempts            : 284
% 0.54/0.75  # BW rewrite match successes           : 123
% 0.54/0.75  # Condensation attempts                : 0
% 0.54/0.75  # Condensation successes               : 0
% 0.54/0.75  # Termbank termtop insertions          : 571326
% 0.54/0.75  
% 0.54/0.75  # -------------------------------------------------
% 0.54/0.75  # User time                : 0.386 s
% 0.54/0.75  # System time              : 0.020 s
% 0.54/0.75  # Total time               : 0.407 s
% 0.54/0.75  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
