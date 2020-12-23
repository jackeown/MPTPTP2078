%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:07 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 884 expanded)
%              Number of clauses        :   90 ( 409 expanded)
%              Number of leaves         :   19 ( 224 expanded)
%              Depth                    :   27
%              Number of atoms          :  238 (1902 expanded)
%              Number of equality atoms :   84 ( 704 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t122_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,X21) != k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | k4_xboole_0(X20,X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X32,X33] : r1_xboole_0(k4_xboole_0(X32,X33),X33) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( ~ r1_xboole_0(X11,X12)
        | k3_xboole_0(X11,X12) = k1_xboole_0 )
      & ( k3_xboole_0(X11,X12) != k1_xboole_0
        | r1_xboole_0(X11,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_29,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X34,X35] : r1_tarski(X34,k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_33,plain,(
    ! [X25] : k2_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X22,X23,X24] :
      ( ( r1_tarski(X22,X23)
        | ~ r1_tarski(X22,k4_xboole_0(X23,X24)) )
      & ( r1_xboole_0(X22,X24)
        | ~ r1_tarski(X22,k4_xboole_0(X23,X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | ~ r1_xboole_0(X30,X31)
      | r1_xboole_0(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_31])])).

fof(c_0_44,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X41,X42,X43] :
      ( ( r1_tarski(k2_zfmisc_1(X41,X43),k2_zfmisc_1(X42,X43))
        | ~ r1_tarski(X41,X42) )
      & ( r1_tarski(k2_zfmisc_1(X43,X41),k2_zfmisc_1(X43,X42))
        | ~ r1_tarski(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34])).

fof(c_0_54,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k4_xboole_0(X1,k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( ~ r1_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_53])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_zfmisc_1(esk5_0,esk6_0)))
    | ~ r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_55])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

fof(c_0_61,plain,(
    ! [X13] :
      ( ~ v1_xboole_0(X13)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k4_xboole_0(X2,k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_64,plain,(
    ! [X36,X37] :
      ( ( k2_zfmisc_1(X36,X37) != k1_xboole_0
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0 )
      & ( X36 != k1_xboole_0
        | k2_zfmisc_1(X36,X37) = k1_xboole_0 )
      & ( X37 != k1_xboole_0
        | k2_zfmisc_1(X36,X37) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_67,plain,(
    ! [X47,X48,X49,X50] : k2_zfmisc_1(k3_xboole_0(X47,X48),k3_xboole_0(X49,X50)) = k3_xboole_0(k2_zfmisc_1(X47,X49),k2_zfmisc_1(X48,X50)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_72,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X39,X38),k2_zfmisc_1(X40,X38))
        | X38 = k1_xboole_0
        | r1_tarski(X39,X40) )
      & ( ~ r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X38,X40))
        | X38 = k1_xboole_0
        | r1_tarski(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_34]),c_0_71])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_79,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X3,X1),X4)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_42]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk5_0,esk4_0),k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk6_0)) = k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_75]),c_0_76])).

fof(c_0_81,plain,(
    ! [X28] : r1_tarski(k1_xboole_0,X28) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_82,plain,(
    ! [X44,X45,X46] :
      ( k2_zfmisc_1(k3_xboole_0(X44,X45),X46) = k3_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X46))
      & k2_zfmisc_1(X46,k3_xboole_0(X44,X45)) = k3_xboole_0(k2_zfmisc_1(X46,X44),k2_zfmisc_1(X46,X45)) ) ),
    inference(variable_rename,[status(thm)],[t122_zfmisc_1])).

cnf(c_0_83,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k4_xboole_0(X4,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_42]),c_0_78])).

cnf(c_0_88,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_41])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_46])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_93,plain,
    ( k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_94,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k4_xboole_0(X4,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_87]),c_0_43])).

cnf(c_0_95,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r2_hidden(X4,k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_88])).

cnf(c_0_96,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_92])).

cnf(c_0_99,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r2_hidden(X4,k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_93])).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,k2_zfmisc_1(X2,k4_xboole_0(X3,X4)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X5,X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_94])).

cnf(c_0_101,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k2_zfmisc_1(X4,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X5,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_71])).

cnf(c_0_102,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_103,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_105,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))
    | ~ r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_58])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,k4_xboole_0(X2,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_24])).

cnf(c_0_107,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0)
    | r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_86])).

cnf(c_0_110,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k4_xboole_0(X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_58])).

cnf(c_0_112,negated_conjecture,
    ( k3_xboole_0(esk4_0,X1) = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_108])).

cnf(c_0_113,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_109])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_115,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_53])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0)
    | v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_78]),c_0_78]),c_0_113])])).

cnf(c_0_117,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_118,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_71])).

cnf(c_0_119,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(X2,k2_zfmisc_1(esk5_0,esk6_0))) = k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_102])).

cnf(c_0_120,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_116]),c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_102]),c_0_117])).

cnf(c_0_124,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122])])).

cnf(c_0_126,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_102]),c_0_117])).

cnf(c_0_127,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_124]),c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127]),c_0_74]),c_0_127]),c_0_74]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.67/0.85  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.67/0.85  # and selection function SelectCQIPrecW.
% 0.67/0.85  #
% 0.67/0.85  # Preprocessing time       : 0.027 s
% 0.67/0.85  # Presaturation interreduction done
% 0.67/0.85  
% 0.67/0.85  # Proof found!
% 0.67/0.85  # SZS status Theorem
% 0.67/0.85  # SZS output start CNFRefutation
% 0.67/0.85  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.67/0.85  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.67/0.85  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.67/0.85  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.67/0.85  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.67/0.85  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.67/0.85  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.67/0.85  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.67/0.85  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.67/0.85  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.67/0.85  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.67/0.85  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.67/0.85  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.67/0.85  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.67/0.85  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.67/0.85  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.67/0.85  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.67/0.85  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.67/0.85  fof(t122_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_zfmisc_1)).
% 0.67/0.85  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.67/0.85  fof(c_0_20, plain, ![X20, X21]:((k4_xboole_0(X20,X21)!=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|k4_xboole_0(X20,X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.67/0.85  fof(c_0_21, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.67/0.85  fof(c_0_22, plain, ![X32, X33]:r1_xboole_0(k4_xboole_0(X32,X33),X33), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.67/0.85  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.67/0.85  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.67/0.85  fof(c_0_25, plain, ![X11, X12]:((~r1_xboole_0(X11,X12)|k3_xboole_0(X11,X12)=k1_xboole_0)&(k3_xboole_0(X11,X12)!=k1_xboole_0|r1_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.67/0.85  cnf(c_0_26, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.67/0.85  cnf(c_0_27, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.67/0.85  fof(c_0_28, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.67/0.85  fof(c_0_29, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.67/0.85  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.67/0.85  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k1_xboole_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.67/0.85  fof(c_0_32, plain, ![X34, X35]:r1_tarski(X34,k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.67/0.85  fof(c_0_33, plain, ![X25]:k2_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.67/0.85  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.67/0.85  cnf(c_0_35, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.67/0.85  cnf(c_0_36, negated_conjecture, (k3_xboole_0(k1_xboole_0,k2_zfmisc_1(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.67/0.85  fof(c_0_37, plain, ![X22, X23, X24]:((r1_tarski(X22,X23)|~r1_tarski(X22,k4_xboole_0(X23,X24)))&(r1_xboole_0(X22,X24)|~r1_tarski(X22,k4_xboole_0(X23,X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.67/0.85  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.67/0.85  cnf(c_0_39, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.67/0.85  fof(c_0_40, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|~r1_xboole_0(X30,X31)|r1_xboole_0(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.67/0.85  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.67/0.85  cnf(c_0_42, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_34])).
% 0.67/0.85  cnf(c_0_43, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_31])])).
% 0.67/0.85  fof(c_0_44, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.67/0.85  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.67/0.85  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.67/0.85  cnf(c_0_47, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.67/0.85  cnf(c_0_48, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.67/0.85  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.67/0.85  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.67/0.85  cnf(c_0_51, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.67/0.85  fof(c_0_52, plain, ![X41, X42, X43]:((r1_tarski(k2_zfmisc_1(X41,X43),k2_zfmisc_1(X42,X43))|~r1_tarski(X41,X42))&(r1_tarski(k2_zfmisc_1(X43,X41),k2_zfmisc_1(X43,X42))|~r1_tarski(X41,X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.67/0.85  cnf(c_0_53, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34])).
% 0.67/0.85  fof(c_0_54, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.67/0.85  cnf(c_0_55, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k4_xboole_0(X1,k2_zfmisc_1(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_51, c_0_24])).
% 0.67/0.85  cnf(c_0_56, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.67/0.85  cnf(c_0_57, plain, (~r1_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(X3,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_53])).
% 0.67/0.85  cnf(c_0_58, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.67/0.85  cnf(c_0_59, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(X2,k2_zfmisc_1(esk5_0,esk6_0)))|~r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_55])).
% 0.67/0.85  cnf(c_0_60, plain, (r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_56, c_0_50])).
% 0.67/0.85  fof(c_0_61, plain, ![X13]:(~v1_xboole_0(X13)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.67/0.85  cnf(c_0_62, plain, (v1_xboole_0(k4_xboole_0(X1,X2))|~r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.67/0.85  cnf(c_0_63, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k4_xboole_0(X2,k2_zfmisc_1(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.67/0.85  fof(c_0_64, plain, ![X36, X37]:((k2_zfmisc_1(X36,X37)!=k1_xboole_0|(X36=k1_xboole_0|X37=k1_xboole_0))&((X36!=k1_xboole_0|k2_zfmisc_1(X36,X37)=k1_xboole_0)&(X37!=k1_xboole_0|k2_zfmisc_1(X36,X37)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.67/0.85  cnf(c_0_65, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.67/0.85  cnf(c_0_66, negated_conjecture, (v1_xboole_0(k4_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k2_zfmisc_1(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.67/0.85  fof(c_0_67, plain, ![X47, X48, X49, X50]:k2_zfmisc_1(k3_xboole_0(X47,X48),k3_xboole_0(X49,X50))=k3_xboole_0(k2_zfmisc_1(X47,X49),k2_zfmisc_1(X48,X50)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.67/0.85  cnf(c_0_68, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.67/0.85  cnf(c_0_69, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.67/0.85  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.67/0.85  cnf(c_0_71, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.67/0.85  fof(c_0_72, plain, ![X38, X39, X40]:((~r1_tarski(k2_zfmisc_1(X39,X38),k2_zfmisc_1(X40,X38))|X38=k1_xboole_0|r1_tarski(X39,X40))&(~r1_tarski(k2_zfmisc_1(X38,X39),k2_zfmisc_1(X38,X40))|X38=k1_xboole_0|r1_tarski(X39,X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.67/0.85  cnf(c_0_73, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.67/0.85  cnf(c_0_74, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_68])).
% 0.67/0.85  cnf(c_0_75, negated_conjecture, (r1_tarski(k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.67/0.85  cnf(c_0_76, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_34]), c_0_71])).
% 0.67/0.85  cnf(c_0_77, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.67/0.85  cnf(c_0_78, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_73])).
% 0.67/0.85  cnf(c_0_79, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X3,X1),X4))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_42]), c_0_74])).
% 0.67/0.85  cnf(c_0_80, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk5_0,esk4_0),k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk6_0))=k2_zfmisc_1(k4_xboole_0(esk3_0,X1),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_75]), c_0_76])).
% 0.67/0.85  fof(c_0_81, plain, ![X28]:r1_tarski(k1_xboole_0,X28), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.67/0.85  fof(c_0_82, plain, ![X44, X45, X46]:(k2_zfmisc_1(k3_xboole_0(X44,X45),X46)=k3_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X46))&k2_zfmisc_1(X46,k3_xboole_0(X44,X45))=k3_xboole_0(k2_zfmisc_1(X46,X44),k2_zfmisc_1(X46,X45))), inference(variable_rename,[status(thm)],[t122_zfmisc_1])).
% 0.67/0.85  cnf(c_0_83, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.67/0.85  cnf(c_0_84, plain, (X1=k1_xboole_0|r1_tarski(X2,k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.67/0.85  cnf(c_0_85, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.67/0.85  cnf(c_0_86, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.67/0.85  cnf(c_0_87, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k4_xboole_0(X4,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_42]), c_0_78])).
% 0.67/0.85  cnf(c_0_88, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.67/0.85  cnf(c_0_89, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_83, c_0_41])).
% 0.67/0.85  cnf(c_0_90, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_51, c_0_38])).
% 0.67/0.85  cnf(c_0_91, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_46])).
% 0.67/0.85  cnf(c_0_92, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=k1_xboole_0|r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 0.67/0.85  cnf(c_0_93, plain, (k2_zfmisc_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.67/0.85  cnf(c_0_94, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k4_xboole_0(X4,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_87]), c_0_43])).
% 0.67/0.85  cnf(c_0_95, plain, (~r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r2_hidden(X4,k2_zfmisc_1(k3_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_35, c_0_88])).
% 0.67/0.85  cnf(c_0_96, plain, (r1_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.67/0.85  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_91])).
% 0.67/0.85  cnf(c_0_98, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_92])).
% 0.67/0.85  cnf(c_0_99, plain, (~r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r2_hidden(X4,k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_93])).
% 0.67/0.85  cnf(c_0_100, plain, (r1_xboole_0(X1,k2_zfmisc_1(X2,k4_xboole_0(X3,X4)))|~r1_tarski(X1,k2_zfmisc_1(X5,X4))), inference(spm,[status(thm)],[c_0_47, c_0_94])).
% 0.67/0.85  cnf(c_0_101, plain, (~r1_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k2_zfmisc_1(X4,k3_xboole_0(X2,X3)))|~r2_hidden(X5,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_95, c_0_71])).
% 0.67/0.85  cnf(c_0_102, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_24])).
% 0.67/0.85  cnf(c_0_103, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,k2_xboole_0(X2,X4)))), inference(spm,[status(thm)],[c_0_47, c_0_96])).
% 0.67/0.85  cnf(c_0_104, negated_conjecture, (r1_tarski(esk3_0,esk5_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.67/0.85  cnf(c_0_105, plain, (v1_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))|~r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_99, c_0_58])).
% 0.67/0.85  cnf(c_0_106, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,k4_xboole_0(X2,esk6_0)))), inference(spm,[status(thm)],[c_0_100, c_0_24])).
% 0.67/0.85  cnf(c_0_107, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)))|~r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.67/0.85  cnf(c_0_108, negated_conjecture, (r1_tarski(esk3_0,esk5_0)|r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.67/0.85  cnf(c_0_109, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_86])).
% 0.67/0.85  cnf(c_0_110, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,k4_xboole_0(X1,esk6_0))))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.67/0.85  cnf(c_0_111, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))|~r1_xboole_0(k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(esk5_0,k3_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_107, c_0_58])).
% 0.67/0.85  cnf(c_0_112, negated_conjecture, (k3_xboole_0(esk4_0,X1)=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_108])).
% 0.67/0.85  cnf(c_0_113, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_109])).
% 0.67/0.85  cnf(c_0_114, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.67/0.85  cnf(c_0_115, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_110, c_0_53])).
% 0.67/0.85  cnf(c_0_116, negated_conjecture, (r1_tarski(esk3_0,esk5_0)|v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_78]), c_0_78]), c_0_113])])).
% 0.67/0.85  cnf(c_0_117, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.67/0.85  cnf(c_0_118, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_71])).
% 0.67/0.85  cnf(c_0_119, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(esk3_0,esk4_0)),k2_zfmisc_1(X2,k2_zfmisc_1(esk5_0,esk6_0)))=k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_71, c_0_102])).
% 0.67/0.85  cnf(c_0_120, negated_conjecture, (k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_115])).
% 0.67/0.85  cnf(c_0_121, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.67/0.85  cnf(c_0_122, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_116]), c_0_117])).
% 0.67/0.85  cnf(c_0_123, negated_conjecture, (k3_xboole_0(X1,X2)=k1_xboole_0|k2_zfmisc_1(k3_xboole_0(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_102]), c_0_117])).
% 0.67/0.85  cnf(c_0_124, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_120])).
% 0.67/0.85  cnf(c_0_125, negated_conjecture, (~r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122])])).
% 0.67/0.85  cnf(c_0_126, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_102]), c_0_117])).
% 0.67/0.85  cnf(c_0_127, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_124]), c_0_125])).
% 0.67/0.85  cnf(c_0_128, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127]), c_0_74]), c_0_127]), c_0_74]), c_0_74])]), ['proof']).
% 0.67/0.85  # SZS output end CNFRefutation
% 0.67/0.85  # Proof object total steps             : 129
% 0.67/0.85  # Proof object clause steps            : 90
% 0.67/0.85  # Proof object formula steps           : 39
% 0.67/0.85  # Proof object conjectures             : 39
% 0.67/0.85  # Proof object clause conjectures      : 36
% 0.67/0.85  # Proof object formula conjectures     : 3
% 0.67/0.85  # Proof object initial clauses used    : 26
% 0.67/0.85  # Proof object initial formulas used   : 19
% 0.67/0.85  # Proof object generating inferences   : 60
% 0.67/0.85  # Proof object simplifying inferences  : 31
% 0.67/0.85  # Training examples: 0 positive, 0 negative
% 0.67/0.85  # Parsed axioms                        : 19
% 0.67/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.67/0.85  # Initial clauses                      : 31
% 0.67/0.85  # Removed in clause preprocessing      : 0
% 0.67/0.85  # Initial clauses in saturation        : 31
% 0.67/0.85  # Processed clauses                    : 3426
% 0.67/0.85  # ...of these trivial                  : 145
% 0.67/0.85  # ...subsumed                          : 2221
% 0.67/0.85  # ...remaining for further processing  : 1060
% 0.67/0.85  # Other redundant clauses eliminated   : 6
% 0.67/0.85  # Clauses deleted for lack of memory   : 0
% 0.67/0.85  # Backward-subsumed                    : 35
% 0.67/0.85  # Backward-rewritten                   : 669
% 0.67/0.85  # Generated clauses                    : 37825
% 0.67/0.85  # ...of the previous two non-trivial   : 30926
% 0.67/0.85  # Contextual simplify-reflections      : 0
% 0.67/0.85  # Paramodulations                      : 37819
% 0.67/0.85  # Factorizations                       : 0
% 0.67/0.85  # Equation resolutions                 : 6
% 0.67/0.85  # Propositional unsat checks           : 0
% 0.67/0.85  #    Propositional check models        : 0
% 0.67/0.85  #    Propositional check unsatisfiable : 0
% 0.67/0.85  #    Propositional clauses             : 0
% 0.67/0.85  #    Propositional clauses after purity: 0
% 0.67/0.85  #    Propositional unsat core size     : 0
% 0.67/0.85  #    Propositional preprocessing time  : 0.000
% 0.67/0.85  #    Propositional encoding time       : 0.000
% 0.67/0.85  #    Propositional solver time         : 0.000
% 0.67/0.85  #    Success case prop preproc time    : 0.000
% 0.67/0.85  #    Success case prop encoding time   : 0.000
% 0.67/0.85  #    Success case prop solver time     : 0.000
% 0.67/0.85  # Current number of processed clauses  : 323
% 0.67/0.85  #    Positive orientable unit clauses  : 99
% 0.67/0.85  #    Positive unorientable unit clauses: 11
% 0.67/0.85  #    Negative unit clauses             : 2
% 0.67/0.85  #    Non-unit-clauses                  : 211
% 0.67/0.85  # Current number of unprocessed clauses: 27221
% 0.67/0.85  # ...number of literals in the above   : 46708
% 0.67/0.85  # Current number of archived formulas  : 0
% 0.67/0.85  # Current number of archived clauses   : 735
% 0.67/0.85  # Clause-clause subsumption calls (NU) : 69570
% 0.67/0.85  # Rec. Clause-clause subsumption calls : 57348
% 0.67/0.85  # Non-unit clause-clause subsumptions  : 978
% 0.67/0.85  # Unit Clause-clause subsumption calls : 572
% 0.67/0.85  # Rewrite failures with RHS unbound    : 0
% 0.67/0.85  # BW rewrite match attempts            : 390
% 0.67/0.85  # BW rewrite match successes           : 212
% 0.67/0.85  # Condensation attempts                : 0
% 0.67/0.85  # Condensation successes               : 0
% 0.67/0.85  # Termbank termtop insertions          : 733057
% 0.67/0.85  
% 0.67/0.85  # -------------------------------------------------
% 0.67/0.85  # User time                : 0.487 s
% 0.67/0.85  # System time              : 0.029 s
% 0.67/0.85  # Total time               : 0.516 s
% 0.67/0.85  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
