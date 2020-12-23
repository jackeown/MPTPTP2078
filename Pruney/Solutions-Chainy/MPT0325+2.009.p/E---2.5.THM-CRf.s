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
% DateTime   : Thu Dec  3 10:44:06 EST 2020

% Result     : Theorem 14.51s
% Output     : CNFRefutation 14.51s
% Verified   : 
% Statistics : Number of formulae       :  111 (2280 expanded)
%              Number of clauses        :   80 (1013 expanded)
%              Number of leaves         :   15 ( 624 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (4169 expanded)
%              Number of equality atoms :   82 (2100 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ( k4_xboole_0(X19,X20) != k1_xboole_0
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | k4_xboole_0(X19,X20) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_16,plain,(
    ! [X28] : k4_xboole_0(k1_xboole_0,X28) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X52,X53,X54,X55] : k2_zfmisc_1(k3_xboole_0(X52,X53),k3_xboole_0(X54,X55)) = k3_xboole_0(k2_zfmisc_1(X52,X54),k2_zfmisc_1(X53,X55)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_21,plain,(
    ! [X29,X30,X31,X32,X35,X36,X37,X38,X39,X40,X42,X43] :
      ( ( r2_hidden(esk3_4(X29,X30,X31,X32),X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k2_zfmisc_1(X29,X30) )
      & ( r2_hidden(esk4_4(X29,X30,X31,X32),X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k2_zfmisc_1(X29,X30) )
      & ( X32 = k4_tarski(esk3_4(X29,X30,X31,X32),esk4_4(X29,X30,X31,X32))
        | ~ r2_hidden(X32,X31)
        | X31 != k2_zfmisc_1(X29,X30) )
      & ( ~ r2_hidden(X36,X29)
        | ~ r2_hidden(X37,X30)
        | X35 != k4_tarski(X36,X37)
        | r2_hidden(X35,X31)
        | X31 != k2_zfmisc_1(X29,X30) )
      & ( ~ r2_hidden(esk5_3(X38,X39,X40),X40)
        | ~ r2_hidden(X42,X38)
        | ~ r2_hidden(X43,X39)
        | esk5_3(X38,X39,X40) != k4_tarski(X42,X43)
        | X40 = k2_zfmisc_1(X38,X39) )
      & ( r2_hidden(esk6_3(X38,X39,X40),X38)
        | r2_hidden(esk5_3(X38,X39,X40),X40)
        | X40 = k2_zfmisc_1(X38,X39) )
      & ( r2_hidden(esk7_3(X38,X39,X40),X39)
        | r2_hidden(esk5_3(X38,X39,X40),X40)
        | X40 = k2_zfmisc_1(X38,X39) )
      & ( esk5_3(X38,X39,X40) = k4_tarski(esk6_3(X38,X39,X40),esk7_3(X38,X39,X40))
        | r2_hidden(esk5_3(X38,X39,X40),X40)
        | X40 = k2_zfmisc_1(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_22,plain,(
    ! [X49,X50,X51] :
      ( ( r1_tarski(k2_zfmisc_1(X49,X51),k2_zfmisc_1(X50,X51))
        | ~ r1_tarski(X49,X50) )
      & ( r1_tarski(k2_zfmisc_1(X51,X49),k2_zfmisc_1(X51,X50))
        | ~ r1_tarski(X49,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X24] : k3_xboole_0(X24,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_26,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_27,plain,(
    ! [X21,X22,X23] :
      ( ( r1_tarski(X21,X22)
        | ~ r1_tarski(X21,k4_xboole_0(X22,X23)) )
      & ( r1_xboole_0(X21,X23)
        | ~ r1_tarski(X21,k4_xboole_0(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_33,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X25] : k4_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk2_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_30]),c_0_30])).

fof(c_0_45,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))
    & k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0
    & ( ~ r1_tarski(esk8_0,esk10_0)
      | ~ r1_tarski(esk9_0,esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_35])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X3,X2),k4_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r2_hidden(esk4_4(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))),X5),k4_xboole_0(X3,k4_xboole_0(X3,X4)))
    | ~ r2_hidden(X5,k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_24]),c_0_24])).

cnf(c_0_61,plain,
    ( X1 = X2
    | r2_hidden(esk2_1(X2),X2)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_53])).

fof(c_0_62,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X47,X46),k2_zfmisc_1(X48,X46))
        | X46 = k1_xboole_0
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(k2_zfmisc_1(X46,X47),k2_zfmisc_1(X46,X48))
        | X46 = k1_xboole_0
        | r1_tarski(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))),k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_56])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_50]),c_0_24]),c_0_24]),c_0_50]),c_0_24]),c_0_24]),c_0_50]),c_0_60])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_61]),c_0_60])).

cnf(c_0_68,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_50])).

cnf(c_0_70,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_35])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_73,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | r2_hidden(esk2_1(k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_53]),c_0_50])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk8_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_1(k2_zfmisc_1(esk10_0,esk11_0)),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_53]),c_0_50]),c_0_72])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_44])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_59]),c_0_50])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_54])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k4_xboole_0(esk9_0,k4_xboole_0(esk9_0,esk11_0))) = k2_zfmisc_1(esk8_0,esk9_0)
    | r2_hidden(esk2_1(k4_xboole_0(esk8_0,esk10_0)),k4_xboole_0(esk8_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_64]),c_0_50])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk8_0,esk10_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_76])).

cnf(c_0_83,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_85,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk2_1(k2_zfmisc_1(esk10_0,esk11_0))),esk11_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_77])).

cnf(c_0_88,plain,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)),k1_xboole_0)
    | k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k4_xboole_0(esk9_0,k4_xboole_0(esk9_0,esk11_0))) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_82]),c_0_60])).

cnf(c_0_90,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_91,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_35])).

cnf(c_0_92,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk2_1(esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,esk11_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_59])])).

cnf(c_0_95,plain,
    ( r2_hidden(esk3_4(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))),X5),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r2_hidden(X5,k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_43])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk11_0),X1),k2_zfmisc_1(esk11_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk2_1(k2_zfmisc_1(esk8_0,esk9_0)),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_53])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,esk11_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_94]),c_0_35])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk10_0)
    | ~ r1_tarski(esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_24]),c_0_24]),c_0_59]),c_0_50]),c_0_50]),c_0_24]),c_0_24]),c_0_50]),c_0_60])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk11_0),esk2_1(k2_zfmisc_1(esk8_0,esk9_0))),k2_zfmisc_1(esk11_0,k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_tarski(esk9_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_76])])).

cnf(c_0_106,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_67])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk2_1(k2_zfmisc_1(esk11_0,k2_zfmisc_1(esk8_0,esk9_0))),k2_zfmisc_1(esk11_0,k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_74]),c_0_108]),c_0_109]),c_0_74]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 14.51/14.69  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 14.51/14.69  # and selection function SelectNegativeLiterals.
% 14.51/14.69  #
% 14.51/14.69  # Preprocessing time       : 0.028 s
% 14.51/14.69  # Presaturation interreduction done
% 14.51/14.69  
% 14.51/14.69  # Proof found!
% 14.51/14.69  # SZS status Theorem
% 14.51/14.69  # SZS output start CNFRefutation
% 14.51/14.69  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.51/14.69  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 14.51/14.69  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.51/14.69  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 14.51/14.69  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.51/14.69  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.51/14.69  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 14.51/14.69  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 14.51/14.69  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 14.51/14.69  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 14.51/14.69  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 14.51/14.69  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 14.51/14.69  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 14.51/14.69  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.51/14.69  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 14.51/14.69  fof(c_0_15, plain, ![X19, X20]:((k4_xboole_0(X19,X20)!=k1_xboole_0|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|k4_xboole_0(X19,X20)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 14.51/14.69  fof(c_0_16, plain, ![X28]:k4_xboole_0(k1_xboole_0,X28)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 14.51/14.69  fof(c_0_17, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 14.51/14.69  fof(c_0_18, plain, ![X52, X53, X54, X55]:k2_zfmisc_1(k3_xboole_0(X52,X53),k3_xboole_0(X54,X55))=k3_xboole_0(k2_zfmisc_1(X52,X54),k2_zfmisc_1(X53,X55)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 14.51/14.69  fof(c_0_19, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 14.51/14.69  fof(c_0_20, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 14.51/14.69  fof(c_0_21, plain, ![X29, X30, X31, X32, X35, X36, X37, X38, X39, X40, X42, X43]:(((((r2_hidden(esk3_4(X29,X30,X31,X32),X29)|~r2_hidden(X32,X31)|X31!=k2_zfmisc_1(X29,X30))&(r2_hidden(esk4_4(X29,X30,X31,X32),X30)|~r2_hidden(X32,X31)|X31!=k2_zfmisc_1(X29,X30)))&(X32=k4_tarski(esk3_4(X29,X30,X31,X32),esk4_4(X29,X30,X31,X32))|~r2_hidden(X32,X31)|X31!=k2_zfmisc_1(X29,X30)))&(~r2_hidden(X36,X29)|~r2_hidden(X37,X30)|X35!=k4_tarski(X36,X37)|r2_hidden(X35,X31)|X31!=k2_zfmisc_1(X29,X30)))&((~r2_hidden(esk5_3(X38,X39,X40),X40)|(~r2_hidden(X42,X38)|~r2_hidden(X43,X39)|esk5_3(X38,X39,X40)!=k4_tarski(X42,X43))|X40=k2_zfmisc_1(X38,X39))&(((r2_hidden(esk6_3(X38,X39,X40),X38)|r2_hidden(esk5_3(X38,X39,X40),X40)|X40=k2_zfmisc_1(X38,X39))&(r2_hidden(esk7_3(X38,X39,X40),X39)|r2_hidden(esk5_3(X38,X39,X40),X40)|X40=k2_zfmisc_1(X38,X39)))&(esk5_3(X38,X39,X40)=k4_tarski(esk6_3(X38,X39,X40),esk7_3(X38,X39,X40))|r2_hidden(esk5_3(X38,X39,X40),X40)|X40=k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 14.51/14.69  fof(c_0_22, plain, ![X49, X50, X51]:((r1_tarski(k2_zfmisc_1(X49,X51),k2_zfmisc_1(X50,X51))|~r1_tarski(X49,X50))&(r1_tarski(k2_zfmisc_1(X51,X49),k2_zfmisc_1(X51,X50))|~r1_tarski(X49,X50))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 14.51/14.69  cnf(c_0_23, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 14.51/14.69  cnf(c_0_24, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 14.51/14.69  fof(c_0_25, plain, ![X24]:k3_xboole_0(X24,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 14.51/14.69  fof(c_0_26, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 14.51/14.69  fof(c_0_27, plain, ![X21, X22, X23]:((r1_tarski(X21,X22)|~r1_tarski(X21,k4_xboole_0(X22,X23)))&(r1_xboole_0(X21,X23)|~r1_tarski(X21,k4_xboole_0(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 14.51/14.69  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.51/14.69  cnf(c_0_29, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 14.51/14.69  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 14.51/14.69  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 14.51/14.69  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 14.51/14.69  cnf(c_0_33, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 14.51/14.69  cnf(c_0_34, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 14.51/14.69  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 14.51/14.69  cnf(c_0_36, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 14.51/14.69  fof(c_0_37, plain, ![X25]:k4_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t3_boole])).
% 14.51/14.69  cnf(c_0_38, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 14.51/14.69  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 14.51/14.69  fof(c_0_40, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk2_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 14.51/14.69  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 14.51/14.69  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 14.51/14.69  cnf(c_0_43, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30]), c_0_30])).
% 14.51/14.69  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_30]), c_0_30])).
% 14.51/14.69  fof(c_0_45, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))&(k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0&(~r1_tarski(esk8_0,esk10_0)|~r1_tarski(esk9_0,esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 14.51/14.69  cnf(c_0_46, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_33])).
% 14.51/14.69  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 14.51/14.69  cnf(c_0_48, plain, (r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 14.51/14.69  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_30])).
% 14.51/14.69  cnf(c_0_50, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 14.51/14.69  cnf(c_0_51, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_38, c_0_30])).
% 14.51/14.69  cnf(c_0_52, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_35])).
% 14.51/14.69  cnf(c_0_53, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 14.51/14.69  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 14.51/14.69  cnf(c_0_55, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X3,X2),k4_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_43])).
% 14.51/14.69  cnf(c_0_56, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 14.51/14.69  cnf(c_0_57, plain, (r2_hidden(esk4_4(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))),X5),k4_xboole_0(X3,k4_xboole_0(X3,X4)))|~r2_hidden(X5,k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))))), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 14.51/14.69  cnf(c_0_58, plain, (k4_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 14.51/14.69  cnf(c_0_59, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 14.51/14.69  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_24]), c_0_24])).
% 14.51/14.69  cnf(c_0_61, plain, (X1=X2|r2_hidden(esk2_1(X2),X2)|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_53, c_0_53])).
% 14.51/14.69  fof(c_0_62, plain, ![X46, X47, X48]:((~r1_tarski(k2_zfmisc_1(X47,X46),k2_zfmisc_1(X48,X46))|X46=k1_xboole_0|r1_tarski(X47,X48))&(~r1_tarski(k2_zfmisc_1(X46,X47),k2_zfmisc_1(X46,X48))|X46=k1_xboole_0|r1_tarski(X47,X48))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 14.51/14.69  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))),k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 14.51/14.69  cnf(c_0_64, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_56])).
% 14.51/14.69  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.51/14.69  cnf(c_0_66, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_50]), c_0_24]), c_0_24]), c_0_50]), c_0_24]), c_0_24]), c_0_50]), c_0_60])).
% 14.51/14.69  cnf(c_0_67, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_1(X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_61]), c_0_60])).
% 14.51/14.69  cnf(c_0_68, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 14.51/14.69  cnf(c_0_69, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk9_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_50])).
% 14.51/14.69  cnf(c_0_70, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_35])).
% 14.51/14.69  cnf(c_0_71, plain, (r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 14.51/14.69  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 14.51/14.69  cnf(c_0_73, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 14.51/14.69  cnf(c_0_74, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 14.51/14.69  cnf(c_0_75, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X4)))|r2_hidden(esk2_1(k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_53]), c_0_50])).
% 14.51/14.69  cnf(c_0_76, negated_conjecture, (r1_tarski(esk8_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])])).
% 14.51/14.69  cnf(c_0_77, negated_conjecture, (r2_hidden(esk2_1(k2_zfmisc_1(esk10_0,esk11_0)),k2_zfmisc_1(esk10_0,esk11_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_53]), c_0_50]), c_0_72])).
% 14.51/14.69  cnf(c_0_78, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_44])).
% 14.51/14.69  cnf(c_0_79, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))=k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_59]), c_0_50])).
% 14.51/14.69  cnf(c_0_80, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_54])).
% 14.51/14.69  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(esk8_0,k4_xboole_0(esk9_0,k4_xboole_0(esk9_0,esk11_0)))=k2_zfmisc_1(esk8_0,esk9_0)|r2_hidden(esk2_1(k4_xboole_0(esk8_0,esk10_0)),k4_xboole_0(esk8_0,esk10_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_64]), c_0_50])).
% 14.51/14.69  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk8_0,esk10_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_76])).
% 14.51/14.69  cnf(c_0_83, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 14.51/14.69  cnf(c_0_84, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 14.51/14.69  cnf(c_0_85, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 14.51/14.69  cnf(c_0_86, plain, (r2_hidden(esk2_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_53])).
% 14.51/14.69  cnf(c_0_87, negated_conjecture, (r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk2_1(k2_zfmisc_1(esk10_0,esk11_0))),esk11_0)), inference(spm,[status(thm)],[c_0_46, c_0_77])).
% 14.51/14.69  cnf(c_0_88, plain, (r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)),k1_xboole_0)|k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 14.51/14.69  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk8_0,k4_xboole_0(esk9_0,k4_xboole_0(esk9_0,esk11_0)))=k2_zfmisc_1(esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_82]), c_0_60])).
% 14.51/14.69  cnf(c_0_90, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_83])).
% 14.51/14.69  cnf(c_0_91, plain, (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_84, c_0_35])).
% 14.51/14.69  cnf(c_0_92, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).
% 14.51/14.69  cnf(c_0_93, negated_conjecture, (r2_hidden(esk2_1(esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 14.51/14.69  cnf(c_0_94, negated_conjecture, (r1_tarski(k4_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,esk11_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_59])])).
% 14.51/14.69  cnf(c_0_95, plain, (r2_hidden(esk3_4(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))),X5),k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~r2_hidden(X5,k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))))), inference(spm,[status(thm)],[c_0_90, c_0_43])).
% 14.51/14.70  cnf(c_0_96, plain, (k4_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),k2_zfmisc_1(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_91])).
% 14.51/14.70  cnf(c_0_97, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk11_0),X1),k2_zfmisc_1(esk11_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 14.51/14.70  cnf(c_0_98, negated_conjecture, (r2_hidden(esk2_1(k2_zfmisc_1(esk8_0,esk9_0)),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_53])).
% 14.51/14.70  cnf(c_0_99, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,esk11_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_94]), c_0_35])])).
% 14.51/14.70  cnf(c_0_100, negated_conjecture, (~r1_tarski(esk8_0,esk10_0)|~r1_tarski(esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 14.51/14.70  cnf(c_0_101, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_24]), c_0_24]), c_0_59]), c_0_50]), c_0_50]), c_0_24]), c_0_24]), c_0_50]), c_0_60])).
% 14.51/14.70  cnf(c_0_102, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk11_0),esk2_1(k2_zfmisc_1(esk8_0,esk9_0))),k2_zfmisc_1(esk11_0,k2_zfmisc_1(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 14.51/14.70  cnf(c_0_103, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 14.51/14.70  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,esk11_0))), inference(spm,[status(thm)],[c_0_23, c_0_99])).
% 14.51/14.70  cnf(c_0_105, negated_conjecture, (~r1_tarski(esk9_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_76])])).
% 14.51/14.70  cnf(c_0_106, plain, (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_101, c_0_67])).
% 14.51/14.70  cnf(c_0_107, negated_conjecture, (r2_hidden(esk2_1(k2_zfmisc_1(esk11_0,k2_zfmisc_1(esk8_0,esk9_0))),k2_zfmisc_1(esk11_0,k2_zfmisc_1(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_86, c_0_102])).
% 14.51/14.70  cnf(c_0_108, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])).
% 14.51/14.70  cnf(c_0_109, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_106])).
% 14.51/14.70  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_74]), c_0_108]), c_0_109]), c_0_74]), c_0_60]), ['proof']).
% 14.51/14.70  # SZS output end CNFRefutation
% 14.51/14.70  # Proof object total steps             : 111
% 14.51/14.70  # Proof object clause steps            : 80
% 14.51/14.70  # Proof object formula steps           : 31
% 14.51/14.70  # Proof object conjectures             : 26
% 14.51/14.70  # Proof object clause conjectures      : 23
% 14.51/14.70  # Proof object formula conjectures     : 3
% 14.51/14.70  # Proof object initial clauses used    : 24
% 14.51/14.70  # Proof object initial formulas used   : 15
% 14.51/14.70  # Proof object generating inferences   : 44
% 14.51/14.70  # Proof object simplifying inferences  : 61
% 14.51/14.70  # Training examples: 0 positive, 0 negative
% 14.51/14.70  # Parsed axioms                        : 15
% 14.51/14.70  # Removed by relevancy pruning/SinE    : 0
% 14.51/14.70  # Initial clauses                      : 31
% 14.51/14.70  # Removed in clause preprocessing      : 1
% 14.51/14.70  # Initial clauses in saturation        : 30
% 14.51/14.70  # Processed clauses                    : 23442
% 14.51/14.70  # ...of these trivial                  : 4659
% 14.51/14.70  # ...subsumed                          : 16111
% 14.51/14.70  # ...remaining for further processing  : 2672
% 14.51/14.70  # Other redundant clauses eliminated   : 3451
% 14.51/14.70  # Clauses deleted for lack of memory   : 0
% 14.51/14.70  # Backward-subsumed                    : 126
% 14.51/14.70  # Backward-rewritten                   : 1253
% 14.51/14.70  # Generated clauses                    : 1702030
% 14.51/14.70  # ...of the previous two non-trivial   : 1399552
% 14.51/14.70  # Contextual simplify-reflections      : 12
% 14.51/14.70  # Paramodulations                      : 1698507
% 14.51/14.70  # Factorizations                       : 66
% 14.51/14.70  # Equation resolutions                 : 3452
% 14.51/14.70  # Propositional unsat checks           : 0
% 14.51/14.70  #    Propositional check models        : 0
% 14.51/14.70  #    Propositional check unsatisfiable : 0
% 14.51/14.70  #    Propositional clauses             : 0
% 14.51/14.70  #    Propositional clauses after purity: 0
% 14.51/14.70  #    Propositional unsat core size     : 0
% 14.51/14.70  #    Propositional preprocessing time  : 0.000
% 14.51/14.70  #    Propositional encoding time       : 0.000
% 14.51/14.70  #    Propositional solver time         : 0.000
% 14.51/14.70  #    Success case prop preproc time    : 0.000
% 14.51/14.70  #    Success case prop encoding time   : 0.000
% 14.51/14.70  #    Success case prop solver time     : 0.000
% 14.51/14.70  # Current number of processed clauses  : 1252
% 14.51/14.70  #    Positive orientable unit clauses  : 333
% 14.51/14.70  #    Positive unorientable unit clauses: 9
% 14.51/14.70  #    Negative unit clauses             : 33
% 14.51/14.70  #    Non-unit-clauses                  : 877
% 14.51/14.70  # Current number of unprocessed clauses: 1372696
% 14.51/14.70  # ...number of literals in the above   : 6027860
% 14.51/14.70  # Current number of archived formulas  : 0
% 14.51/14.70  # Current number of archived clauses   : 1415
% 14.51/14.70  # Clause-clause subsumption calls (NU) : 265423
% 14.51/14.70  # Rec. Clause-clause subsumption calls : 117875
% 14.51/14.70  # Non-unit clause-clause subsumptions  : 7673
% 14.51/14.70  # Unit Clause-clause subsumption calls : 28230
% 14.51/14.70  # Rewrite failures with RHS unbound    : 0
% 14.51/14.70  # BW rewrite match attempts            : 7275
% 14.51/14.70  # BW rewrite match successes           : 277
% 14.51/14.70  # Condensation attempts                : 0
% 14.51/14.70  # Condensation successes               : 0
% 14.51/14.70  # Termbank termtop insertions          : 47020844
% 14.58/14.76  
% 14.58/14.76  # -------------------------------------------------
% 14.58/14.76  # User time                : 13.772 s
% 14.58/14.76  # System time              : 0.633 s
% 14.58/14.76  # Total time               : 14.406 s
% 14.58/14.76  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
