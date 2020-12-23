%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:49 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 312 expanded)
%              Number of clauses        :   40 ( 142 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 ( 720 expanded)
%              Number of equality atoms :   75 ( 289 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t130_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(X2),X1) != k1_xboole_0
        & k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X12] :
      ( ~ v1_xboole_0(X12)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_14,plain,(
    v1_xboole_0(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_18,plain,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_18])).

fof(c_0_21,plain,(
    ! [X42,X43,X44,X45,X48,X49,X50,X51,X52,X53,X55,X56] :
      ( ( r2_hidden(esk3_4(X42,X43,X44,X45),X42)
        | ~ r2_hidden(X45,X44)
        | X44 != k2_zfmisc_1(X42,X43) )
      & ( r2_hidden(esk4_4(X42,X43,X44,X45),X43)
        | ~ r2_hidden(X45,X44)
        | X44 != k2_zfmisc_1(X42,X43) )
      & ( X45 = k4_tarski(esk3_4(X42,X43,X44,X45),esk4_4(X42,X43,X44,X45))
        | ~ r2_hidden(X45,X44)
        | X44 != k2_zfmisc_1(X42,X43) )
      & ( ~ r2_hidden(X49,X42)
        | ~ r2_hidden(X50,X43)
        | X48 != k4_tarski(X49,X50)
        | r2_hidden(X48,X44)
        | X44 != k2_zfmisc_1(X42,X43) )
      & ( ~ r2_hidden(esk5_3(X51,X52,X53),X53)
        | ~ r2_hidden(X55,X51)
        | ~ r2_hidden(X56,X52)
        | esk5_3(X51,X52,X53) != k4_tarski(X55,X56)
        | X53 = k2_zfmisc_1(X51,X52) )
      & ( r2_hidden(esk6_3(X51,X52,X53),X51)
        | r2_hidden(esk5_3(X51,X52,X53),X53)
        | X53 = k2_zfmisc_1(X51,X52) )
      & ( r2_hidden(esk7_3(X51,X52,X53),X52)
        | r2_hidden(esk5_3(X51,X52,X53),X53)
        | X53 = k2_zfmisc_1(X51,X52) )
      & ( esk5_3(X51,X52,X53) = k4_tarski(esk6_3(X51,X52,X53),esk7_3(X51,X52,X53))
        | r2_hidden(esk5_3(X51,X52,X53),X53)
        | X53 = k2_zfmisc_1(X51,X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( X1 = k2_zfmisc_1(k1_xboole_0,X2)
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_25,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(X2),X1) != k1_xboole_0
          & k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t130_zfmisc_1])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_26])).

fof(c_0_30,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    & ( k2_zfmisc_1(k1_tarski(esk9_0),esk8_0) = k1_xboole_0
      | k2_zfmisc_1(esk8_0,k1_tarski(esk9_0)) = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_31,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,plain,(
    ! [X59,X60,X61,X62] :
      ( ( r2_hidden(X59,X61)
        | ~ r2_hidden(k4_tarski(X59,X60),k2_zfmisc_1(X61,k1_tarski(X62))) )
      & ( X60 = X62
        | ~ r2_hidden(k4_tarski(X59,X60),k2_zfmisc_1(X61,k1_tarski(X62))) )
      & ( ~ r2_hidden(X59,X61)
        | X60 != X62
        | r2_hidden(k4_tarski(X59,X60),k2_zfmisc_1(X61,k1_tarski(X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk5_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X4,X1))
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(k1_tarski(esk9_0),esk8_0) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,k1_tarski(esk9_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))
    | ~ r2_hidden(X1,X2)
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_1(X2),esk5_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X2,X1))
    | v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) = k1_xboole_0
    | k2_zfmisc_1(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk8_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))
    | X3 != X4
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,esk1_1(X2)),k2_zfmisc_1(X3,X2))
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) = k1_xboole_0
    | v1_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_22])).

cnf(c_0_56,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_3(k1_xboole_0,X2,X1),esk1_1(X3)),k2_zfmisc_1(X1,X3))
    | v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) = k1_xboole_0
    | k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_55])).

cnf(c_0_60,plain,
    ( X1 = k2_zfmisc_1(X2,k1_xboole_0)
    | r2_hidden(esk5_3(X2,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_56])).

cnf(c_0_61,plain,
    ( r2_hidden(k4_tarski(esk1_1(X1),X2),k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52]),c_0_22]),c_0_15])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_22])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_64])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:15:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.21/0.50  # and selection function GSelectMinInfpos.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.042 s
% 0.21/0.50  # Presaturation interreduction done
% 0.21/0.50  
% 0.21/0.50  # Proof found!
% 0.21/0.50  # SZS status Theorem
% 0.21/0.50  # SZS output start CNFRefutation
% 0.21/0.50  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.21/0.50  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.21/0.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.50  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.21/0.50  fof(t130_zfmisc_1, conjecture, ![X1, X2]:(X1!=k1_xboole_0=>(k2_zfmisc_1(k1_tarski(X2),X1)!=k1_xboole_0&k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 0.21/0.50  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.50  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.50  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.50  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.50  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.50  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.50  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.50  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.21/0.50  fof(c_0_13, plain, ![X12]:(~v1_xboole_0(X12)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.21/0.50  fof(c_0_14, plain, v1_xboole_0(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.21/0.50  cnf(c_0_15, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.50  cnf(c_0_16, plain, (v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.50  fof(c_0_17, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.50  cnf(c_0_18, plain, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.50  cnf(c_0_19, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_20, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_16, c_0_18])).
% 0.21/0.50  fof(c_0_21, plain, ![X42, X43, X44, X45, X48, X49, X50, X51, X52, X53, X55, X56]:(((((r2_hidden(esk3_4(X42,X43,X44,X45),X42)|~r2_hidden(X45,X44)|X44!=k2_zfmisc_1(X42,X43))&(r2_hidden(esk4_4(X42,X43,X44,X45),X43)|~r2_hidden(X45,X44)|X44!=k2_zfmisc_1(X42,X43)))&(X45=k4_tarski(esk3_4(X42,X43,X44,X45),esk4_4(X42,X43,X44,X45))|~r2_hidden(X45,X44)|X44!=k2_zfmisc_1(X42,X43)))&(~r2_hidden(X49,X42)|~r2_hidden(X50,X43)|X48!=k4_tarski(X49,X50)|r2_hidden(X48,X44)|X44!=k2_zfmisc_1(X42,X43)))&((~r2_hidden(esk5_3(X51,X52,X53),X53)|(~r2_hidden(X55,X51)|~r2_hidden(X56,X52)|esk5_3(X51,X52,X53)!=k4_tarski(X55,X56))|X53=k2_zfmisc_1(X51,X52))&(((r2_hidden(esk6_3(X51,X52,X53),X51)|r2_hidden(esk5_3(X51,X52,X53),X53)|X53=k2_zfmisc_1(X51,X52))&(r2_hidden(esk7_3(X51,X52,X53),X52)|r2_hidden(esk5_3(X51,X52,X53),X53)|X53=k2_zfmisc_1(X51,X52)))&(esk5_3(X51,X52,X53)=k4_tarski(esk6_3(X51,X52,X53),esk7_3(X51,X52,X53))|r2_hidden(esk5_3(X51,X52,X53),X53)|X53=k2_zfmisc_1(X51,X52))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.21/0.50  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.50  cnf(c_0_23, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.50  cnf(c_0_24, plain, (X1=k2_zfmisc_1(k1_xboole_0,X2)|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.50  cnf(c_0_25, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.50  cnf(c_0_26, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_24])).
% 0.21/0.50  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(X1!=k1_xboole_0=>(k2_zfmisc_1(k1_tarski(X2),X1)!=k1_xboole_0&k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t130_zfmisc_1])).
% 0.21/0.50  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).
% 0.21/0.50  cnf(c_0_29, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[c_0_24, c_0_26])).
% 0.21/0.50  fof(c_0_30, negated_conjecture, (esk8_0!=k1_xboole_0&(k2_zfmisc_1(k1_tarski(esk9_0),esk8_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,k1_tarski(esk9_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.21/0.50  fof(c_0_31, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.50  fof(c_0_32, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.50  fof(c_0_33, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.50  fof(c_0_34, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.50  fof(c_0_35, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.50  fof(c_0_36, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.50  fof(c_0_37, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.50  fof(c_0_38, plain, ![X59, X60, X61, X62]:(((r2_hidden(X59,X61)|~r2_hidden(k4_tarski(X59,X60),k2_zfmisc_1(X61,k1_tarski(X62))))&(X60=X62|~r2_hidden(k4_tarski(X59,X60),k2_zfmisc_1(X61,k1_tarski(X62)))))&(~r2_hidden(X59,X61)|X60!=X62|r2_hidden(k4_tarski(X59,X60),k2_zfmisc_1(X61,k1_tarski(X62))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.21/0.50  cnf(c_0_39, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(X2,esk5_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X4,X1))|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.50  cnf(c_0_40, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(k1_tarski(esk9_0),esk8_0)=k1_xboole_0|k2_zfmisc_1(esk8_0,k1_tarski(esk9_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.50  cnf(c_0_42, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.50  cnf(c_0_43, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.50  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.50  cnf(c_0_45, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.50  cnf(c_0_46, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.50  cnf(c_0_47, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.50  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.50  cnf(c_0_49, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))|~r2_hidden(X1,X2)|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.50  cnf(c_0_50, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk1_1(X2),esk5_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X2,X1))|v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.50  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(esk8_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))=k1_xboole_0|k2_zfmisc_1(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk8_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 0.21/0.50  cnf(c_0_52, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.50  cnf(c_0_53, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))|X3!=X4|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 0.21/0.50  cnf(c_0_54, plain, (r2_hidden(k4_tarski(X1,esk1_1(X2)),k2_zfmisc_1(X3,X2))|v1_xboole_0(X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_40])).
% 0.21/0.50  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(esk8_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))=k1_xboole_0|v1_xboole_0(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_22])).
% 0.21/0.50  cnf(c_0_56, plain, (r2_hidden(esk7_3(X1,X2,X3),X2)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.50  cnf(c_0_57, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_53])).
% 0.21/0.50  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk5_3(k1_xboole_0,X2,X1),esk1_1(X3)),k2_zfmisc_1(X1,X3))|v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 0.21/0.50  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(esk8_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))=k1_xboole_0|k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_55])).
% 0.21/0.50  cnf(c_0_60, plain, (X1=k2_zfmisc_1(X2,k1_xboole_0)|r2_hidden(esk5_3(X2,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_56])).
% 0.21/0.50  cnf(c_0_61, plain, (r2_hidden(k4_tarski(esk1_1(X1),X2),k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_57, c_0_40])).
% 0.21/0.50  cnf(c_0_62, negated_conjecture, (k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_52]), c_0_22]), c_0_15])).
% 0.21/0.50  cnf(c_0_63, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_60])).
% 0.21/0.50  cnf(c_0_64, negated_conjecture, (v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_22])).
% 0.21/0.50  cnf(c_0_65, plain, (X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_64])])).
% 0.21/0.50  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_65])]), ['proof']).
% 0.21/0.50  # SZS output end CNFRefutation
% 0.21/0.50  # Proof object total steps             : 67
% 0.21/0.50  # Proof object clause steps            : 40
% 0.21/0.50  # Proof object formula steps           : 27
% 0.21/0.50  # Proof object conjectures             : 11
% 0.21/0.50  # Proof object clause conjectures      : 8
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 17
% 0.21/0.50  # Proof object initial formulas used   : 13
% 0.21/0.50  # Proof object generating inferences   : 15
% 0.21/0.50  # Proof object simplifying inferences  : 37
% 0.21/0.50  # Training examples: 0 positive, 0 negative
% 0.21/0.50  # Parsed axioms                        : 13
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 24
% 0.21/0.50  # Removed in clause preprocessing      : 7
% 0.21/0.50  # Initial clauses in saturation        : 17
% 0.21/0.50  # Processed clauses                    : 285
% 0.21/0.50  # ...of these trivial                  : 0
% 0.21/0.50  # ...subsumed                          : 80
% 0.21/0.50  # ...remaining for further processing  : 205
% 0.21/0.50  # Other redundant clauses eliminated   : 6
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 4
% 0.21/0.50  # Backward-rewritten                   : 147
% 0.21/0.50  # Generated clauses                    : 3453
% 0.21/0.50  # ...of the previous two non-trivial   : 3369
% 0.21/0.50  # Contextual simplify-reflections      : 2
% 0.21/0.50  # Paramodulations                      : 3420
% 0.21/0.50  # Factorizations                       : 0
% 0.21/0.50  # Equation resolutions                 : 6
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 4
% 0.21/0.50  #    Positive orientable unit clauses  : 1
% 0.21/0.50  #    Positive unorientable unit clauses: 1
% 0.21/0.50  #    Negative unit clauses             : 2
% 0.21/0.50  #    Non-unit-clauses                  : 0
% 0.21/0.50  # Current number of unprocessed clauses: 3020
% 0.21/0.50  # ...number of literals in the above   : 14788
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 203
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 2595
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 583
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 64
% 0.21/0.50  # Unit Clause-clause subsumption calls : 99
% 0.21/0.50  # Rewrite failures with RHS unbound    : 5
% 0.21/0.50  # BW rewrite match attempts            : 140
% 0.21/0.50  # BW rewrite match successes           : 139
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 72380
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.158 s
% 0.21/0.50  # System time              : 0.007 s
% 0.21/0.50  # Total time               : 0.165 s
% 0.21/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
