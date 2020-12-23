%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:11 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 347 expanded)
%              Number of clauses        :   64 ( 176 expanded)
%              Number of leaves         :   11 (  85 expanded)
%              Depth                    :   26
%              Number of atoms          :  255 (1183 expanded)
%              Number of equality atoms :  111 ( 535 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_15,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X20
        | X23 = X21
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( esk3_3(X25,X26,X27) != X25
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( esk3_3(X25,X26,X27) != X26
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X27)
        | esk3_3(X25,X26,X27) = X25
        | esk3_3(X25,X26,X27) = X26
        | X27 = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_20,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

fof(c_0_21,plain,(
    ! [X38,X39,X41] :
      ( ( r2_hidden(esk4_2(X38,X39),X39)
        | ~ r2_hidden(X38,X39) )
      & ( ~ r2_hidden(X41,X39)
        | ~ r2_hidden(X41,esk4_2(X38,X39))
        | ~ r2_hidden(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_17]),c_0_18])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk4_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( esk4_2(X1,k2_enumset1(X2,X2,X2,X2)) = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | r1_tarski(k1_setfam_1(X56),X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ r2_hidden(X3,k2_enumset1(X2,X2,X2,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_setfam_1(X1),esk4_2(X2,X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

fof(c_0_41,plain,(
    ! [X42,X43,X44,X45,X46,X48,X51,X52,X53,X54] :
      ( ( ~ r2_hidden(X44,X43)
        | ~ r2_hidden(X45,X42)
        | r2_hidden(X44,X45)
        | X43 != k1_setfam_1(X42)
        | X42 = k1_xboole_0 )
      & ( r2_hidden(esk5_3(X42,X43,X46),X42)
        | r2_hidden(X46,X43)
        | X43 != k1_setfam_1(X42)
        | X42 = k1_xboole_0 )
      & ( ~ r2_hidden(X46,esk5_3(X42,X43,X46))
        | r2_hidden(X46,X43)
        | X43 != k1_setfam_1(X42)
        | X42 = k1_xboole_0 )
      & ( r2_hidden(esk7_2(X42,X48),X42)
        | ~ r2_hidden(esk6_2(X42,X48),X48)
        | X48 = k1_setfam_1(X42)
        | X42 = k1_xboole_0 )
      & ( ~ r2_hidden(esk6_2(X42,X48),esk7_2(X42,X48))
        | ~ r2_hidden(esk6_2(X42,X48),X48)
        | X48 = k1_setfam_1(X42)
        | X42 = k1_xboole_0 )
      & ( r2_hidden(esk6_2(X42,X48),X48)
        | ~ r2_hidden(X51,X42)
        | r2_hidden(esk6_2(X42,X48),X51)
        | X48 = k1_setfam_1(X42)
        | X42 = k1_xboole_0 )
      & ( X53 != k1_setfam_1(X52)
        | X53 = k1_xboole_0
        | X52 != k1_xboole_0 )
      & ( X54 != k1_xboole_0
        | X54 = k1_setfam_1(X52)
        | X52 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,esk4_2(X2,X3))
    | ~ r2_hidden(X1,k1_setfam_1(X3))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(esk4_2(X1,X2),k1_setfam_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( k1_setfam_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(esk4_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_25])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_47])).

cnf(c_0_53,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(esk4_2(X2,X1),k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(esk4_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k1_setfam_1(X3)))),X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k1_setfam_1(X3))))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(esk4_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_25])).

fof(c_0_56,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_25])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k1_setfam_1(X2))))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1))),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_58])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1))),X2)
    | r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_58])).

cnf(c_0_65,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_47])).

cnf(c_0_66,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1))) = k1_xboole_0
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1))) = k1_xboole_0
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1))) = X1
    | k1_xboole_0 != X1 ),
    inference(ef,[status(thm)],[c_0_67])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k1_setfam_1(X1))
    | k1_xboole_0 != X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_68])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k1_xboole_0 != X1 ),
    inference(spm,[status(thm)],[c_0_69,c_0_49])).

cnf(c_0_71,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_72,plain,
    ( k1_xboole_0 != X1
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_70]),c_0_57])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk5_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_74,plain,
    ( esk5_3(k2_enumset1(X1,X1,X1,X1),X2,X3) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r2_hidden(X3,X2)
    | X2 != k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_71])).

cnf(c_0_75,plain,
    ( k2_enumset1(X1,X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_34])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_setfam_1(k2_enumset1(X3,X3,X3,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

fof(c_0_77,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_76])).

fof(c_0_80,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk8_0)) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk8_0)) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_58])).

cnf(c_0_84,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) != esk8_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_85,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_83]),c_0_47])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:14:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.47/0.63  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.47/0.63  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.63  #
% 0.47/0.63  # Preprocessing time       : 0.029 s
% 0.47/0.63  # Presaturation interreduction done
% 0.47/0.63  
% 0.47/0.63  # Proof found!
% 0.47/0.63  # SZS status Theorem
% 0.47/0.63  # SZS output start CNFRefutation
% 0.47/0.63  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.47/0.63  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.63  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.63  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.63  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.47/0.63  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.47/0.63  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.47/0.63  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.47/0.63  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.47/0.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.63  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.47/0.63  fof(c_0_11, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.47/0.63  fof(c_0_12, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.63  fof(c_0_13, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.63  fof(c_0_14, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.63  cnf(c_0_15, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.63  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.63  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.63  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.63  fof(c_0_19, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X23,X22)|(X23=X20|X23=X21)|X22!=k2_tarski(X20,X21))&((X24!=X20|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))))&(((esk3_3(X25,X26,X27)!=X25|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26))&(esk3_3(X25,X26,X27)!=X26|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26)))&(r2_hidden(esk3_3(X25,X26,X27),X27)|(esk3_3(X25,X26,X27)=X25|esk3_3(X25,X26,X27)=X26)|X27=k2_tarski(X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.47/0.63  cnf(c_0_20, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.47/0.63  fof(c_0_21, plain, ![X38, X39, X41]:((r2_hidden(esk4_2(X38,X39),X39)|~r2_hidden(X38,X39))&(~r2_hidden(X41,X39)|~r2_hidden(X41,esk4_2(X38,X39))|~r2_hidden(X38,X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.47/0.63  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.63  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.63  cnf(c_0_24, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.47/0.63  cnf(c_0_25, plain, (r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.63  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_18])).
% 0.47/0.63  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_17]), c_0_18])).
% 0.47/0.63  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk4_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.63  cnf(c_0_29, plain, (esk4_2(X1,k2_enumset1(X2,X2,X2,X2))=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.47/0.63  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X1,X1,X3)), inference(er,[status(thm)],[c_0_26])).
% 0.47/0.63  fof(c_0_31, plain, ![X55, X56]:(~r2_hidden(X55,X56)|r1_tarski(k1_setfam_1(X56),X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.47/0.63  cnf(c_0_32, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X3,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.47/0.63  cnf(c_0_33, plain, (~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|~r2_hidden(X3,k2_enumset1(X2,X2,X2,X2))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.47/0.63  cnf(c_0_34, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_30])).
% 0.47/0.63  fof(c_0_35, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.47/0.63  cnf(c_0_36, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.63  cnf(c_0_37, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_32])).
% 0.47/0.63  cnf(c_0_38, plain, (~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.47/0.63  cnf(c_0_39, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.47/0.63  cnf(c_0_40, plain, (r1_tarski(k1_setfam_1(X1),esk4_2(X2,X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.47/0.63  fof(c_0_41, plain, ![X42, X43, X44, X45, X46, X48, X51, X52, X53, X54]:((((~r2_hidden(X44,X43)|(~r2_hidden(X45,X42)|r2_hidden(X44,X45))|X43!=k1_setfam_1(X42)|X42=k1_xboole_0)&((r2_hidden(esk5_3(X42,X43,X46),X42)|r2_hidden(X46,X43)|X43!=k1_setfam_1(X42)|X42=k1_xboole_0)&(~r2_hidden(X46,esk5_3(X42,X43,X46))|r2_hidden(X46,X43)|X43!=k1_setfam_1(X42)|X42=k1_xboole_0)))&(((r2_hidden(esk7_2(X42,X48),X42)|~r2_hidden(esk6_2(X42,X48),X48)|X48=k1_setfam_1(X42)|X42=k1_xboole_0)&(~r2_hidden(esk6_2(X42,X48),esk7_2(X42,X48))|~r2_hidden(esk6_2(X42,X48),X48)|X48=k1_setfam_1(X42)|X42=k1_xboole_0))&(r2_hidden(esk6_2(X42,X48),X48)|(~r2_hidden(X51,X42)|r2_hidden(esk6_2(X42,X48),X51))|X48=k1_setfam_1(X42)|X42=k1_xboole_0)))&((X53!=k1_setfam_1(X52)|X53=k1_xboole_0|X52!=k1_xboole_0)&(X54!=k1_xboole_0|X54=k1_setfam_1(X52)|X52!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.47/0.63  cnf(c_0_42, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.47/0.63  cnf(c_0_43, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.47/0.63  cnf(c_0_44, plain, (r2_hidden(X1,esk4_2(X2,X3))|~r2_hidden(X1,k1_setfam_1(X3))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.47/0.63  cnf(c_0_45, plain, (X1=k1_xboole_0|X1!=k1_setfam_1(X2)|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.63  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2)))), inference(spm,[status(thm)],[c_0_39, c_0_42])).
% 0.47/0.63  cnf(c_0_47, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.47/0.63  cnf(c_0_48, plain, (~r2_hidden(esk4_2(X1,X2),k1_setfam_1(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.47/0.63  cnf(c_0_49, plain, (k1_setfam_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_45])).
% 0.47/0.63  cnf(c_0_50, plain, (~r2_hidden(X1,k1_setfam_1(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_44])).
% 0.47/0.63  cnf(c_0_51, plain, (r2_hidden(esk4_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X3)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_46, c_0_25])).
% 0.47/0.63  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_39, c_0_47])).
% 0.47/0.63  cnf(c_0_53, plain, (X1!=k1_xboole_0|~r2_hidden(esk4_2(X2,X1),k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.47/0.63  cnf(c_0_54, plain, (~r2_hidden(esk4_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k1_setfam_1(X3)))),X3)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k1_setfam_1(X3))))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.47/0.63  cnf(c_0_55, plain, (r2_hidden(esk4_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_52, c_0_25])).
% 0.47/0.63  fof(c_0_56, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.63  cnf(c_0_57, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_25])).
% 0.47/0.63  cnf(c_0_58, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.47/0.63  cnf(c_0_59, plain, (~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k1_setfam_1(X2))))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.47/0.63  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.47/0.63  cnf(c_0_61, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.47/0.63  cnf(c_0_62, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1))),X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_59, c_0_58])).
% 0.47/0.63  cnf(c_0_63, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.47/0.63  cnf(c_0_64, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1))),X2)|r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_62, c_0_58])).
% 0.47/0.63  cnf(c_0_65, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_60, c_0_47])).
% 0.47/0.63  cnf(c_0_66, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1)))=k1_xboole_0|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.47/0.63  cnf(c_0_67, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1)))=k1_xboole_0|k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.47/0.63  cnf(c_0_68, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(X1)))=X1|k1_xboole_0!=X1), inference(ef,[status(thm)],[c_0_67])).
% 0.47/0.63  cnf(c_0_69, plain, (r1_tarski(X1,k1_setfam_1(X1))|k1_xboole_0!=X1), inference(spm,[status(thm)],[c_0_42, c_0_68])).
% 0.47/0.63  cnf(c_0_70, plain, (r1_tarski(X1,k1_xboole_0)|k1_xboole_0!=X1), inference(spm,[status(thm)],[c_0_69, c_0_49])).
% 0.47/0.63  cnf(c_0_71, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.63  cnf(c_0_72, plain, (k1_xboole_0!=X1|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_70]), c_0_57])).
% 0.47/0.63  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk5_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.63  cnf(c_0_74, plain, (esk5_3(k2_enumset1(X1,X1,X1,X1),X2,X3)=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r2_hidden(X3,X2)|X2!=k1_setfam_1(k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_24, c_0_71])).
% 0.47/0.63  cnf(c_0_75, plain, (k2_enumset1(X1,X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_34])).
% 0.47/0.63  cnf(c_0_76, plain, (r2_hidden(X1,X2)|X2!=k1_setfam_1(k2_enumset1(X3,X3,X3,X3))|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.47/0.63  fof(c_0_77, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.47/0.63  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.47/0.63  cnf(c_0_79, plain, (r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_76])).
% 0.47/0.63  fof(c_0_80, negated_conjecture, k1_setfam_1(k1_tarski(esk8_0))!=esk8_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).
% 0.47/0.63  cnf(c_0_81, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2))),X2)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.47/0.63  cnf(c_0_82, negated_conjecture, (k1_setfam_1(k1_tarski(esk8_0))!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.47/0.63  cnf(c_0_83, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_81, c_0_58])).
% 0.47/0.63  cnf(c_0_84, negated_conjecture, (k1_setfam_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))!=esk8_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_16]), c_0_17]), c_0_18])).
% 0.47/0.63  cnf(c_0_85, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_83]), c_0_47])])).
% 0.47/0.63  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])]), ['proof']).
% 0.47/0.63  # SZS output end CNFRefutation
% 0.47/0.63  # Proof object total steps             : 87
% 0.47/0.63  # Proof object clause steps            : 64
% 0.47/0.63  # Proof object formula steps           : 23
% 0.47/0.63  # Proof object conjectures             : 6
% 0.47/0.63  # Proof object clause conjectures      : 3
% 0.47/0.63  # Proof object formula conjectures     : 3
% 0.47/0.63  # Proof object initial clauses used    : 17
% 0.47/0.63  # Proof object initial formulas used   : 11
% 0.47/0.63  # Proof object generating inferences   : 40
% 0.47/0.63  # Proof object simplifying inferences  : 18
% 0.47/0.63  # Training examples: 0 positive, 0 negative
% 0.47/0.63  # Parsed axioms                        : 12
% 0.47/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.63  # Initial clauses                      : 34
% 0.47/0.63  # Removed in clause preprocessing      : 3
% 0.47/0.63  # Initial clauses in saturation        : 31
% 0.47/0.63  # Processed clauses                    : 2960
% 0.47/0.63  # ...of these trivial                  : 28
% 0.47/0.63  # ...subsumed                          : 2303
% 0.47/0.63  # ...remaining for further processing  : 629
% 0.47/0.63  # Other redundant clauses eliminated   : 136
% 0.47/0.63  # Clauses deleted for lack of memory   : 0
% 0.47/0.63  # Backward-subsumed                    : 42
% 0.47/0.63  # Backward-rewritten                   : 55
% 0.47/0.63  # Generated clauses                    : 17407
% 0.47/0.63  # ...of the previous two non-trivial   : 15031
% 0.47/0.63  # Contextual simplify-reflections      : 21
% 0.47/0.63  # Paramodulations                      : 17156
% 0.47/0.63  # Factorizations                       : 72
% 0.47/0.63  # Equation resolutions                 : 176
% 0.47/0.63  # Propositional unsat checks           : 0
% 0.47/0.63  #    Propositional check models        : 0
% 0.47/0.63  #    Propositional check unsatisfiable : 0
% 0.47/0.63  #    Propositional clauses             : 0
% 0.47/0.63  #    Propositional clauses after purity: 0
% 0.47/0.63  #    Propositional unsat core size     : 0
% 0.47/0.63  #    Propositional preprocessing time  : 0.000
% 0.47/0.63  #    Propositional encoding time       : 0.000
% 0.47/0.63  #    Propositional solver time         : 0.000
% 0.47/0.63  #    Success case prop preproc time    : 0.000
% 0.47/0.63  #    Success case prop encoding time   : 0.000
% 0.47/0.63  #    Success case prop solver time     : 0.000
% 0.47/0.63  # Current number of processed clauses  : 494
% 0.47/0.63  #    Positive orientable unit clauses  : 22
% 0.47/0.63  #    Positive unorientable unit clauses: 0
% 0.47/0.63  #    Negative unit clauses             : 8
% 0.47/0.63  #    Non-unit-clauses                  : 464
% 0.47/0.63  # Current number of unprocessed clauses: 11896
% 0.47/0.63  # ...number of literals in the above   : 51245
% 0.47/0.63  # Current number of archived formulas  : 0
% 0.47/0.63  # Current number of archived clauses   : 132
% 0.47/0.63  # Clause-clause subsumption calls (NU) : 27696
% 0.47/0.63  # Rec. Clause-clause subsumption calls : 16553
% 0.47/0.63  # Non-unit clause-clause subsumptions  : 1399
% 0.47/0.63  # Unit Clause-clause subsumption calls : 926
% 0.47/0.63  # Rewrite failures with RHS unbound    : 0
% 0.47/0.63  # BW rewrite match attempts            : 188
% 0.47/0.63  # BW rewrite match successes           : 15
% 0.47/0.63  # Condensation attempts                : 0
% 0.47/0.63  # Condensation successes               : 0
% 0.47/0.63  # Termbank termtop insertions          : 297459
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.291 s
% 0.47/0.64  # System time              : 0.011 s
% 0.47/0.64  # Total time               : 0.303 s
% 0.47/0.64  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
