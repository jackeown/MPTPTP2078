%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:57 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  123 (11175 expanded)
%              Number of clauses        :   79 (4232 expanded)
%              Number of leaves         :   22 (3435 expanded)
%              Depth                    :   18
%              Number of atoms          :  288 (15465 expanded)
%              Number of equality atoms :  129 (12531 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_22,plain,(
    ! [X64,X65] :
      ( ~ r1_xboole_0(k1_tarski(X64),X65)
      | ~ r2_hidden(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k5_enumset1(X40,X40,X41,X42,X43,X44,X45) = k4_enumset1(X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52) = k5_enumset1(X46,X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,plain,(
    ! [X68,X69] : k3_tarski(k2_tarski(X68,X69)) = k2_xboole_0(X68,X69) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

cnf(c_0_32,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X53,X54,X55,X57,X58,X59,X60,X62] :
      ( ( r2_hidden(X55,esk2_3(X53,X54,X55))
        | ~ r2_hidden(X55,X54)
        | X54 != k3_tarski(X53) )
      & ( r2_hidden(esk2_3(X53,X54,X55),X53)
        | ~ r2_hidden(X55,X54)
        | X54 != k3_tarski(X53) )
      & ( ~ r2_hidden(X57,X58)
        | ~ r2_hidden(X58,X53)
        | r2_hidden(X57,X54)
        | X54 != k3_tarski(X53) )
      & ( ~ r2_hidden(esk3_2(X59,X60),X60)
        | ~ r2_hidden(esk3_2(X59,X60),X62)
        | ~ r2_hidden(X62,X59)
        | X60 = k3_tarski(X59) )
      & ( r2_hidden(esk3_2(X59,X60),esk4_2(X59,X60))
        | r2_hidden(esk3_2(X59,X60),X60)
        | X60 = k3_tarski(X59) )
      & ( r2_hidden(esk4_2(X59,X60),X59)
        | r2_hidden(esk3_2(X59,X60),X60)
        | X60 = k3_tarski(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_41,plain,(
    ! [X20,X21,X22] :
      ( ( r1_xboole_0(X20,k2_xboole_0(X21,X22))
        | ~ r1_xboole_0(X20,X21)
        | ~ r1_xboole_0(X20,X22) )
      & ( r1_xboole_0(X20,X21)
        | ~ r1_xboole_0(X20,k2_xboole_0(X21,X22)) )
      & ( r1_xboole_0(X20,X22)
        | ~ r1_xboole_0(X20,k2_xboole_0(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_43,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_xboole_0
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X66,X67] :
      ( r2_hidden(X66,X67)
      | r1_xboole_0(k1_tarski(X66),X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_51,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_52,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ r1_xboole_0(k6_enumset1(esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_33]),c_0_34]),c_0_48]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_58,plain,(
    ! [X73,X74] :
      ( ( ~ r1_tarski(X73,k1_tarski(X74))
        | X73 = k1_xboole_0
        | X73 = k1_tarski(X74) )
      & ( X73 != k1_xboole_0
        | r1_tarski(X73,k1_tarski(X74)) )
      & ( X73 != k1_tarski(X74)
        | r1_tarski(X73,k1_tarski(X74)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | ~ r1_xboole_0(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_48]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

fof(c_0_65,plain,(
    ! [X70,X71,X72] :
      ( ( r2_hidden(X70,X72)
        | ~ r1_tarski(k2_tarski(X70,X71),X72) )
      & ( r2_hidden(X71,X72)
        | ~ r1_tarski(k2_tarski(X70,X71),X72) )
      & ( ~ r2_hidden(X70,X72)
        | ~ r2_hidden(X71,X72)
        | r1_tarski(k2_tarski(X70,X71),X72) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_66,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(k6_enumset1(esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),esk7_0)
    | r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_56])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_72,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_80,plain,(
    ! [X19] :
      ( ( r1_xboole_0(X19,X19)
        | X19 != k1_xboole_0 )
      & ( X19 = k1_xboole_0
        | ~ r1_xboole_0(X19,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_62])).

cnf(c_0_82,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_76])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk3_2(k1_xboole_0,esk7_0)),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,esk3_2(k1_xboole_0,X1)),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_60])).

cnf(c_0_93,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X1 = esk6_0
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_76])).

cnf(c_0_95,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

fof(c_0_96,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0)) = esk6_0
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0)) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_101,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_102,plain,
    ( ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0)) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_105,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_100])).

cnf(c_0_106,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_48]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_107,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_53])])).

cnf(c_0_108,negated_conjecture,
    ( esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_109,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_54])).

cnf(c_0_110,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_111,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_56])).

cnf(c_0_112,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_76])).

cnf(c_0_113,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,esk1_2(k1_xboole_0,X1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_79])).

cnf(c_0_114,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_115,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_116,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_111]),c_0_112])).

cnf(c_0_117,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_113]),c_0_53])])).

cnf(c_0_118,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_119,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_76])).

cnf(c_0_120,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_106,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_119]),c_0_120]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.56  # and selection function GSelectMinInfpos.
% 0.19/0.56  #
% 0.19/0.56  # Preprocessing time       : 0.028 s
% 0.19/0.56  # Presaturation interreduction done
% 0.19/0.56  
% 0.19/0.56  # Proof found!
% 0.19/0.56  # SZS status Theorem
% 0.19/0.56  # SZS output start CNFRefutation
% 0.19/0.56  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.19/0.56  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.56  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.56  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.56  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.56  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.56  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.56  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.56  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.56  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.19/0.56  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.56  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.56  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.56  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.19/0.56  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.56  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.19/0.56  fof(t39_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.19/0.56  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.56  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.56  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.56  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.19/0.56  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.56  fof(c_0_22, plain, ![X64, X65]:(~r1_xboole_0(k1_tarski(X64),X65)|~r2_hidden(X64,X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.19/0.56  fof(c_0_23, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.56  fof(c_0_24, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.56  fof(c_0_25, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.56  fof(c_0_26, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.56  fof(c_0_27, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.56  fof(c_0_28, plain, ![X40, X41, X42, X43, X44, X45]:k5_enumset1(X40,X40,X41,X42,X43,X44,X45)=k4_enumset1(X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.56  fof(c_0_29, plain, ![X46, X47, X48, X49, X50, X51, X52]:k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52)=k5_enumset1(X46,X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.56  fof(c_0_30, plain, ![X68, X69]:k3_tarski(k2_tarski(X68,X69))=k2_xboole_0(X68,X69), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.56  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.19/0.56  cnf(c_0_32, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.56  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.56  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.56  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.56  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.56  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.56  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.56  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.56  fof(c_0_40, plain, ![X53, X54, X55, X57, X58, X59, X60, X62]:((((r2_hidden(X55,esk2_3(X53,X54,X55))|~r2_hidden(X55,X54)|X54!=k3_tarski(X53))&(r2_hidden(esk2_3(X53,X54,X55),X53)|~r2_hidden(X55,X54)|X54!=k3_tarski(X53)))&(~r2_hidden(X57,X58)|~r2_hidden(X58,X53)|r2_hidden(X57,X54)|X54!=k3_tarski(X53)))&((~r2_hidden(esk3_2(X59,X60),X60)|(~r2_hidden(esk3_2(X59,X60),X62)|~r2_hidden(X62,X59))|X60=k3_tarski(X59))&((r2_hidden(esk3_2(X59,X60),esk4_2(X59,X60))|r2_hidden(esk3_2(X59,X60),X60)|X60=k3_tarski(X59))&(r2_hidden(esk4_2(X59,X60),X59)|r2_hidden(esk3_2(X59,X60),X60)|X60=k3_tarski(X59))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.56  fof(c_0_41, plain, ![X20, X21, X22]:((r1_xboole_0(X20,k2_xboole_0(X21,X22))|~r1_xboole_0(X20,X21)|~r1_xboole_0(X20,X22))&((r1_xboole_0(X20,X21)|~r1_xboole_0(X20,k2_xboole_0(X21,X22)))&(r1_xboole_0(X20,X22)|~r1_xboole_0(X20,k2_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.19/0.56  cnf(c_0_42, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.56  fof(c_0_43, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.19/0.56  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_45, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.56  fof(c_0_46, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.56  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.56  cnf(c_0_48, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_34])).
% 0.19/0.56  cnf(c_0_49, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.56  fof(c_0_50, plain, ![X66, X67]:(r2_hidden(X66,X67)|r1_xboole_0(k1_tarski(X66),X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.19/0.56  fof(c_0_51, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.56  cnf(c_0_52, plain, (X1=k3_tarski(X2)|r2_hidden(esk3_2(X2,X1),X1)|~r1_xboole_0(k6_enumset1(esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1),esk4_2(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.56  cnf(c_0_53, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.56  cnf(c_0_54, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.19/0.56  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_56, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_33]), c_0_34]), c_0_48]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.19/0.56  cnf(c_0_57, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.56  fof(c_0_58, plain, ![X73, X74]:((~r1_tarski(X73,k1_tarski(X74))|(X73=k1_xboole_0|X73=k1_tarski(X74)))&((X73!=k1_xboole_0|r1_tarski(X73,k1_tarski(X74)))&(X73!=k1_tarski(X74)|r1_tarski(X73,k1_tarski(X74))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).
% 0.19/0.56  cnf(c_0_59, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.56  cnf(c_0_60, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.19/0.56  cnf(c_0_61, negated_conjecture, (r1_xboole_0(X1,esk7_0)|~r1_xboole_0(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.56  cnf(c_0_62, plain, (r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_63, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.56  cnf(c_0_64, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_48]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  fof(c_0_65, plain, ![X70, X71, X72]:(((r2_hidden(X70,X72)|~r1_tarski(k2_tarski(X70,X71),X72))&(r2_hidden(X71,X72)|~r1_tarski(k2_tarski(X70,X71),X72)))&(~r2_hidden(X70,X72)|~r2_hidden(X71,X72)|r1_tarski(k2_tarski(X70,X71),X72))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.56  fof(c_0_66, plain, ![X14, X15]:(~r1_xboole_0(X14,X15)|r1_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.56  cnf(c_0_67, plain, (X1=k1_xboole_0|~r1_xboole_0(k6_enumset1(esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1),esk3_2(k1_xboole_0,X1)),X1)), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 0.19/0.56  cnf(c_0_68, negated_conjecture, (r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),esk7_0)|r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.56  cnf(c_0_69, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.19/0.56  cnf(c_0_70, negated_conjecture, (r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_64, c_0_56])).
% 0.19/0.56  cnf(c_0_71, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.56  fof(c_0_72, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.56  cnf(c_0_73, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.56  cnf(c_0_74, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.56  cnf(c_0_75, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.56  cnf(c_0_76, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.56  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.56  cnf(c_0_79, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.56  fof(c_0_80, plain, ![X19]:((r1_xboole_0(X19,X19)|X19!=k1_xboole_0)&(X19=k1_xboole_0|~r1_xboole_0(X19,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.19/0.56  cnf(c_0_81, plain, (r1_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_62])).
% 0.19/0.56  cnf(c_0_82, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_83, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.56  cnf(c_0_84, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_76])).
% 0.19/0.56  cnf(c_0_85, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.56  cnf(c_0_86, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.56  cnf(c_0_87, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.56  cnf(c_0_88, negated_conjecture, (r1_xboole_0(X1,esk7_0)|r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_81])).
% 0.19/0.56  cnf(c_0_89, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk3_2(k1_xboole_0,esk7_0)),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.56  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.56  cnf(c_0_91, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_92, plain, (X1=k1_xboole_0|r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,esk3_2(k1_xboole_0,X1)),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_82, c_0_60])).
% 0.19/0.56  cnf(c_0_93, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.56  cnf(c_0_94, negated_conjecture, (esk6_0=k1_xboole_0|X1=k1_xboole_0|X1=esk6_0|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_76])).
% 0.19/0.56  cnf(c_0_95, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.56  fof(c_0_96, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.56  cnf(c_0_97, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_91, c_0_85])).
% 0.19/0.56  cnf(c_0_98, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0)),esk7_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.56  cnf(c_0_99, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0))=esk6_0|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0))=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.56  cnf(c_0_100, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.56  cnf(c_0_101, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.56  cnf(c_0_102, plain, (~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_44, c_0_97])).
% 0.19/0.56  cnf(c_0_103, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_2(k1_xboole_0,esk7_0))=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.56  cnf(c_0_104, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.56  cnf(c_0_105, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_100])).
% 0.19/0.56  cnf(c_0_106, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_48]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_107, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_53])])).
% 0.19/0.56  cnf(c_0_108, negated_conjecture, (esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.19/0.56  cnf(c_0_109, plain, (r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_105, c_0_54])).
% 0.19/0.56  cnf(c_0_110, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.56  cnf(c_0_111, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_56])).
% 0.19/0.56  cnf(c_0_112, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=esk6_0), inference(spm,[status(thm)],[c_0_108, c_0_76])).
% 0.19/0.56  cnf(c_0_113, plain, (r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,esk1_2(k1_xboole_0,X1)),k1_xboole_0)|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_109, c_0_79])).
% 0.19/0.56  cnf(c_0_114, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.56  cnf(c_0_115, negated_conjecture, (esk7_0!=k1_xboole_0|esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_116, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_111]), c_0_112])).
% 0.19/0.56  cnf(c_0_117, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_113]), c_0_53])])).
% 0.19/0.56  cnf(c_0_118, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.56  cnf(c_0_119, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_76])).
% 0.19/0.56  cnf(c_0_120, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_106, c_0_117])).
% 0.19/0.56  cnf(c_0_121, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])])).
% 0.19/0.56  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_119]), c_0_120]), c_0_121]), ['proof']).
% 0.19/0.56  # SZS output end CNFRefutation
% 0.19/0.56  # Proof object total steps             : 123
% 0.19/0.56  # Proof object clause steps            : 79
% 0.19/0.56  # Proof object formula steps           : 44
% 0.19/0.56  # Proof object conjectures             : 34
% 0.19/0.56  # Proof object clause conjectures      : 31
% 0.19/0.56  # Proof object formula conjectures     : 3
% 0.19/0.56  # Proof object initial clauses used    : 29
% 0.19/0.56  # Proof object initial formulas used   : 22
% 0.19/0.56  # Proof object generating inferences   : 33
% 0.19/0.56  # Proof object simplifying inferences  : 126
% 0.19/0.56  # Training examples: 0 positive, 0 negative
% 0.19/0.56  # Parsed axioms                        : 22
% 0.19/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.56  # Initial clauses                      : 39
% 0.19/0.56  # Removed in clause preprocessing      : 8
% 0.19/0.56  # Initial clauses in saturation        : 31
% 0.19/0.56  # Processed clauses                    : 1122
% 0.19/0.56  # ...of these trivial                  : 5
% 0.19/0.56  # ...subsumed                          : 496
% 0.19/0.56  # ...remaining for further processing  : 620
% 0.19/0.56  # Other redundant clauses eliminated   : 6
% 0.19/0.56  # Clauses deleted for lack of memory   : 0
% 0.19/0.56  # Backward-subsumed                    : 44
% 0.19/0.56  # Backward-rewritten                   : 288
% 0.19/0.56  # Generated clauses                    : 6800
% 0.19/0.56  # ...of the previous two non-trivial   : 6608
% 0.19/0.56  # Contextual simplify-reflections      : 2
% 0.19/0.56  # Paramodulations                      : 6785
% 0.19/0.56  # Factorizations                       : 9
% 0.19/0.56  # Equation resolutions                 : 6
% 0.19/0.56  # Propositional unsat checks           : 0
% 0.19/0.56  #    Propositional check models        : 0
% 0.19/0.56  #    Propositional check unsatisfiable : 0
% 0.19/0.56  #    Propositional clauses             : 0
% 0.19/0.56  #    Propositional clauses after purity: 0
% 0.19/0.56  #    Propositional unsat core size     : 0
% 0.19/0.56  #    Propositional preprocessing time  : 0.000
% 0.19/0.56  #    Propositional encoding time       : 0.000
% 0.19/0.56  #    Propositional solver time         : 0.000
% 0.19/0.56  #    Success case prop preproc time    : 0.000
% 0.19/0.56  #    Success case prop encoding time   : 0.000
% 0.19/0.56  #    Success case prop solver time     : 0.000
% 0.19/0.56  # Current number of processed clauses  : 252
% 0.19/0.56  #    Positive orientable unit clauses  : 14
% 0.19/0.56  #    Positive unorientable unit clauses: 0
% 0.19/0.56  #    Negative unit clauses             : 3
% 0.19/0.56  #    Non-unit-clauses                  : 235
% 0.19/0.56  # Current number of unprocessed clauses: 5448
% 0.19/0.56  # ...number of literals in the above   : 21579
% 0.19/0.56  # Current number of archived formulas  : 0
% 0.19/0.56  # Current number of archived clauses   : 370
% 0.19/0.56  # Clause-clause subsumption calls (NU) : 21646
% 0.19/0.56  # Rec. Clause-clause subsumption calls : 6211
% 0.19/0.56  # Non-unit clause-clause subsumptions  : 534
% 0.19/0.56  # Unit Clause-clause subsumption calls : 63
% 0.19/0.56  # Rewrite failures with RHS unbound    : 0
% 0.19/0.56  # BW rewrite match attempts            : 41
% 0.19/0.56  # BW rewrite match successes           : 5
% 0.19/0.56  # Condensation attempts                : 0
% 0.19/0.56  # Condensation successes               : 0
% 0.19/0.56  # Termbank termtop insertions          : 244242
% 0.19/0.56  
% 0.19/0.56  # -------------------------------------------------
% 0.19/0.56  # User time                : 0.208 s
% 0.19/0.56  # System time              : 0.008 s
% 0.19/0.56  # Total time               : 0.216 s
% 0.19/0.56  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
