%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:19 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  123 (4063 expanded)
%              Number of clauses        :   78 (1643 expanded)
%              Number of leaves         :   22 (1205 expanded)
%              Depth                    :   15
%              Number of atoms          :  236 (5989 expanded)
%              Number of equality atoms :  118 (3997 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t32_zfmisc_1,conjecture,(
    ! [X1,X2] : k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(c_0_22,plain,(
    ! [X29,X30] :
      ( ( k4_xboole_0(X29,X30) != k1_xboole_0
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | k4_xboole_0(X29,X30) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_23,plain,(
    ! [X31,X32] : k4_xboole_0(X31,X32) = k5_xboole_0(X31,k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_25,plain,(
    ! [X33] : r1_xboole_0(X33,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_29,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( ~ r2_hidden(X38,X37)
        | X38 = X36
        | X37 != k1_tarski(X36) )
      & ( X39 != X36
        | r2_hidden(X39,X37)
        | X37 != k1_tarski(X36) )
      & ( ~ r2_hidden(esk4_2(X40,X41),X41)
        | esk4_2(X40,X41) != X40
        | X41 = k1_tarski(X40) )
      & ( r2_hidden(esk4_2(X40,X41),X41)
        | esk4_2(X40,X41) = X40
        | X41 = k1_tarski(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X43] : k2_tarski(X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_31,plain,(
    ! [X44,X45] : k1_enumset1(X44,X44,X45) = k2_tarski(X44,X45) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_32,plain,(
    ! [X46,X47,X48] : k2_enumset1(X46,X46,X47,X48) = k1_enumset1(X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X49,X50,X51,X52] : k3_enumset1(X49,X49,X50,X51,X52) = k2_enumset1(X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_34,plain,(
    ! [X53,X54,X55,X56,X57] : k4_enumset1(X53,X53,X54,X55,X56,X57) = k3_enumset1(X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_35,plain,(
    ! [X58,X59,X60,X61,X62,X63] : k5_enumset1(X58,X58,X59,X60,X61,X62,X63) = k4_enumset1(X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_36,plain,(
    ! [X27,X28] :
      ( ( r1_tarski(X27,X28)
        | X27 != X28 )
      & ( r1_tarski(X28,X27)
        | X27 != X28 )
      & ( ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,X27)
        | X27 = X28 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_49,plain,(
    ! [X21,X22,X24,X25,X26] :
      ( ( r1_xboole_0(X21,X22)
        | r2_hidden(esk3_2(X21,X22),k3_xboole_0(X21,X22)) )
      & ( ~ r2_hidden(X26,k3_xboole_0(X24,X25))
        | ~ r1_xboole_0(X24,X25) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_56,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_57,negated_conjecture,(
    ~ ! [X1,X2] : k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2))) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t32_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X66,X67] : k3_tarski(k2_tarski(X66,X67)) = k2_xboole_0(X66,X67) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_59,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_60,plain,
    ( X1 = X2
    | k5_xboole_0(X2,k3_xboole_0(X2,X1)) != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0
    | ~ r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_65,negated_conjecture,(
    k3_tarski(k2_tarski(k1_tarski(esk5_0),k1_tarski(esk6_0))) != k2_tarski(esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

fof(c_0_66,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_67,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

fof(c_0_69,plain,(
    ! [X72] : k3_tarski(k1_tarski(X72)) = X72 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_71,plain,
    ( X1 = X2
    | k5_xboole_0(X2,k3_xboole_0(X2,X1)) != k1_xboole_0
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_tarski(esk5_0),k1_tarski(esk6_0))) != k2_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_44])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_70])).

fof(c_0_80,plain,(
    ! [X64,X65] :
      ( r2_hidden(X64,X65)
      | r1_xboole_0(k1_tarski(X64),X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_53])).

cnf(c_0_83,negated_conjecture,
    ( k3_tarski(k5_enumset1(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) != k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_84,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_27]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)) = k1_xboole_0
    | esk1_2(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) = X1 ),
    inference(spm,[status(thm)],[c_0_77,c_0_53])).

cnf(c_0_86,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_79])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_41])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) != k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_64])).

cnf(c_0_93,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k1_xboole_0
    | esk1_2(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) = X1 ),
    inference(spm,[status(thm)],[c_0_85,c_0_64])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_84]),c_0_87])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_89])).

cnf(c_0_97,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_41])).

cnf(c_0_98,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( esk1_2(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = esk6_0
    | k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) != k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_95])).

cnf(c_0_102,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

fof(c_0_103,plain,(
    ! [X68,X69] : r1_tarski(k1_tarski(X68),k2_tarski(X68,X69)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

cnf(c_0_104,plain,
    ( r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = k1_xboole_0
    | k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) != k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_64])).

cnf(c_0_106,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

fof(c_0_107,plain,(
    ! [X70,X71] :
      ( X70 = X71
      | k5_xboole_0(k1_tarski(X70),k1_tarski(X71)) = k2_tarski(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_zfmisc_1])])).

cnf(c_0_108,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,plain,
    ( r2_hidden(esk3_2(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)),k3_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_62])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = k1_xboole_0
    | k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k1_xboole_0
    | k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) != k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_64])).

cnf(c_0_111,plain,
    ( X1 = X2
    | k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_112,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_113,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_114,plain,
    ( r2_hidden(esk3_2(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)),k3_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_64])).

cnf(c_0_115,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k1_xboole_0
    | k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) != k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_110]),c_0_94])])).

cnf(c_0_116,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k1_xboole_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_77,c_0_106])).

cnf(c_0_117,plain,
    ( X1 = X2
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) != k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_96])).

cnf(c_0_120,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_116]),c_0_94]),c_0_117])).

cnf(c_0_121,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_62])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120]),c_0_120]),c_0_120]),c_0_120]),c_0_120]),c_0_120]),c_0_120]),c_0_120]),c_0_121])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.07/1.24  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 1.07/1.24  # and selection function SelectUnlessUniqMax.
% 1.07/1.24  #
% 1.07/1.24  # Preprocessing time       : 0.028 s
% 1.07/1.24  # Presaturation interreduction done
% 1.07/1.24  
% 1.07/1.24  # Proof found!
% 1.07/1.24  # SZS status Theorem
% 1.07/1.24  # SZS output start CNFRefutation
% 1.07/1.24  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.07/1.24  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.07/1.24  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.07/1.24  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.07/1.24  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.07/1.24  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.07/1.24  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.07/1.24  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.07/1.24  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.07/1.24  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.07/1.24  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.07/1.24  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.07/1.24  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.07/1.24  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.07/1.24  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.07/1.24  fof(t32_zfmisc_1, conjecture, ![X1, X2]:k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2)))=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 1.07/1.24  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.07/1.24  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.07/1.24  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.07/1.24  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.07/1.24  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.07/1.24  fof(t29_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.07/1.24  fof(c_0_22, plain, ![X29, X30]:((k4_xboole_0(X29,X30)!=k1_xboole_0|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|k4_xboole_0(X29,X30)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.07/1.24  fof(c_0_23, plain, ![X31, X32]:k4_xboole_0(X31,X32)=k5_xboole_0(X31,k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.07/1.24  fof(c_0_24, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.07/1.24  fof(c_0_25, plain, ![X33]:r1_xboole_0(X33,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 1.07/1.24  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.07/1.24  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.07/1.24  fof(c_0_28, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.07/1.24  fof(c_0_29, plain, ![X36, X37, X38, X39, X40, X41]:(((~r2_hidden(X38,X37)|X38=X36|X37!=k1_tarski(X36))&(X39!=X36|r2_hidden(X39,X37)|X37!=k1_tarski(X36)))&((~r2_hidden(esk4_2(X40,X41),X41)|esk4_2(X40,X41)!=X40|X41=k1_tarski(X40))&(r2_hidden(esk4_2(X40,X41),X41)|esk4_2(X40,X41)=X40|X41=k1_tarski(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.07/1.24  fof(c_0_30, plain, ![X43]:k2_tarski(X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.07/1.24  fof(c_0_31, plain, ![X44, X45]:k1_enumset1(X44,X44,X45)=k2_tarski(X44,X45), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.07/1.24  fof(c_0_32, plain, ![X46, X47, X48]:k2_enumset1(X46,X46,X47,X48)=k1_enumset1(X46,X47,X48), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.07/1.24  fof(c_0_33, plain, ![X49, X50, X51, X52]:k3_enumset1(X49,X49,X50,X51,X52)=k2_enumset1(X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.07/1.24  fof(c_0_34, plain, ![X53, X54, X55, X56, X57]:k4_enumset1(X53,X53,X54,X55,X56,X57)=k3_enumset1(X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.07/1.24  fof(c_0_35, plain, ![X58, X59, X60, X61, X62, X63]:k5_enumset1(X58,X58,X59,X60,X61,X62,X63)=k4_enumset1(X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.07/1.24  fof(c_0_36, plain, ![X27, X28]:(((r1_tarski(X27,X28)|X27!=X28)&(r1_tarski(X28,X27)|X27!=X28))&(~r1_tarski(X27,X28)|~r1_tarski(X28,X27)|X27=X28)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.07/1.24  cnf(c_0_37, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.07/1.24  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.07/1.24  cnf(c_0_39, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.07/1.24  cnf(c_0_40, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 1.07/1.24  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.07/1.24  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.07/1.24  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.07/1.24  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.07/1.24  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.07/1.24  cnf(c_0_46, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.07/1.24  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.07/1.24  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.07/1.24  fof(c_0_49, plain, ![X21, X22, X24, X25, X26]:((r1_xboole_0(X21,X22)|r2_hidden(esk3_2(X21,X22),k3_xboole_0(X21,X22)))&(~r2_hidden(X26,k3_xboole_0(X24,X25))|~r1_xboole_0(X24,X25))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.07/1.24  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.07/1.24  cnf(c_0_51, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_27])).
% 1.07/1.24  cnf(c_0_52, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.07/1.24  cnf(c_0_53, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.07/1.24  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 1.07/1.24  cnf(c_0_55, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.07/1.24  fof(c_0_56, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.07/1.24  fof(c_0_57, negated_conjecture, ~(![X1, X2]:k3_tarski(k2_tarski(k1_tarski(X1),k1_tarski(X2)))=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t32_zfmisc_1])).
% 1.07/1.24  fof(c_0_58, plain, ![X66, X67]:k3_tarski(k2_tarski(X66,X67))=k2_xboole_0(X66,X67), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.07/1.24  cnf(c_0_59, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.07/1.24  cnf(c_0_60, plain, (X1=X2|k5_xboole_0(X2,k3_xboole_0(X2,X1))!=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.07/1.24  cnf(c_0_61, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0|~r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.07/1.24  cnf(c_0_62, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 1.07/1.24  cnf(c_0_63, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_39])).
% 1.07/1.24  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.07/1.24  fof(c_0_65, negated_conjecture, k3_tarski(k2_tarski(k1_tarski(esk5_0),k1_tarski(esk6_0)))!=k2_tarski(esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 1.07/1.24  fof(c_0_66, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.07/1.24  cnf(c_0_67, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.07/1.24  cnf(c_0_68, plain, (X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 1.07/1.24  fof(c_0_69, plain, ![X72]:k3_tarski(k1_tarski(X72))=X72, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 1.07/1.24  cnf(c_0_70, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.07/1.24  cnf(c_0_71, plain, (X1=X2|k5_xboole_0(X2,k3_xboole_0(X2,X1))!=k1_xboole_0|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 1.07/1.24  cnf(c_0_72, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.07/1.24  cnf(c_0_73, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 1.07/1.24  cnf(c_0_74, negated_conjecture, (k3_tarski(k2_tarski(k1_tarski(esk5_0),k1_tarski(esk6_0)))!=k2_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.07/1.24  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.07/1.24  cnf(c_0_76, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_67, c_0_44])).
% 1.07/1.24  cnf(c_0_77, plain, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_68])).
% 1.07/1.24  cnf(c_0_78, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.07/1.24  cnf(c_0_79, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_70])).
% 1.07/1.24  fof(c_0_80, plain, ![X64, X65]:(r2_hidden(X64,X65)|r1_xboole_0(k1_tarski(X64),X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 1.07/1.24  cnf(c_0_81, plain, (X1=k1_xboole_0|k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 1.07/1.24  cnf(c_0_82, plain, (k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_53])).
% 1.07/1.24  cnf(c_0_83, negated_conjecture, (k3_tarski(k5_enumset1(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))!=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48])).
% 1.07/1.24  cnf(c_0_84, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_27]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 1.07/1.24  cnf(c_0_85, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2))=k1_xboole_0|esk1_2(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)=X1), inference(spm,[status(thm)],[c_0_77, c_0_53])).
% 1.07/1.24  cnf(c_0_86, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 1.07/1.24  cnf(c_0_87, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_79])).
% 1.07/1.24  cnf(c_0_88, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.07/1.24  cnf(c_0_89, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.07/1.24  cnf(c_0_90, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_41])).
% 1.07/1.24  cnf(c_0_91, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.07/1.24  cnf(c_0_92, negated_conjecture, (k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))!=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_64])).
% 1.07/1.24  cnf(c_0_93, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))=k1_xboole_0|esk1_2(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)=X1), inference(spm,[status(thm)],[c_0_85, c_0_64])).
% 1.07/1.24  cnf(c_0_94, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_84]), c_0_87])).
% 1.07/1.24  cnf(c_0_95, plain, (r2_hidden(X1,X2)|r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])).
% 1.07/1.24  cnf(c_0_96, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_73, c_0_89])).
% 1.07/1.24  cnf(c_0_97, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_90, c_0_41])).
% 1.07/1.24  cnf(c_0_98, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.07/1.24  cnf(c_0_99, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_91])).
% 1.07/1.24  cnf(c_0_100, negated_conjecture, (esk1_2(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=esk6_0|k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)!=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 1.07/1.24  cnf(c_0_101, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_55, c_0_95])).
% 1.07/1.24  cnf(c_0_102, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 1.07/1.24  fof(c_0_103, plain, ![X68, X69]:r1_tarski(k1_tarski(X68),k2_tarski(X68,X69)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 1.07/1.24  cnf(c_0_104, plain, (r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_98])).
% 1.07/1.24  cnf(c_0_105, negated_conjecture, (k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=k1_xboole_0|k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)!=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_64])).
% 1.07/1.24  cnf(c_0_106, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)=k1_xboole_0|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 1.07/1.24  fof(c_0_107, plain, ![X70, X71]:(X70=X71|k5_xboole_0(k1_tarski(X70),k1_tarski(X71))=k2_tarski(X70,X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_zfmisc_1])])).
% 1.07/1.24  cnf(c_0_108, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.07/1.24  cnf(c_0_109, plain, (r2_hidden(esk3_2(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)),k3_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_104, c_0_62])).
% 1.07/1.24  cnf(c_0_110, negated_conjecture, (k5_xboole_0(k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=k1_xboole_0|k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k1_xboole_0|k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)!=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_64])).
% 1.07/1.24  cnf(c_0_111, plain, (X1=X2|k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 1.07/1.24  cnf(c_0_112, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.07/1.24  cnf(c_0_113, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 1.07/1.24  cnf(c_0_114, plain, (r2_hidden(esk3_2(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)),k3_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_109, c_0_64])).
% 1.07/1.24  cnf(c_0_115, negated_conjecture, (k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k1_xboole_0|k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)!=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_110]), c_0_94])])).
% 1.07/1.24  cnf(c_0_116, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))=k1_xboole_0|X1=X2), inference(spm,[status(thm)],[c_0_77, c_0_106])).
% 1.07/1.24  cnf(c_0_117, plain, (X1=X2|k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))=k5_enumset1(X1,X1,X1,X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48])).
% 1.07/1.24  cnf(c_0_118, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 1.07/1.24  cnf(c_0_119, negated_conjecture, (k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)!=k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|~r2_hidden(esk5_0,k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_96])).
% 1.07/1.24  cnf(c_0_120, negated_conjecture, (esk6_0=esk5_0), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_116]), c_0_94]), c_0_117])).
% 1.07/1.24  cnf(c_0_121, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_118, c_0_62])).
% 1.07/1.24  cnf(c_0_122, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120]), c_0_120]), c_0_120]), c_0_120]), c_0_120]), c_0_120]), c_0_120]), c_0_120]), c_0_121])]), ['proof']).
% 1.07/1.24  # SZS output end CNFRefutation
% 1.07/1.24  # Proof object total steps             : 123
% 1.07/1.24  # Proof object clause steps            : 78
% 1.07/1.24  # Proof object formula steps           : 45
% 1.07/1.24  # Proof object conjectures             : 13
% 1.07/1.24  # Proof object clause conjectures      : 10
% 1.07/1.24  # Proof object formula conjectures     : 3
% 1.07/1.24  # Proof object initial clauses used    : 28
% 1.07/1.24  # Proof object initial formulas used   : 22
% 1.07/1.24  # Proof object generating inferences   : 33
% 1.07/1.24  # Proof object simplifying inferences  : 119
% 1.07/1.24  # Training examples: 0 positive, 0 negative
% 1.07/1.24  # Parsed axioms                        : 22
% 1.07/1.24  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.24  # Initial clauses                      : 33
% 1.07/1.24  # Removed in clause preprocessing      : 8
% 1.07/1.24  # Initial clauses in saturation        : 25
% 1.07/1.24  # Processed clauses                    : 5843
% 1.07/1.24  # ...of these trivial                  : 12
% 1.07/1.24  # ...subsumed                          : 4839
% 1.07/1.24  # ...remaining for further processing  : 992
% 1.07/1.24  # Other redundant clauses eliminated   : 343
% 1.07/1.24  # Clauses deleted for lack of memory   : 0
% 1.07/1.24  # Backward-subsumed                    : 37
% 1.07/1.24  # Backward-rewritten                   : 73
% 1.07/1.24  # Generated clauses                    : 112887
% 1.07/1.24  # ...of the previous two non-trivial   : 98045
% 1.07/1.24  # Contextual simplify-reflections      : 7
% 1.07/1.24  # Paramodulations                      : 112523
% 1.07/1.24  # Factorizations                       : 22
% 1.07/1.24  # Equation resolutions                 : 343
% 1.07/1.24  # Propositional unsat checks           : 0
% 1.07/1.24  #    Propositional check models        : 0
% 1.07/1.24  #    Propositional check unsatisfiable : 0
% 1.07/1.24  #    Propositional clauses             : 0
% 1.07/1.24  #    Propositional clauses after purity: 0
% 1.07/1.24  #    Propositional unsat core size     : 0
% 1.07/1.24  #    Propositional preprocessing time  : 0.000
% 1.07/1.24  #    Propositional encoding time       : 0.000
% 1.07/1.24  #    Propositional solver time         : 0.000
% 1.07/1.24  #    Success case prop preproc time    : 0.000
% 1.07/1.24  #    Success case prop encoding time   : 0.000
% 1.07/1.24  #    Success case prop solver time     : 0.000
% 1.07/1.24  # Current number of processed clauses  : 854
% 1.07/1.24  #    Positive orientable unit clauses  : 17
% 1.07/1.24  #    Positive unorientable unit clauses: 3
% 1.07/1.24  #    Negative unit clauses             : 1
% 1.07/1.24  #    Non-unit-clauses                  : 833
% 1.07/1.24  # Current number of unprocessed clauses: 92012
% 1.07/1.24  # ...number of literals in the above   : 329023
% 1.07/1.24  # Current number of archived formulas  : 0
% 1.07/1.24  # Current number of archived clauses   : 142
% 1.07/1.24  # Clause-clause subsumption calls (NU) : 170212
% 1.07/1.24  # Rec. Clause-clause subsumption calls : 109599
% 1.07/1.24  # Non-unit clause-clause subsumptions  : 4663
% 1.07/1.24  # Unit Clause-clause subsumption calls : 129
% 1.07/1.24  # Rewrite failures with RHS unbound    : 0
% 1.07/1.24  # BW rewrite match attempts            : 50
% 1.07/1.24  # BW rewrite match successes           : 28
% 1.07/1.24  # Condensation attempts                : 0
% 1.07/1.24  # Condensation successes               : 0
% 1.07/1.24  # Termbank termtop insertions          : 2585760
% 1.07/1.25  
% 1.07/1.25  # -------------------------------------------------
% 1.07/1.25  # User time                : 0.863 s
% 1.07/1.25  # System time              : 0.040 s
% 1.07/1.25  # Total time               : 0.903 s
% 1.07/1.25  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
