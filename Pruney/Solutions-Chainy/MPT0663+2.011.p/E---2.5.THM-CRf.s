%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 (1039 expanded)
%              Number of clauses        :   48 ( 381 expanded)
%              Number of leaves         :   19 ( 326 expanded)
%              Depth                    :   12
%              Number of atoms          :  253 (1373 expanded)
%              Number of equality atoms :  151 (1177 expanded)
%              Maximal formula depth    :   47 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

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

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

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

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(t50_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t71_funct_1])).

fof(c_0_20,plain,(
    ! [X98,X99] : k1_setfam_1(k2_tarski(X98,X99)) = k3_xboole_0(X98,X99) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X59,X60] : k3_tarski(k2_tarski(X59,X60)) = k2_xboole_0(X59,X60) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r2_hidden(esk5_0,k3_xboole_0(k1_relat_1(esk7_0),esk6_0))
    & k1_funct_1(k7_relat_1(esk7_0,esk6_0),esk5_0) != k1_funct_1(esk7_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X37,X38,X39,X40] : k3_enumset1(X37,X37,X38,X39,X40) = k2_enumset1(X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X41,X42,X43,X44,X45] : k4_enumset1(X41,X41,X42,X43,X44,X45) = k3_enumset1(X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X46,X47,X48,X49,X50,X51] : k5_enumset1(X46,X46,X47,X48,X49,X50,X51) = k4_enumset1(X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58] : k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58) = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_enumset1(X15,X14,X13,X12) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_32,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22] : k5_enumset1(X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k4_enumset1(X16,X17,X18,X19,X20,X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_33,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] : k6_enumset1(X23,X24,X25,X26,X27,X28,X29,X30) = k2_xboole_0(k4_enumset1(X23,X24,X25,X26,X27,X28),k2_tarski(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_0,k3_xboole_0(k1_relat_1(esk7_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
    ! [X85,X86,X87,X88,X89,X91,X94,X95,X96,X97] :
      ( ( ~ r2_hidden(X87,X86)
        | ~ r2_hidden(X88,X85)
        | r2_hidden(X87,X88)
        | X86 != k1_setfam_1(X85)
        | X85 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X85,X86,X89),X85)
        | r2_hidden(X89,X86)
        | X86 != k1_setfam_1(X85)
        | X85 = k1_xboole_0 )
      & ( ~ r2_hidden(X89,esk2_3(X85,X86,X89))
        | r2_hidden(X89,X86)
        | X86 != k1_setfam_1(X85)
        | X85 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X85,X91),X85)
        | ~ r2_hidden(esk3_2(X85,X91),X91)
        | X91 = k1_setfam_1(X85)
        | X85 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X85,X91),esk4_2(X85,X91))
        | ~ r2_hidden(esk3_2(X85,X91),X91)
        | X91 = k1_setfam_1(X85)
        | X85 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X85,X91),X91)
        | ~ r2_hidden(X94,X85)
        | r2_hidden(esk3_2(X85,X91),X94)
        | X91 = k1_setfam_1(X85)
        | X85 = k1_xboole_0 )
      & ( X96 != k1_setfam_1(X95)
        | X96 = k1_xboole_0
        | X95 != k1_xboole_0 )
      & ( X97 != k1_xboole_0
        | X97 = k1_setfam_1(X95)
        | X95 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,k1_setfam_1(k6_enumset1(k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_25]),c_0_46]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_25]),c_0_46]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,k1_setfam_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0)))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_56,plain,(
    ! [X64,X65,X66,X67,X68,X69,X70,X71,X72,X73,X74,X75,X76,X77,X78,X79,X80,X81,X82,X83] :
      ( ( ~ r2_hidden(X73,X72)
        | X73 = X64
        | X73 = X65
        | X73 = X66
        | X73 = X67
        | X73 = X68
        | X73 = X69
        | X73 = X70
        | X73 = X71
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X64
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X65
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X66
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X67
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X68
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X69
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X70
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( X74 != X71
        | r2_hidden(X74,X72)
        | X72 != k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X75
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X76
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X77
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X78
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X79
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X80
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X81
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) != X82
        | ~ r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) )
      & ( r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X75
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X76
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X77
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X78
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X79
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X80
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X81
        | esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83) = X82
        | X83 = k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_57,plain,(
    ! [X61,X62,X63] : k2_xboole_0(k2_tarski(X61,X62),X63) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t50_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X11] : k2_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,k1_setfam_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_64,plain,(
    ! [X100,X101,X102] :
      ( ( r2_hidden(X100,X101)
        | ~ r2_hidden(X100,k1_relat_1(k7_relat_1(X102,X101)))
        | ~ v1_relat_1(X102) )
      & ( r2_hidden(X100,k1_relat_1(X102))
        | ~ r2_hidden(X100,k1_relat_1(k7_relat_1(X102,X101)))
        | ~ v1_relat_1(X102) )
      & ( ~ r2_hidden(X100,X101)
        | ~ r2_hidden(X100,k1_relat_1(X102))
        | r2_hidden(X100,k1_relat_1(k7_relat_1(X102,X101)))
        | ~ v1_relat_1(X102) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0)) = k1_xboole_0
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).

cnf(c_0_67,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_25]),c_0_46]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_68,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_46]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X2,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0)) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X1,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_69])])).

fof(c_0_75,plain,(
    ! [X103,X104,X105] :
      ( ~ v1_relat_1(X105)
      | ~ v1_funct_1(X105)
      | ~ r2_hidden(X103,k1_relat_1(k7_relat_1(X105,X104)))
      | k1_funct_1(k7_relat_1(X105,X104),X103) = k1_funct_1(X105,X103) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,X2)))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0)) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_74])).

cnf(c_0_79,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(k7_relat_1(esk7_0,X1)))
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_78,c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,X1),X2) = k1_funct_1(esk7_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(esk7_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_71])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(k7_relat_1(esk7_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk7_0,esk6_0),esk5_0) != k1_funct_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:02:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.19/0.38  # and selection function SelectNegativeLiterals.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t71_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 0.19/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.38  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.19/0.38  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.19/0.38  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.19/0.38  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.19/0.38  fof(t50_zfmisc_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.19/0.38  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.38  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.19/0.38  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 0.19/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t71_funct_1])).
% 0.19/0.38  fof(c_0_20, plain, ![X98, X99]:k1_setfam_1(k2_tarski(X98,X99))=k3_xboole_0(X98,X99), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.38  fof(c_0_21, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_22, plain, ![X59, X60]:k3_tarski(k2_tarski(X59,X60))=k2_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.38  fof(c_0_23, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(r2_hidden(esk5_0,k3_xboole_0(k1_relat_1(esk7_0),esk6_0))&k1_funct_1(k7_relat_1(esk7_0,esk6_0),esk5_0)!=k1_funct_1(esk7_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.19/0.38  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  fof(c_0_26, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_27, plain, ![X37, X38, X39, X40]:k3_enumset1(X37,X37,X38,X39,X40)=k2_enumset1(X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.38  fof(c_0_28, plain, ![X41, X42, X43, X44, X45]:k4_enumset1(X41,X41,X42,X43,X44,X45)=k3_enumset1(X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.38  fof(c_0_29, plain, ![X46, X47, X48, X49, X50, X51]:k5_enumset1(X46,X46,X47,X48,X49,X50,X51)=k4_enumset1(X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.38  fof(c_0_30, plain, ![X52, X53, X54, X55, X56, X57, X58]:k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58)=k5_enumset1(X52,X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.38  fof(c_0_31, plain, ![X12, X13, X14, X15]:k2_enumset1(X12,X13,X14,X15)=k2_enumset1(X15,X14,X13,X12), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.19/0.38  fof(c_0_32, plain, ![X16, X17, X18, X19, X20, X21, X22]:k5_enumset1(X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k4_enumset1(X16,X17,X18,X19,X20,X21),k1_tarski(X22)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 0.19/0.38  fof(c_0_33, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  cnf(c_0_34, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_35, plain, ![X23, X24, X25, X26, X27, X28, X29, X30]:k6_enumset1(X23,X24,X25,X26,X27,X28,X29,X30)=k2_xboole_0(k4_enumset1(X23,X24,X25,X26,X27,X28),k2_tarski(X29,X30)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk5_0,k3_xboole_0(k1_relat_1(esk7_0),esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_37, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_43, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_44, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_46, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_25])).
% 0.19/0.38  cnf(c_0_47, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  fof(c_0_48, plain, ![X85, X86, X87, X88, X89, X91, X94, X95, X96, X97]:((((~r2_hidden(X87,X86)|(~r2_hidden(X88,X85)|r2_hidden(X87,X88))|X86!=k1_setfam_1(X85)|X85=k1_xboole_0)&((r2_hidden(esk2_3(X85,X86,X89),X85)|r2_hidden(X89,X86)|X86!=k1_setfam_1(X85)|X85=k1_xboole_0)&(~r2_hidden(X89,esk2_3(X85,X86,X89))|r2_hidden(X89,X86)|X86!=k1_setfam_1(X85)|X85=k1_xboole_0)))&(((r2_hidden(esk4_2(X85,X91),X85)|~r2_hidden(esk3_2(X85,X91),X91)|X91=k1_setfam_1(X85)|X85=k1_xboole_0)&(~r2_hidden(esk3_2(X85,X91),esk4_2(X85,X91))|~r2_hidden(esk3_2(X85,X91),X91)|X91=k1_setfam_1(X85)|X85=k1_xboole_0))&(r2_hidden(esk3_2(X85,X91),X91)|(~r2_hidden(X94,X85)|r2_hidden(esk3_2(X85,X91),X94))|X91=k1_setfam_1(X85)|X85=k1_xboole_0)))&((X96!=k1_setfam_1(X95)|X96=k1_xboole_0|X95!=k1_xboole_0)&(X97!=k1_xboole_0|X97=k1_setfam_1(X95)|X95!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,k1_setfam_1(k6_enumset1(k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.38  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.19/0.38  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_25]), c_0_46]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.19/0.38  cnf(c_0_52, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_25]), c_0_46]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.19/0.38  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_0,k1_setfam_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0))))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_55, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  fof(c_0_56, plain, ![X64, X65, X66, X67, X68, X69, X70, X71, X72, X73, X74, X75, X76, X77, X78, X79, X80, X81, X82, X83]:(((~r2_hidden(X73,X72)|(X73=X64|X73=X65|X73=X66|X73=X67|X73=X68|X73=X69|X73=X70|X73=X71)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71))&((((((((X74!=X64|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71))&(X74!=X65|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(X74!=X66|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(X74!=X67|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(X74!=X68|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(X74!=X69|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(X74!=X70|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(X74!=X71|r2_hidden(X74,X72)|X72!=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71))))&(((((((((esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X75|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82))&(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X76|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))&(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X77|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))&(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X78|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))&(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X79|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))&(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X80|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))&(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X81|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))&(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)!=X82|~r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))&(r2_hidden(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83),X83)|(esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X75|esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X76|esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X77|esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X78|esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X79|esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X80|esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X81|esk1_9(X75,X76,X77,X78,X79,X80,X81,X82,X83)=X82)|X83=k6_enumset1(X75,X76,X77,X78,X79,X80,X81,X82)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.19/0.38  fof(c_0_57, plain, ![X61, X62, X63]:k2_xboole_0(k2_tarski(X61,X62),X63)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t50_zfmisc_1])).
% 0.19/0.38  fof(c_0_58, plain, ![X11]:k2_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.38  cnf(c_0_59, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,k1_setfam_1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55])).
% 0.19/0.38  cnf(c_0_61, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.38  cnf(c_0_62, plain, (k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.38  cnf(c_0_63, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.38  fof(c_0_64, plain, ![X100, X101, X102]:(((r2_hidden(X100,X101)|~r2_hidden(X100,k1_relat_1(k7_relat_1(X102,X101)))|~v1_relat_1(X102))&(r2_hidden(X100,k1_relat_1(X102))|~r2_hidden(X100,k1_relat_1(k7_relat_1(X102,X101)))|~v1_relat_1(X102)))&(~r2_hidden(X100,X101)|~r2_hidden(X100,k1_relat_1(X102))|r2_hidden(X100,k1_relat_1(k7_relat_1(X102,X101)))|~v1_relat_1(X102))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0))=k1_xboole_0|r2_hidden(esk5_0,X1)|~r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.38  cnf(c_0_66, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).
% 0.19/0.38  cnf(c_0_67, plain, (k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_25]), c_0_46]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.19/0.38  cnf(c_0_68, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_46]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.38  cnf(c_0_69, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X2,X10)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.38  cnf(c_0_70, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0))=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.38  cnf(c_0_73, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.38  cnf(c_0_74, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X1,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_69])])).
% 0.19/0.38  fof(c_0_75, plain, ![X103, X104, X105]:(~v1_relat_1(X105)|~v1_funct_1(X105)|(~r2_hidden(X103,k1_relat_1(k7_relat_1(X105,X104)))|k1_funct_1(k7_relat_1(X105,X104),X103)=k1_funct_1(X105,X103))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,k1_relat_1(k7_relat_1(esk7_0,X2)))|~r2_hidden(X1,k1_relat_1(esk7_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk7_0))), inference(sr,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k1_relat_1(esk7_0))=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_74])).
% 0.19/0.38  cnf(c_0_79, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(k7_relat_1(esk7_0,X1)))|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[c_0_78, c_0_73])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (k1_funct_1(k7_relat_1(esk7_0,X1),X2)=k1_funct_1(esk7_0,X2)|~r2_hidden(X2,k1_relat_1(k7_relat_1(esk7_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_71])])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(k7_relat_1(esk7_0,esk6_0)))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (k1_funct_1(k7_relat_1(esk7_0,esk6_0),esk5_0)!=k1_funct_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 87
% 0.19/0.38  # Proof object clause steps            : 48
% 0.19/0.38  # Proof object formula steps           : 39
% 0.19/0.38  # Proof object conjectures             : 20
% 0.19/0.38  # Proof object clause conjectures      : 17
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 19
% 0.19/0.38  # Proof object generating inferences   : 9
% 0.19/0.38  # Proof object simplifying inferences  : 111
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 19
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 48
% 0.19/0.38  # Removed in clause preprocessing      : 9
% 0.19/0.38  # Initial clauses in saturation        : 39
% 0.19/0.38  # Processed clauses                    : 133
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 17
% 0.19/0.38  # ...remaining for further processing  : 115
% 0.19/0.38  # Other redundant clauses eliminated   : 24
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 254
% 0.19/0.38  # ...of the previous two non-trivial   : 200
% 0.19/0.38  # Contextual simplify-reflections      : 4
% 0.19/0.38  # Paramodulations                      : 234
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 24
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 54
% 0.19/0.38  #    Positive orientable unit clauses  : 20
% 0.19/0.38  #    Positive unorientable unit clauses: 2
% 0.19/0.38  #    Negative unit clauses             : 6
% 0.19/0.38  #    Non-unit-clauses                  : 26
% 0.19/0.38  # Current number of unprocessed clauses: 142
% 0.19/0.38  # ...number of literals in the above   : 400
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 56
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 276
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 220
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 18
% 0.19/0.38  # Unit Clause-clause subsumption calls : 66
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 188
% 0.19/0.38  # BW rewrite match successes           : 32
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6224
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
