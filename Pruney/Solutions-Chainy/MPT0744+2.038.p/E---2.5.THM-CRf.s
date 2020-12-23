%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:27 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 876 expanded)
%              Number of clauses        :   58 ( 345 expanded)
%              Number of leaves         :   19 ( 250 expanded)
%              Depth                    :   14
%              Number of atoms          :  320 (1856 expanded)
%              Number of equality atoms :  131 ( 796 expanded)
%              Maximal formula depth    :   47 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

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

fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

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

fof(c_0_19,plain,(
    ! [X57,X58] : k3_tarski(k2_tarski(X57,X58)) = k2_xboole_0(X57,X58) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X18)
        | r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X35,X36,X37,X38] : k3_enumset1(X35,X35,X36,X37,X38) = k2_enumset1(X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X39,X40,X41,X42,X43] : k4_enumset1(X39,X39,X40,X41,X42,X43) = k3_enumset1(X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X44,X45,X46,X47,X48,X49] : k5_enumset1(X44,X44,X45,X46,X47,X48,X49) = k4_enumset1(X44,X45,X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56] : k6_enumset1(X50,X50,X51,X52,X53,X54,X55,X56) = k5_enumset1(X50,X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_30,plain,(
    ! [X81] : k1_ordinal1(X81) = k2_xboole_0(X81,k1_tarski(X81)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_31,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X22
        | X23 != k1_tarski(X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_tarski(X22) )
      & ( ~ r2_hidden(esk2_2(X26,X27),X27)
        | esk2_2(X26,X27) != X26
        | X27 = k1_tarski(X26) )
      & ( r2_hidden(esk2_2(X26,X27),X27)
        | esk2_2(X26,X27) = X26
        | X27 = k1_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,negated_conjecture,
    ( v3_ordinal1(esk5_0)
    & v3_ordinal1(esk6_0)
    & ( ~ r2_hidden(esk5_0,k1_ordinal1(esk6_0))
      | ~ r1_ordinal1(esk5_0,esk6_0) )
    & ( r2_hidden(esk5_0,k1_ordinal1(esk6_0))
      | r1_ordinal1(esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_41,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,k1_ordinal1(esk6_0))
    | r1_ordinal1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_42]),c_0_23]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk6_0)
    | r2_hidden(esk5_0,k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_23]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

fof(c_0_50,plain,(
    ! [X88,X89] :
      ( ~ v3_ordinal1(X88)
      | ~ v3_ordinal1(X89)
      | r1_ordinal1(X88,X89)
      | r2_hidden(X89,X88) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_52,plain,(
    ! [X86,X87] :
      ( ( ~ r1_ordinal1(X86,X87)
        | r1_tarski(X86,X87)
        | ~ v3_ordinal1(X86)
        | ~ v3_ordinal1(X87) )
      & ( ~ r1_tarski(X86,X87)
        | r1_ordinal1(X86,X87)
        | ~ v3_ordinal1(X86)
        | ~ v3_ordinal1(X87) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk6_0)
    | r2_hidden(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_ordinal1(esk6_0))
    | ~ r1_ordinal1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_60,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = esk6_0
    | r1_ordinal1(esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_63,plain,(
    ! [X90,X91] :
      ( ~ r2_hidden(X90,X91)
      | ~ r1_tarski(X91,X90) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_64,negated_conjecture,
    ( r1_ordinal1(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_46]),c_0_23]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r1_ordinal1(X1,esk6_0)
    | r2_hidden(esk6_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_59])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = esk6_0
    | r1_tarski(esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_59]),c_0_56])])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_ordinal1(esk6_0,esk5_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_56])).

cnf(c_0_74,negated_conjecture,
    ( esk5_0 = esk6_0
    | ~ r1_tarski(esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_71]),c_0_56]),c_0_59])])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_77,plain,(
    ! [X82,X83,X84] :
      ( ( ~ v1_ordinal1(X82)
        | ~ r2_hidden(X83,X82)
        | r1_tarski(X83,X82) )
      & ( r2_hidden(esk4_1(X84),X84)
        | v1_ordinal1(X84) )
      & ( ~ r1_tarski(esk4_1(X84),X84)
        | v1_ordinal1(X84) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( esk5_0 = esk6_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_82,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( esk5_0 = esk6_0
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

fof(c_0_84,plain,(
    ! [X80] :
      ( ( v1_ordinal1(X80)
        | ~ v3_ordinal1(X80) )
      & ( v2_ordinal1(X80)
        | ~ v3_ordinal1(X80) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_80])).

fof(c_0_86,plain,(
    ! [X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71,X72,X73,X74,X75,X76,X77,X78] :
      ( ( ~ r2_hidden(X68,X67)
        | X68 = X59
        | X68 = X60
        | X68 = X61
        | X68 = X62
        | X68 = X63
        | X68 = X64
        | X68 = X65
        | X68 = X66
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X59
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X60
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X61
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X62
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X63
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X64
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X65
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( X69 != X66
        | r2_hidden(X69,X67)
        | X67 != k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X70
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X71
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X72
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X73
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X74
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X75
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X76
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) != X77
        | ~ r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) )
      & ( r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X70
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X71
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X72
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X73
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X74
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X75
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X76
        | esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78) = X77
        | X78 = k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 = esk6_0
    | ~ v1_ordinal1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_74])).

cnf(c_0_89,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_85])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_56])])).

cnf(c_0_94,negated_conjecture,
    ( r1_ordinal1(esk6_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_59]),c_0_90])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_91])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_93]),c_0_95])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:54:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.15/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.15/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.15/0.40  #
% 0.15/0.40  # Preprocessing time       : 0.029 s
% 0.15/0.40  # Presaturation interreduction done
% 0.15/0.40  
% 0.15/0.40  # Proof found!
% 0.15/0.40  # SZS status Theorem
% 0.15/0.40  # SZS output start CNFRefutation
% 0.15/0.40  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.15/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.40  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.15/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.15/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.15/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.15/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.15/0.40  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.15/0.40  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.15/0.40  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.15/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.15/0.40  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.15/0.40  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.15/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.15/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.15/0.40  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.15/0.40  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.15/0.40  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.15/0.40  fof(c_0_19, plain, ![X57, X58]:k3_tarski(k2_tarski(X57,X58))=k2_xboole_0(X57,X58), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.15/0.40  fof(c_0_20, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.40  fof(c_0_21, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk1_3(X16,X17,X18),X16)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk1_3(X16,X17,X18),X17)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk1_3(X16,X17,X18),X18)|(r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.15/0.40  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.40  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.40  fof(c_0_24, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.15/0.40  fof(c_0_25, plain, ![X35, X36, X37, X38]:k3_enumset1(X35,X35,X36,X37,X38)=k2_enumset1(X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.15/0.40  fof(c_0_26, plain, ![X39, X40, X41, X42, X43]:k4_enumset1(X39,X39,X40,X41,X42,X43)=k3_enumset1(X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.15/0.40  fof(c_0_27, plain, ![X44, X45, X46, X47, X48, X49]:k5_enumset1(X44,X44,X45,X46,X47,X48,X49)=k4_enumset1(X44,X45,X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.15/0.40  fof(c_0_28, plain, ![X50, X51, X52, X53, X54, X55, X56]:k6_enumset1(X50,X50,X51,X52,X53,X54,X55,X56)=k5_enumset1(X50,X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.15/0.40  fof(c_0_29, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.15/0.40  fof(c_0_30, plain, ![X81]:k1_ordinal1(X81)=k2_xboole_0(X81,k1_tarski(X81)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.15/0.40  fof(c_0_31, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.40  fof(c_0_32, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|X24=X22|X23!=k1_tarski(X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_tarski(X22)))&((~r2_hidden(esk2_2(X26,X27),X27)|esk2_2(X26,X27)!=X26|X27=k1_tarski(X26))&(r2_hidden(esk2_2(X26,X27),X27)|esk2_2(X26,X27)=X26|X27=k1_tarski(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.15/0.40  cnf(c_0_33, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.40  cnf(c_0_34, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.15/0.40  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.40  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.40  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.15/0.40  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.40  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.40  fof(c_0_40, negated_conjecture, (v3_ordinal1(esk5_0)&(v3_ordinal1(esk6_0)&((~r2_hidden(esk5_0,k1_ordinal1(esk6_0))|~r1_ordinal1(esk5_0,esk6_0))&(r2_hidden(esk5_0,k1_ordinal1(esk6_0))|r1_ordinal1(esk5_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.15/0.40  cnf(c_0_41, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.15/0.40  cnf(c_0_42, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.15/0.40  cnf(c_0_43, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.15/0.40  cnf(c_0_44, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.15/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,k1_ordinal1(esk6_0))|r1_ordinal1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_46, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.15/0.40  cnf(c_0_47, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_42]), c_0_23]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.15/0.40  cnf(c_0_48, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_44])).
% 0.15/0.40  cnf(c_0_49, negated_conjecture, (r1_ordinal1(esk5_0,esk6_0)|r2_hidden(esk5_0,k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_23]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.15/0.40  fof(c_0_50, plain, ![X88, X89]:(~v3_ordinal1(X88)|(~v3_ordinal1(X89)|(r1_ordinal1(X88,X89)|r2_hidden(X89,X88)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.15/0.40  cnf(c_0_51, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.40  fof(c_0_52, plain, ![X86, X87]:((~r1_ordinal1(X86,X87)|r1_tarski(X86,X87)|(~v3_ordinal1(X86)|~v3_ordinal1(X87)))&(~r1_tarski(X86,X87)|r1_ordinal1(X86,X87)|(~v3_ordinal1(X86)|~v3_ordinal1(X87)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.15/0.40  cnf(c_0_53, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_47])).
% 0.15/0.40  cnf(c_0_54, negated_conjecture, (r1_ordinal1(esk5_0,esk6_0)|r2_hidden(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.15/0.40  cnf(c_0_55, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.15/0.40  cnf(c_0_56, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_57, negated_conjecture, (~r2_hidden(esk5_0,k1_ordinal1(esk6_0))|~r1_ordinal1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_58, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.15/0.40  cnf(c_0_59, negated_conjecture, (v3_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  fof(c_0_60, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.15/0.40  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.15/0.40  cnf(c_0_62, negated_conjecture, (esk5_0=esk6_0|r1_ordinal1(esk5_0,esk6_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.15/0.40  fof(c_0_63, plain, ![X90, X91]:(~r2_hidden(X90,X91)|~r1_tarski(X91,X90)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.15/0.40  cnf(c_0_64, negated_conjecture, (r1_ordinal1(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.15/0.40  cnf(c_0_65, negated_conjecture, (~r1_ordinal1(esk5_0,esk6_0)|~r2_hidden(esk5_0,k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_46]), c_0_23]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.15/0.40  cnf(c_0_66, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_58])).
% 0.15/0.40  cnf(c_0_67, negated_conjecture, (r1_ordinal1(X1,esk6_0)|r2_hidden(esk6_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_59])).
% 0.15/0.40  cnf(c_0_68, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.15/0.40  cnf(c_0_69, negated_conjecture, (esk5_0=esk6_0|r1_tarski(esk5_0,esk6_0)|r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_59]), c_0_56])])).
% 0.15/0.40  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.15/0.40  cnf(c_0_71, negated_conjecture, (r1_ordinal1(esk6_0,esk5_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 0.15/0.40  cnf(c_0_72, negated_conjecture, (~r1_ordinal1(esk5_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.15/0.40  cnf(c_0_73, negated_conjecture, (r1_ordinal1(esk5_0,esk6_0)|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_56])).
% 0.15/0.40  cnf(c_0_74, negated_conjecture, (esk5_0=esk6_0|~r1_tarski(esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.15/0.40  cnf(c_0_75, negated_conjecture, (r1_tarski(esk6_0,esk5_0)|r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_71]), c_0_56]), c_0_59])])).
% 0.15/0.40  cnf(c_0_76, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.40  fof(c_0_77, plain, ![X82, X83, X84]:((~v1_ordinal1(X82)|(~r2_hidden(X83,X82)|r1_tarski(X83,X82)))&((r2_hidden(esk4_1(X84),X84)|v1_ordinal1(X84))&(~r1_tarski(esk4_1(X84),X84)|v1_ordinal1(X84)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.15/0.40  cnf(c_0_78, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|~r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.15/0.40  cnf(c_0_79, negated_conjecture, (esk5_0=esk6_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.15/0.40  cnf(c_0_80, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.15/0.40  cnf(c_0_81, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.15/0.40  cnf(c_0_82, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.15/0.40  cnf(c_0_83, negated_conjecture, (esk5_0=esk6_0|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.15/0.40  fof(c_0_84, plain, ![X80]:((v1_ordinal1(X80)|~v3_ordinal1(X80))&(v2_ordinal1(X80)|~v3_ordinal1(X80))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.15/0.40  cnf(c_0_85, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_80])).
% 0.15/0.40  fof(c_0_86, plain, ![X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72, X73, X74, X75, X76, X77, X78]:(((~r2_hidden(X68,X67)|(X68=X59|X68=X60|X68=X61|X68=X62|X68=X63|X68=X64|X68=X65|X68=X66)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66))&((((((((X69!=X59|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66))&(X69!=X60|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(X69!=X61|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(X69!=X62|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(X69!=X63|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(X69!=X64|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(X69!=X65|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(X69!=X66|r2_hidden(X69,X67)|X67!=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66))))&(((((((((esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X70|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77))&(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X71|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))&(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X72|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))&(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X73|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))&(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X74|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))&(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X75|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))&(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X76|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))&(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)!=X77|~r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))&(r2_hidden(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78),X78)|(esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X70|esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X71|esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X72|esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X73|esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X74|esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X75|esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X76|esk3_9(X70,X71,X72,X73,X74,X75,X76,X77,X78)=X77)|X78=k6_enumset1(X70,X71,X72,X73,X74,X75,X76,X77)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.15/0.40  cnf(c_0_87, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_81])).
% 0.15/0.40  cnf(c_0_88, negated_conjecture, (esk5_0=esk6_0|~v1_ordinal1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_74])).
% 0.15/0.40  cnf(c_0_89, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.15/0.40  cnf(c_0_90, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_70, c_0_85])).
% 0.15/0.40  cnf(c_0_91, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.15/0.40  cnf(c_0_92, negated_conjecture, (~r1_ordinal1(esk5_0,esk6_0)|~r2_hidden(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_87])).
% 0.15/0.40  cnf(c_0_93, negated_conjecture, (esk5_0=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_56])])).
% 0.15/0.40  cnf(c_0_94, negated_conjecture, (r1_ordinal1(esk6_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_59]), c_0_90])).
% 0.15/0.40  cnf(c_0_95, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_91])])).
% 0.15/0.40  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_93]), c_0_95])]), ['proof']).
% 0.15/0.40  # SZS output end CNFRefutation
% 0.15/0.40  # Proof object total steps             : 97
% 0.15/0.40  # Proof object clause steps            : 58
% 0.15/0.40  # Proof object formula steps           : 39
% 0.15/0.40  # Proof object conjectures             : 27
% 0.15/0.40  # Proof object clause conjectures      : 24
% 0.15/0.40  # Proof object formula conjectures     : 3
% 0.15/0.40  # Proof object initial clauses used    : 25
% 0.15/0.40  # Proof object initial formulas used   : 19
% 0.15/0.40  # Proof object generating inferences   : 18
% 0.15/0.40  # Proof object simplifying inferences  : 76
% 0.15/0.40  # Training examples: 0 positive, 0 negative
% 0.15/0.40  # Parsed axioms                        : 19
% 0.15/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.40  # Initial clauses                      : 53
% 0.15/0.40  # Removed in clause preprocessing      : 9
% 0.15/0.40  # Initial clauses in saturation        : 44
% 0.15/0.40  # Processed clauses                    : 119
% 0.15/0.40  # ...of these trivial                  : 0
% 0.15/0.40  # ...subsumed                          : 3
% 0.15/0.40  # ...remaining for further processing  : 116
% 0.15/0.40  # Other redundant clauses eliminated   : 26
% 0.15/0.40  # Clauses deleted for lack of memory   : 0
% 0.15/0.40  # Backward-subsumed                    : 3
% 0.15/0.40  # Backward-rewritten                   : 19
% 0.15/0.40  # Generated clauses                    : 171
% 0.15/0.40  # ...of the previous two non-trivial   : 157
% 0.15/0.40  # Contextual simplify-reflections      : 2
% 0.15/0.40  # Paramodulations                      : 152
% 0.15/0.40  # Factorizations                       : 2
% 0.15/0.40  # Equation resolutions                 : 26
% 0.15/0.40  # Propositional unsat checks           : 0
% 0.15/0.40  #    Propositional check models        : 0
% 0.15/0.40  #    Propositional check unsatisfiable : 0
% 0.15/0.40  #    Propositional clauses             : 0
% 0.15/0.40  #    Propositional clauses after purity: 0
% 0.15/0.40  #    Propositional unsat core size     : 0
% 0.15/0.40  #    Propositional preprocessing time  : 0.000
% 0.15/0.40  #    Propositional encoding time       : 0.000
% 0.15/0.40  #    Propositional solver time         : 0.000
% 0.15/0.40  #    Success case prop preproc time    : 0.000
% 0.15/0.40  #    Success case prop encoding time   : 0.000
% 0.15/0.40  #    Success case prop solver time     : 0.000
% 0.15/0.40  # Current number of processed clauses  : 36
% 0.15/0.40  #    Positive orientable unit clauses  : 12
% 0.15/0.40  #    Positive unorientable unit clauses: 0
% 0.15/0.40  #    Negative unit clauses             : 4
% 0.15/0.40  #    Non-unit-clauses                  : 20
% 0.15/0.40  # Current number of unprocessed clauses: 122
% 0.15/0.40  # ...number of literals in the above   : 396
% 0.15/0.40  # Current number of archived formulas  : 0
% 0.15/0.40  # Current number of archived clauses   : 73
% 0.15/0.40  # Clause-clause subsumption calls (NU) : 356
% 0.15/0.40  # Rec. Clause-clause subsumption calls : 243
% 0.15/0.40  # Non-unit clause-clause subsumptions  : 8
% 0.15/0.40  # Unit Clause-clause subsumption calls : 46
% 0.15/0.40  # Rewrite failures with RHS unbound    : 0
% 0.15/0.40  # BW rewrite match attempts            : 79
% 0.15/0.40  # BW rewrite match successes           : 1
% 0.15/0.40  # Condensation attempts                : 0
% 0.15/0.40  # Condensation successes               : 0
% 0.15/0.40  # Termbank termtop insertions          : 5217
% 0.15/0.40  
% 0.15/0.40  # -------------------------------------------------
% 0.15/0.40  # User time                : 0.034 s
% 0.15/0.40  # System time              : 0.006 s
% 0.15/0.40  # Total time               : 0.040 s
% 0.15/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
