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
% DateTime   : Thu Dec  3 10:56:29 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 916 expanded)
%              Number of clauses        :   54 ( 359 expanded)
%              Number of leaves         :   18 ( 254 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 (2178 expanded)
%              Number of equality atoms :  146 ( 723 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

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

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(c_0_18,plain,(
    ! [X59,X60] : k3_tarski(k2_tarski(X59,X60)) = k2_xboole_0(X59,X60) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_21,plain,(
    ! [X84] : k1_ordinal1(X84) = k2_xboole_0(X84,k1_tarski(X84)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_22,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
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

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

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
    ! [X82,X83] :
      ( ~ v3_ordinal1(X82)
      | ~ v3_ordinal1(X83)
      | r1_ordinal1(X82,X83)
      | r1_ordinal1(X83,X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_32,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | ~ r1_ordinal1(esk4_0,esk5_0) )
    & ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | r1_ordinal1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_33,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X89,X90] :
      ( ~ v3_ordinal1(X89)
      | ~ v3_ordinal1(X90)
      | r1_ordinal1(X89,X90)
      | r2_hidden(X90,X89) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_43,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X20
        | X24 = X21
        | X24 = X22
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X20
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X26,X27,X28,X29) != X26
        | ~ r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk2_4(X26,X27,X28,X29) != X27
        | ~ r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk2_4(X26,X27,X28,X29) != X28
        | ~ r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( r2_hidden(esk2_4(X26,X27,X28,X29),X29)
        | esk2_4(X26,X27,X28,X29) = X26
        | esk2_4(X26,X27,X28,X29) = X27
        | esk2_4(X26,X27,X28,X29) = X28
        | X29 = k1_enumset1(X26,X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_45,plain,(
    ! [X91,X92] :
      ( ~ r2_hidden(X91,X92)
      | ~ r1_tarski(X92,X91) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_46,plain,(
    ! [X85,X86] :
      ( ( ~ r1_ordinal1(X85,X86)
        | r1_tarski(X85,X86)
        | ~ v3_ordinal1(X85)
        | ~ v3_ordinal1(X86) )
      & ( ~ r1_tarski(X85,X86)
        | r1_ordinal1(X85,X86)
        | ~ v3_ordinal1(X85)
        | ~ v3_ordinal1(X86) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_47,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | ~ r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_52,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r1_ordinal1(X1,esk5_0)
    | r1_ordinal1(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_25]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_ordinal1(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_63,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_50]),c_0_25]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_66,plain,
    ( ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk4_0)
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_59])).

cnf(c_0_70,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk4_0)
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_48]),c_0_59])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_75,plain,(
    ! [X87,X88] :
      ( ~ v3_ordinal1(X87)
      | ~ v3_ordinal1(X88)
      | r2_hidden(X87,X88)
      | X87 = X88
      | r2_hidden(X88,X87) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_76,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_72]),c_0_59]),c_0_48])]),c_0_73])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_76,c_0_77])).

fof(c_0_81,plain,(
    ! [X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71,X72,X73,X74,X75,X76,X77,X78,X79,X80] :
      ( ( ~ r2_hidden(X70,X69)
        | X70 = X61
        | X70 = X62
        | X70 = X63
        | X70 = X64
        | X70 = X65
        | X70 = X66
        | X70 = X67
        | X70 = X68
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X61
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X62
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X63
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X64
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X65
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X66
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X67
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( X71 != X68
        | r2_hidden(X71,X69)
        | X69 != k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X72
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X73
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X74
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X75
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X76
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X77
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X78
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) != X79
        | ~ r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) )
      & ( r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X72
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X73
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X74
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X75
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X76
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X77
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X78
        | esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80) = X79
        | X80 = k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_48])).

cnf(c_0_84,negated_conjecture,
    ( esk4_0 = esk5_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_80]),c_0_48]),c_0_59])])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_59]),c_0_77]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_58]),c_0_48])])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_87]),c_0_89])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:14:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.029 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.18/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.39  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.18/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.18/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.18/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.18/0.39  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.18/0.39  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.18/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.18/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.39  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.18/0.39  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.18/0.39  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.18/0.39  fof(c_0_18, plain, ![X59, X60]:k3_tarski(k2_tarski(X59,X60))=k2_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.18/0.39  fof(c_0_19, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.39  fof(c_0_20, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.18/0.39  fof(c_0_21, plain, ![X84]:k1_ordinal1(X84)=k2_xboole_0(X84,k1_tarski(X84)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.18/0.39  fof(c_0_22, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.39  fof(c_0_23, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk1_3(X16,X17,X18),X16)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk1_3(X16,X17,X18),X17)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk1_3(X16,X17,X18),X18)|(r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.18/0.39  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.39  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.39  fof(c_0_26, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.39  fof(c_0_27, plain, ![X37, X38, X39, X40]:k3_enumset1(X37,X37,X38,X39,X40)=k2_enumset1(X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.39  fof(c_0_28, plain, ![X41, X42, X43, X44, X45]:k4_enumset1(X41,X41,X42,X43,X44,X45)=k3_enumset1(X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.39  fof(c_0_29, plain, ![X46, X47, X48, X49, X50, X51]:k5_enumset1(X46,X46,X47,X48,X49,X50,X51)=k4_enumset1(X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.39  fof(c_0_30, plain, ![X52, X53, X54, X55, X56, X57, X58]:k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58)=k5_enumset1(X52,X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.18/0.39  fof(c_0_31, plain, ![X82, X83]:(~v3_ordinal1(X82)|~v3_ordinal1(X83)|(r1_ordinal1(X82,X83)|r1_ordinal1(X83,X82))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.18/0.39  fof(c_0_32, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&((~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0))&(r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.18/0.39  cnf(c_0_33, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_34, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_35, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.39  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.39  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.39  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.39  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.39  fof(c_0_42, plain, ![X89, X90]:(~v3_ordinal1(X89)|(~v3_ordinal1(X90)|(r1_ordinal1(X89,X90)|r2_hidden(X90,X89)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.18/0.39  fof(c_0_43, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X24,X23)|(X24=X20|X24=X21|X24=X22)|X23!=k1_enumset1(X20,X21,X22))&(((X25!=X20|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))&(X25!=X21|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22)))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))))&((((esk2_4(X26,X27,X28,X29)!=X26|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28))&(esk2_4(X26,X27,X28,X29)!=X27|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(esk2_4(X26,X27,X28,X29)!=X28|~r2_hidden(esk2_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(r2_hidden(esk2_4(X26,X27,X28,X29),X29)|(esk2_4(X26,X27,X28,X29)=X26|esk2_4(X26,X27,X28,X29)=X27|esk2_4(X26,X27,X28,X29)=X28)|X29=k1_enumset1(X26,X27,X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.18/0.39  cnf(c_0_44, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  fof(c_0_45, plain, ![X91, X92]:(~r2_hidden(X91,X92)|~r1_tarski(X92,X91)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.39  fof(c_0_46, plain, ![X85, X86]:((~r1_ordinal1(X85,X86)|r1_tarski(X85,X86)|(~v3_ordinal1(X85)|~v3_ordinal1(X86)))&(~r1_tarski(X85,X86)|r1_ordinal1(X85,X86)|(~v3_ordinal1(X85)|~v3_ordinal1(X86)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.18/0.39  cnf(c_0_47, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_48, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.39  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.39  cnf(c_0_50, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.39  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.39  cnf(c_0_52, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.39  cnf(c_0_53, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.39  cnf(c_0_54, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.39  cnf(c_0_55, negated_conjecture, (r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.39  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.39  cnf(c_0_58, negated_conjecture, (r1_ordinal1(X1,esk5_0)|r1_ordinal1(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.39  cnf(c_0_59, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.39  cnf(c_0_60, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_25]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.18/0.39  cnf(c_0_61, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_51])).
% 0.18/0.39  cnf(c_0_62, negated_conjecture, (r1_ordinal1(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 0.18/0.39  cnf(c_0_63, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.39  cnf(c_0_64, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_54])).
% 0.18/0.39  cnf(c_0_65, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_50]), c_0_25]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.18/0.39  cnf(c_0_66, plain, (~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.39  cnf(c_0_67, negated_conjecture, (r1_ordinal1(esk5_0,esk4_0)|r1_ordinal1(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.39  cnf(c_0_68, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.39  cnf(c_0_69, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_59])).
% 0.18/0.39  cnf(c_0_70, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_63])).
% 0.18/0.39  cnf(c_0_71, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.18/0.39  cnf(c_0_72, negated_conjecture, (r1_ordinal1(esk5_0,esk4_0)|~r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_48]), c_0_59])])).
% 0.18/0.39  cnf(c_0_73, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.39  cnf(c_0_74, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  fof(c_0_75, plain, ![X87, X88]:(~v3_ordinal1(X87)|(~v3_ordinal1(X88)|(r2_hidden(X87,X88)|X87=X88|r2_hidden(X88,X87)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.18/0.39  cnf(c_0_76, negated_conjecture, (esk4_0=esk5_0|r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.39  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_72]), c_0_59]), c_0_48])]), c_0_73])).
% 0.18/0.39  cnf(c_0_78, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.39  cnf(c_0_79, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (esk4_0=esk5_0|r1_ordinal1(esk4_0,esk5_0)), inference(sr,[status(thm)],[c_0_76, c_0_77])).
% 0.18/0.39  fof(c_0_81, plain, ![X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72, X73, X74, X75, X76, X77, X78, X79, X80]:(((~r2_hidden(X70,X69)|(X70=X61|X70=X62|X70=X63|X70=X64|X70=X65|X70=X66|X70=X67|X70=X68)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68))&((((((((X71!=X61|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68))&(X71!=X62|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X63|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X64|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X65|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X66|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X67|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X68|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68))))&(((((((((esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X72|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X73|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X74|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X75|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X76|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X77|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X78|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X79|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X72|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X73|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X74|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X75|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X76|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X77|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X78|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X79)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.18/0.39  cnf(c_0_82, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_78])).
% 0.18/0.39  cnf(c_0_83, negated_conjecture, (X1=esk5_0|r2_hidden(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_79, c_0_48])).
% 0.18/0.39  cnf(c_0_84, negated_conjecture, (esk4_0=esk5_0|~r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_80]), c_0_48]), c_0_59])])).
% 0.18/0.39  cnf(c_0_85, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.18/0.39  cnf(c_0_86, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_82])).
% 0.18/0.39  cnf(c_0_87, negated_conjecture, (esk4_0=esk5_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_59]), c_0_77]), c_0_84])).
% 0.18/0.39  cnf(c_0_88, negated_conjecture, (r1_ordinal1(esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_58]), c_0_48])])).
% 0.18/0.39  cnf(c_0_89, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).
% 0.18/0.39  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_87]), c_0_89])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 91
% 0.18/0.39  # Proof object clause steps            : 54
% 0.18/0.39  # Proof object formula steps           : 37
% 0.18/0.39  # Proof object conjectures             : 26
% 0.18/0.39  # Proof object clause conjectures      : 23
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 23
% 0.18/0.39  # Proof object initial formulas used   : 18
% 0.18/0.39  # Proof object generating inferences   : 16
% 0.18/0.39  # Proof object simplifying inferences  : 77
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 18
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 51
% 0.18/0.39  # Removed in clause preprocessing      : 9
% 0.18/0.39  # Initial clauses in saturation        : 42
% 0.18/0.39  # Processed clauses                    : 135
% 0.18/0.39  # ...of these trivial                  : 4
% 0.18/0.39  # ...subsumed                          : 5
% 0.18/0.39  # ...remaining for further processing  : 126
% 0.18/0.39  # Other redundant clauses eliminated   : 100
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 4
% 0.18/0.39  # Backward-rewritten                   : 17
% 0.18/0.39  # Generated clauses                    : 515
% 0.18/0.39  # ...of the previous two non-trivial   : 300
% 0.18/0.39  # Contextual simplify-reflections      : 2
% 0.18/0.39  # Paramodulations                      : 159
% 0.18/0.39  # Factorizations                       : 264
% 0.18/0.39  # Equation resolutions                 : 100
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 47
% 0.18/0.39  #    Positive orientable unit clauses  : 11
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 1
% 0.18/0.39  #    Non-unit-clauses                  : 35
% 0.18/0.39  # Current number of unprocessed clauses: 241
% 0.18/0.39  # ...number of literals in the above   : 1481
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 72
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 352
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 247
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.18/0.39  # Unit Clause-clause subsumption calls : 58
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 68
% 0.18/0.39  # BW rewrite match successes           : 4
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 7210
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.049 s
% 0.18/0.39  # System time              : 0.005 s
% 0.18/0.39  # Total time               : 0.055 s
% 0.18/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
