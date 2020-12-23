%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 606 expanded)
%              Number of clauses        :   55 ( 239 expanded)
%              Number of leaves         :   18 ( 172 expanded)
%              Depth                    :   12
%              Number of atoms          :  299 (1300 expanded)
%              Number of equality atoms :  129 ( 548 expanded)
%              Maximal formula depth    :   47 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

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
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk1_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk1_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk1_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk1_3(X18,X19,X20),X20)
        | r2_hidden(esk1_3(X18,X19,X20),X18)
        | r2_hidden(esk1_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X37,X38,X39,X40] : k3_enumset1(X37,X37,X38,X39,X40) = k2_enumset1(X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X41,X42,X43,X44,X45] : k4_enumset1(X41,X41,X42,X43,X44,X45) = k3_enumset1(X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X46,X47,X48,X49,X50,X51] : k5_enumset1(X46,X46,X47,X48,X49,X50,X51) = k4_enumset1(X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58] : k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58) = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_29,plain,(
    ! [X82] : k1_ordinal1(X82) = k2_xboole_0(X82,k1_tarski(X82)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_30,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_31,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X24
        | X25 != k1_tarski(X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k1_tarski(X24) )
      & ( ~ r2_hidden(esk2_2(X28,X29),X29)
        | esk2_2(X28,X29) != X28
        | X29 = k1_tarski(X28) )
      & ( r2_hidden(esk2_2(X28,X29),X29)
        | esk2_2(X28,X29) = X28
        | X29 = k1_tarski(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | ~ r1_ordinal1(esk4_0,esk5_0) )
    & ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | r1_ordinal1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_40,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_41]),c_0_22]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_22]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

fof(c_0_49,plain,(
    ! [X85,X86] :
      ( ~ v3_ordinal1(X85)
      | ~ v3_ordinal1(X86)
      | r1_ordinal1(X85,X86)
      | r2_hidden(X86,X85) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_50,plain,(
    ! [X83,X84] :
      ( ( ~ r1_ordinal1(X83,X84)
        | r1_tarski(X83,X84)
        | ~ v3_ordinal1(X83)
        | ~ v3_ordinal1(X84) )
      & ( ~ r1_tarski(X83,X84)
        | r1_ordinal1(X83,X84)
        | ~ v3_ordinal1(X83)
        | ~ v3_ordinal1(X84) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_56,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_60,plain,(
    ! [X87,X88] :
      ( ~ r2_hidden(X87,X88)
      | ~ r1_tarski(X88,X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_61,negated_conjecture,
    ( r1_ordinal1(X1,esk4_0)
    | r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | ~ r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_tarski(esk4_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_54])])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_45]),c_0_22]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_ordinal1(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_59])).

fof(c_0_72,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ r2_hidden(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( esk4_0 = esk5_0
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_68]),c_0_54]),c_0_59])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_54])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

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
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_80])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(sr,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_59]),c_0_85])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_88]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.044 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.40  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.40  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.20/0.40  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.40  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.20/0.40  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.40  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.20/0.40  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.20/0.40  fof(c_0_18, plain, ![X59, X60]:k3_tarski(k2_tarski(X59,X60))=k2_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.20/0.40  fof(c_0_19, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_20, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk1_3(X18,X19,X20),X18)|~r2_hidden(esk1_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk1_3(X18,X19,X20),X19)|~r2_hidden(esk1_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk1_3(X18,X19,X20),X20)|(r2_hidden(esk1_3(X18,X19,X20),X18)|r2_hidden(esk1_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  fof(c_0_23, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_24, plain, ![X37, X38, X39, X40]:k3_enumset1(X37,X37,X38,X39,X40)=k2_enumset1(X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  fof(c_0_25, plain, ![X41, X42, X43, X44, X45]:k4_enumset1(X41,X41,X42,X43,X44,X45)=k3_enumset1(X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.40  fof(c_0_26, plain, ![X46, X47, X48, X49, X50, X51]:k5_enumset1(X46,X46,X47,X48,X49,X50,X51)=k4_enumset1(X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.40  fof(c_0_27, plain, ![X52, X53, X54, X55, X56, X57, X58]:k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58)=k5_enumset1(X52,X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.40  fof(c_0_28, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.20/0.40  fof(c_0_29, plain, ![X82]:k1_ordinal1(X82)=k2_xboole_0(X82,k1_tarski(X82)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.20/0.40  fof(c_0_30, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_31, plain, ![X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X26,X25)|X26=X24|X25!=k1_tarski(X24))&(X27!=X24|r2_hidden(X27,X25)|X25!=k1_tarski(X24)))&((~r2_hidden(esk2_2(X28,X29),X29)|esk2_2(X28,X29)!=X28|X29=k1_tarski(X28))&(r2_hidden(esk2_2(X28,X29),X29)|esk2_2(X28,X29)=X28|X29=k1_tarski(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.40  cnf(c_0_32, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  fof(c_0_39, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&((~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0))&(r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.20/0.40  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_42, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_43, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_45, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_46, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_41]), c_0_22]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.20/0.40  cnf(c_0_47, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_22]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.20/0.40  fof(c_0_49, plain, ![X85, X86]:(~v3_ordinal1(X85)|(~v3_ordinal1(X86)|(r1_ordinal1(X85,X86)|r2_hidden(X86,X85)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.20/0.40  fof(c_0_50, plain, ![X83, X84]:((~r1_ordinal1(X83,X84)|r1_tarski(X83,X84)|(~v3_ordinal1(X83)|~v3_ordinal1(X84)))&(~r1_tarski(X83,X84)|r1_ordinal1(X83,X84)|(~v3_ordinal1(X83)|~v3_ordinal1(X84)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.20/0.40  cnf(c_0_51, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.40  cnf(c_0_53, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_55, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  fof(c_0_56, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (esk4_0=esk5_0|r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  fof(c_0_60, plain, ![X87, X88]:(~r2_hidden(X87,X88)|~r1_tarski(X88,X87)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (r1_ordinal1(X1,esk4_0)|r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_63, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.20/0.41  cnf(c_0_64, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (esk4_0=esk5_0|r1_tarski(esk4_0,esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_54])])).
% 0.20/0.41  cnf(c_0_67, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (r1_ordinal1(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_59])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_45]), c_0_22]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.20/0.41  cnf(c_0_70, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_63])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (r1_ordinal1(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_59])).
% 0.20/0.41  fof(c_0_72, plain, ![X11, X12]:(~r2_hidden(X11,X12)|~r2_hidden(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.20/0.41  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_74, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (esk4_0=esk5_0|~r1_tarski(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_68]), c_0_54]), c_0_59])])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_54])).
% 0.20/0.41  cnf(c_0_79, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.41  cnf(c_0_80, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 0.20/0.41  fof(c_0_81, plain, ![X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72, X73, X74, X75, X76, X77, X78, X79, X80]:(((~r2_hidden(X70,X69)|(X70=X61|X70=X62|X70=X63|X70=X64|X70=X65|X70=X66|X70=X67|X70=X68)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68))&((((((((X71!=X61|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68))&(X71!=X62|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X63|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X64|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X65|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X66|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X67|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68)))&(X71!=X68|r2_hidden(X71,X69)|X69!=k6_enumset1(X61,X62,X63,X64,X65,X66,X67,X68))))&(((((((((esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X72|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X73|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X74|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X75|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X76|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X77|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X78|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)!=X79|~r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))&(r2_hidden(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80),X80)|(esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X72|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X73|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X74|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X75|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X76|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X77|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X78|esk3_9(X72,X73,X74,X75,X76,X77,X78,X79,X80)=X79)|X80=k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.20/0.41  cnf(c_0_82, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_74])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.20/0.41  cnf(c_0_85, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_67, c_0_80])).
% 0.20/0.41  cnf(c_0_86, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_82])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (esk4_0=esk5_0), inference(sr,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (r1_ordinal1(esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_59]), c_0_85])).
% 0.20/0.41  cnf(c_0_90, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_88]), c_0_90])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 92
% 0.20/0.41  # Proof object clause steps            : 55
% 0.20/0.41  # Proof object formula steps           : 37
% 0.20/0.41  # Proof object conjectures             : 25
% 0.20/0.41  # Proof object clause conjectures      : 22
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 24
% 0.20/0.41  # Proof object initial formulas used   : 18
% 0.20/0.41  # Proof object generating inferences   : 15
% 0.20/0.41  # Proof object simplifying inferences  : 75
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 18
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 49
% 0.20/0.41  # Removed in clause preprocessing      : 9
% 0.20/0.41  # Initial clauses in saturation        : 40
% 0.20/0.41  # Processed clauses                    : 132
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 9
% 0.20/0.41  # ...remaining for further processing  : 123
% 0.20/0.41  # Other redundant clauses eliminated   : 25
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 3
% 0.20/0.41  # Backward-rewritten                   : 22
% 0.20/0.41  # Generated clauses                    : 214
% 0.20/0.41  # ...of the previous two non-trivial   : 204
% 0.20/0.41  # Contextual simplify-reflections      : 3
% 0.20/0.41  # Paramodulations                      : 191
% 0.20/0.41  # Factorizations                       : 2
% 0.20/0.41  # Equation resolutions                 : 25
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 39
% 0.20/0.41  #    Positive orientable unit clauses  : 12
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 10
% 0.20/0.41  #    Non-unit-clauses                  : 17
% 0.20/0.41  # Current number of unprocessed clauses: 147
% 0.20/0.41  # ...number of literals in the above   : 472
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 77
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 488
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 307
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 15
% 0.20/0.41  # Unit Clause-clause subsumption calls : 119
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 77
% 0.20/0.41  # BW rewrite match successes           : 1
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 5436
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.058 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.064 s
% 0.20/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
