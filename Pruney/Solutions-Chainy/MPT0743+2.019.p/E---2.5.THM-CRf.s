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
% DateTime   : Thu Dec  3 10:56:18 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 (5302 expanded)
%              Number of clauses        :   53 (2055 expanded)
%              Number of leaves         :   19 (1566 expanded)
%              Depth                    :   10
%              Number of atoms          :  294 (8710 expanded)
%              Number of equality atoms :  110 (4431 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

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

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_20,plain,(
    ! [X75] : k1_ordinal1(X75) = k2_xboole_0(X75,k1_tarski(X75)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_21,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X52,X53] : k3_tarski(k2_tarski(X52,X53)) = k2_xboole_0(X52,X53) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X83,X84] :
      ( ~ r2_hidden(X83,X84)
      | ~ r1_tarski(X84,X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_25,plain,(
    ! [X76,X77] :
      ( ( ~ r1_ordinal1(X76,X77)
        | r1_tarski(X76,X77)
        | ~ v3_ordinal1(X76)
        | ~ v3_ordinal1(X77) )
      & ( ~ r1_tarski(X76,X77)
        | r1_ordinal1(X76,X77)
        | ~ v3_ordinal1(X76)
        | ~ v3_ordinal1(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_26,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & ( ~ r2_hidden(esk3_0,esk4_0)
      | ~ r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) )
    & ( r2_hidden(esk3_0,esk4_0)
      | r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_27,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X28,X29,X30,X31] : k3_enumset1(X28,X28,X29,X30,X31) = k2_enumset1(X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X32,X33,X34,X35,X36] : k4_enumset1(X32,X32,X33,X34,X35,X36) = k3_enumset1(X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X37,X38,X39,X40,X41,X42] : k5_enumset1(X37,X37,X38,X39,X40,X41,X42) = k4_enumset1(X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49] : k6_enumset1(X43,X43,X44,X45,X46,X47,X48,X49) = k5_enumset1(X43,X44,X45,X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,plain,(
    ! [X80,X81] :
      ( ~ v3_ordinal1(X80)
      | ~ v3_ordinal1(X81)
      | r1_ordinal1(X80,X81)
      | r2_hidden(X81,X80) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_37,plain,(
    ! [X82] :
      ( ~ v3_ordinal1(X82)
      | v3_ordinal1(k1_ordinal1(X82)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
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

cnf(c_0_49,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_52,plain,(
    ! [X50,X51] :
      ( ( ~ r1_tarski(k1_tarski(X50),X51)
        | r2_hidden(X50,X51) )
      & ( ~ r2_hidden(X50,X51)
        | r1_tarski(k1_tarski(X50),X51) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_53,plain,(
    ! [X78,X79] :
      ( ~ v3_ordinal1(X78)
      | ~ v3_ordinal1(X79)
      | r2_hidden(X78,X79)
      | X78 = X79
      | r2_hidden(X79,X78) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_54,plain,
    ( ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_30]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_ordinal1(X1,esk4_0)
    | r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_41]),c_0_30]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))
    | ~ r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_50])])).

cnf(c_0_63,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

fof(c_0_65,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ r2_hidden(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_ordinal1(k1_ordinal1(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),esk4_0)
    | r2_hidden(esk4_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_70,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_28]),c_0_30]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_71,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(X1,esk4_0)
    | r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_50])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_58]),c_0_63])])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_41]),c_0_30]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_77,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)
    | r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_63])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( esk3_0 = esk4_0
    | r2_hidden(esk4_0,esk3_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_78]),c_0_79])).

fof(c_0_85,plain,(
    ! [X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71,X72,X73] :
      ( ( ~ r2_hidden(X63,X62)
        | X63 = X54
        | X63 = X55
        | X63 = X56
        | X63 = X57
        | X63 = X58
        | X63 = X59
        | X63 = X60
        | X63 = X61
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X54
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X55
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X56
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X57
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X58
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X59
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X60
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( X64 != X61
        | r2_hidden(X64,X62)
        | X62 != k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X65
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X66
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X67
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X68
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X69
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X70
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X71
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) != X72
        | ~ r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) )
      & ( r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X65
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X66
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X67
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X68
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X69
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X70
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X71
        | esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73) = X72
        | X73 = k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = esk4_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_81]),c_0_84])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(sr,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_89]),c_0_89]),c_0_89]),c_0_89]),c_0_89]),c_0_89]),c_0_89]),c_0_89]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.039 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.21/0.47  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.21/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.47  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.47  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.47  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.21/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.47  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.47  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.47  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.21/0.47  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.21/0.47  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.21/0.47  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.47  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.21/0.47  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.21/0.47  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.21/0.47  fof(c_0_19, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.21/0.47  fof(c_0_20, plain, ![X75]:k1_ordinal1(X75)=k2_xboole_0(X75,k1_tarski(X75)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.21/0.47  fof(c_0_21, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.47  fof(c_0_22, plain, ![X52, X53]:k3_tarski(k2_tarski(X52,X53))=k2_xboole_0(X52,X53), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.47  fof(c_0_23, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.47  fof(c_0_24, plain, ![X83, X84]:(~r2_hidden(X83,X84)|~r1_tarski(X84,X83)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.47  fof(c_0_25, plain, ![X76, X77]:((~r1_ordinal1(X76,X77)|r1_tarski(X76,X77)|(~v3_ordinal1(X76)|~v3_ordinal1(X77)))&(~r1_tarski(X76,X77)|r1_ordinal1(X76,X77)|(~v3_ordinal1(X76)|~v3_ordinal1(X77)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.21/0.47  fof(c_0_26, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&((~r2_hidden(esk3_0,esk4_0)|~r1_ordinal1(k1_ordinal1(esk3_0),esk4_0))&(r2_hidden(esk3_0,esk4_0)|r1_ordinal1(k1_ordinal1(esk3_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.21/0.47  cnf(c_0_27, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.47  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.47  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.47  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.47  fof(c_0_31, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.47  fof(c_0_32, plain, ![X28, X29, X30, X31]:k3_enumset1(X28,X28,X29,X30,X31)=k2_enumset1(X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.47  fof(c_0_33, plain, ![X32, X33, X34, X35, X36]:k4_enumset1(X32,X32,X33,X34,X35,X36)=k3_enumset1(X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.47  fof(c_0_34, plain, ![X37, X38, X39, X40, X41, X42]:k5_enumset1(X37,X37,X38,X39,X40,X41,X42)=k4_enumset1(X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.47  fof(c_0_35, plain, ![X43, X44, X45, X46, X47, X48, X49]:k6_enumset1(X43,X43,X44,X45,X46,X47,X48,X49)=k5_enumset1(X43,X44,X45,X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.47  fof(c_0_36, plain, ![X80, X81]:(~v3_ordinal1(X80)|(~v3_ordinal1(X81)|(r1_ordinal1(X80,X81)|r2_hidden(X81,X80)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.21/0.47  fof(c_0_37, plain, ![X82]:(~v3_ordinal1(X82)|v3_ordinal1(k1_ordinal1(X82))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.21/0.47  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.47  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.47  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_ordinal1(k1_ordinal1(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_41, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.47  cnf(c_0_42, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.47  cnf(c_0_43, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.47  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.47  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.47  cnf(c_0_46, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.47  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.47  fof(c_0_48, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk1_3(X18,X19,X20),X18)|~r2_hidden(esk1_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk1_3(X18,X19,X20),X19)|~r2_hidden(esk1_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk1_3(X18,X19,X20),X20)|(r2_hidden(esk1_3(X18,X19,X20),X18)|r2_hidden(esk1_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.21/0.47  cnf(c_0_49, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.47  cnf(c_0_50, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_51, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.47  fof(c_0_52, plain, ![X50, X51]:((~r1_tarski(k1_tarski(X50),X51)|r2_hidden(X50,X51))&(~r2_hidden(X50,X51)|r1_tarski(k1_tarski(X50),X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.47  fof(c_0_53, plain, ![X78, X79]:(~v3_ordinal1(X78)|(~v3_ordinal1(X79)|(r2_hidden(X78,X79)|X78=X79|r2_hidden(X79,X78)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.21/0.47  cnf(c_0_54, plain, (~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.47  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_30]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.21/0.47  cnf(c_0_56, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.47  cnf(c_0_57, negated_conjecture, (r1_ordinal1(X1,esk4_0)|r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.47  cnf(c_0_58, plain, (v3_ordinal1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_41]), c_0_30]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.21/0.47  cnf(c_0_59, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.47  cnf(c_0_60, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.47  cnf(c_0_61, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.47  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~v3_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))|~r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_50])])).
% 0.21/0.47  cnf(c_0_63, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_64, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.47  fof(c_0_65, plain, ![X11, X12]:(~r2_hidden(X11,X12)|~r2_hidden(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.21/0.47  cnf(c_0_66, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.47  cnf(c_0_67, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_ordinal1(k1_ordinal1(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_68, negated_conjecture, (r1_ordinal1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),esk4_0)|r2_hidden(esk4_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.47  cnf(c_0_69, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.47  cnf(c_0_70, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_28]), c_0_30]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.47  cnf(c_0_71, negated_conjecture, (X1=esk4_0|r2_hidden(X1,esk4_0)|r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_50])).
% 0.21/0.47  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_58]), c_0_63])])).
% 0.21/0.47  cnf(c_0_73, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_64])).
% 0.21/0.47  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.47  cnf(c_0_75, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.21/0.47  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_41]), c_0_30]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.21/0.47  cnf(c_0_77, negated_conjecture, (r1_ordinal1(k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)|r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_68, c_0_63])).
% 0.21/0.47  cnf(c_0_78, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_69])).
% 0.21/0.47  cnf(c_0_79, plain, (~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_70])).
% 0.21/0.47  cnf(c_0_80, negated_conjecture, (esk3_0=esk4_0|r2_hidden(esk4_0,esk3_0)|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_63])).
% 0.21/0.47  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.21/0.47  cnf(c_0_82, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_75])).
% 0.21/0.47  cnf(c_0_83, negated_conjecture, (r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))|~r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.47  cnf(c_0_84, negated_conjecture, (~r2_hidden(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_78]), c_0_79])).
% 0.21/0.47  fof(c_0_85, plain, ![X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72, X73]:(((~r2_hidden(X63,X62)|(X63=X54|X63=X55|X63=X56|X63=X57|X63=X58|X63=X59|X63=X60|X63=X61)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61))&((((((((X64!=X54|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61))&(X64!=X55|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(X64!=X56|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(X64!=X57|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(X64!=X58|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(X64!=X59|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(X64!=X60|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(X64!=X61|r2_hidden(X64,X62)|X62!=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61))))&(((((((((esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X65|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72))&(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X66|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))&(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X67|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))&(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X68|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))&(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X69|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))&(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X70|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))&(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X71|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))&(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)!=X72|~r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))&(r2_hidden(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73),X73)|(esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X65|esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X66|esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X67|esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X68|esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X69|esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X70|esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X71|esk2_9(X65,X66,X67,X68,X69,X70,X71,X72,X73)=X72)|X73=k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.21/0.47  cnf(c_0_86, negated_conjecture, (esk3_0=esk4_0|r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.47  cnf(c_0_87, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_81]), c_0_84])).
% 0.21/0.47  cnf(c_0_88, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.21/0.47  cnf(c_0_89, negated_conjecture, (esk3_0=esk4_0), inference(sr,[status(thm)],[c_0_86, c_0_87])).
% 0.21/0.47  cnf(c_0_90, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).
% 0.21/0.47  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_89]), c_0_89]), c_0_89]), c_0_89]), c_0_89]), c_0_89]), c_0_89]), c_0_89]), c_0_90])]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 92
% 0.21/0.47  # Proof object clause steps            : 53
% 0.21/0.47  # Proof object formula steps           : 39
% 0.21/0.47  # Proof object conjectures             : 23
% 0.21/0.47  # Proof object clause conjectures      : 20
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 24
% 0.21/0.47  # Proof object initial formulas used   : 19
% 0.21/0.47  # Proof object generating inferences   : 13
% 0.21/0.47  # Proof object simplifying inferences  : 91
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 19
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 46
% 0.21/0.47  # Removed in clause preprocessing      : 9
% 0.21/0.47  # Initial clauses in saturation        : 37
% 0.21/0.47  # Processed clauses                    : 238
% 0.21/0.47  # ...of these trivial                  : 0
% 0.21/0.47  # ...subsumed                          : 50
% 0.21/0.47  # ...remaining for further processing  : 188
% 0.21/0.47  # Other redundant clauses eliminated   : 200
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 5
% 0.21/0.47  # Backward-rewritten                   : 17
% 0.21/0.47  # Generated clauses                    : 1695
% 0.21/0.47  # ...of the previous two non-trivial   : 1137
% 0.21/0.47  # Contextual simplify-reflections      : 4
% 0.21/0.47  # Paramodulations                      : 784
% 0.21/0.47  # Factorizations                       : 712
% 0.21/0.47  # Equation resolutions                 : 200
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 110
% 0.21/0.47  #    Positive orientable unit clauses  : 11
% 0.21/0.47  #    Positive unorientable unit clauses: 0
% 0.21/0.47  #    Negative unit clauses             : 45
% 0.21/0.47  #    Non-unit-clauses                  : 54
% 0.21/0.47  # Current number of unprocessed clauses: 966
% 0.21/0.47  # ...number of literals in the above   : 4737
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 75
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 674
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 534
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 27
% 0.21/0.47  # Unit Clause-clause subsumption calls : 524
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 60
% 0.21/0.47  # BW rewrite match successes           : 2
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 19474
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.124 s
% 0.21/0.47  # System time              : 0.007 s
% 0.21/0.47  # Total time               : 0.131 s
% 0.21/0.47  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
