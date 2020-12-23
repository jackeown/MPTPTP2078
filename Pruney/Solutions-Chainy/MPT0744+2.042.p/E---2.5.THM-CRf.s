%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:28 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  105 (4036 expanded)
%              Number of clauses        :   62 (1594 expanded)
%              Number of leaves         :   21 (1107 expanded)
%              Depth                    :   16
%              Number of atoms          :  324 (9242 expanded)
%              Number of equality atoms :  116 (2473 expanded)
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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

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

fof(c_0_21,plain,(
    ! [X53,X54] : k3_tarski(k2_tarski(X53,X54)) = k2_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_24,plain,(
    ! [X77] : k1_ordinal1(X77) = k2_xboole_0(X77,k1_tarski(X77)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_25,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
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

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k5_enumset1(X38,X38,X39,X40,X41,X42,X43) = k4_enumset1(X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_33,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50) = k5_enumset1(X44,X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | ~ r1_ordinal1(esk4_0,esk5_0) )
    & ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | r1_ordinal1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_35,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X86,X87] :
      ( ~ v3_ordinal1(X86)
      | ~ v3_ordinal1(X87)
      | r1_ordinal1(X86,X87)
      | r2_hidden(X87,X86) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | ~ r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_28]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_ordinal1(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_54,plain,(
    ! [X82,X83] :
      ( ( ~ r1_ordinal1(X82,X83)
        | r1_tarski(X82,X83)
        | ~ v3_ordinal1(X82)
        | ~ v3_ordinal1(X83) )
      & ( ~ r1_tarski(X82,X83)
        | r1_ordinal1(X82,X83)
        | ~ v3_ordinal1(X82)
        | ~ v3_ordinal1(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_55,negated_conjecture,
    ( r1_ordinal1(X1,esk4_0)
    | r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_50])).

fof(c_0_56,plain,(
    ! [X78,X79,X80] :
      ( ( ~ v1_ordinal1(X78)
        | ~ r2_hidden(X79,X78)
        | r1_tarski(X79,X78) )
      & ( r2_hidden(esk3_1(X80),X80)
        | v1_ordinal1(X80) )
      & ( ~ r1_tarski(esk3_1(X80),X80)
        | v1_ordinal1(X80) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_61,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_50]),c_0_49])])).

fof(c_0_64,plain,(
    ! [X76] :
      ( ( v1_ordinal1(X76)
        | ~ v3_ordinal1(X76) )
      & ( v2_ordinal1(X76)
        | ~ v3_ordinal1(X76) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_65,plain,(
    ! [X88,X89] :
      ( ~ r2_hidden(X88,X89)
      | ~ r1_tarski(X89,X88) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_66,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | r1_tarski(X51,k3_tarski(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_67,plain,(
    ! [X22] : k2_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ v1_ordinal1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_70,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_71,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | ~ r2_xboole_0(X20,X21) )
      & ( X20 != X21
        | ~ r2_xboole_0(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | X20 = X21
        | r2_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_50])])).

fof(c_0_78,plain,(
    ! [X84,X85] :
      ( ~ v1_ordinal1(X84)
      | ~ v3_ordinal1(X85)
      | ~ r2_xboole_0(X84,X85)
      | r2_hidden(X84,X85) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_79,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_49]),c_0_50])])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_46]),c_0_28]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_77])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_xboole_0(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_91,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0)
    | ~ v1_ordinal1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_49])])).

cnf(c_0_92,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_58])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_70]),c_0_50])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_92]),c_0_49]),c_0_50])])).

fof(c_0_96,plain,(
    ! [X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71,X72,X73,X74] :
      ( ( ~ r2_hidden(X64,X63)
        | X64 = X55
        | X64 = X56
        | X64 = X57
        | X64 = X58
        | X64 = X59
        | X64 = X60
        | X64 = X61
        | X64 = X62
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X55
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X56
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X57
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X58
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X59
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X60
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X61
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( X65 != X62
        | r2_hidden(X65,X63)
        | X63 != k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X66
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X67
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X68
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X69
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X70
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X71
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X72
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) != X73
        | ~ r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) )
      & ( r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X66
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X67
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X68
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X69
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X70
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X71
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X72
        | esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74) = X73
        | X74 = k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_94,c_0_85])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_95])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(sr,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_92])]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_103])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.13/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.39  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.13/0.39  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.13/0.39  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.13/0.39  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.13/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.39  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.13/0.39  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.13/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.39  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.13/0.39  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.13/0.39  fof(c_0_21, plain, ![X53, X54]:k3_tarski(k2_tarski(X53,X54))=k2_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.39  fof(c_0_22, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_23, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.13/0.39  fof(c_0_24, plain, ![X77]:k1_ordinal1(X77)=k2_xboole_0(X77,k1_tarski(X77)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.39  fof(c_0_25, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_26, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk1_3(X16,X17,X18),X16)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk1_3(X16,X17,X18),X17)|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk1_3(X16,X17,X18),X18)|(r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.13/0.39  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_29, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_30, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_31, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.39  fof(c_0_32, plain, ![X38, X39, X40, X41, X42, X43]:k5_enumset1(X38,X38,X39,X40,X41,X42,X43)=k4_enumset1(X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.39  fof(c_0_33, plain, ![X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50)=k5_enumset1(X44,X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.39  fof(c_0_34, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&((~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0))&(r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.13/0.39  cnf(c_0_35, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.39  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  fof(c_0_44, plain, ![X86, X87]:(~v3_ordinal1(X86)|(~v3_ordinal1(X87)|(r1_ordinal1(X86,X87)|r2_hidden(X87,X86)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_46, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.39  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.39  cnf(c_0_48, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_28]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.13/0.39  cnf(c_0_52, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_47])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (r1_ordinal1(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.39  fof(c_0_54, plain, ![X82, X83]:((~r1_ordinal1(X82,X83)|r1_tarski(X82,X83)|(~v3_ordinal1(X82)|~v3_ordinal1(X83)))&(~r1_tarski(X82,X83)|r1_ordinal1(X82,X83)|(~v3_ordinal1(X82)|~v3_ordinal1(X83)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (r1_ordinal1(X1,esk4_0)|r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_50])).
% 0.13/0.39  fof(c_0_56, plain, ![X78, X79, X80]:((~v1_ordinal1(X78)|(~r2_hidden(X79,X78)|r1_tarski(X79,X78)))&((r2_hidden(esk3_1(X80),X80)|v1_ordinal1(X80))&(~r1_tarski(esk3_1(X80),X80)|v1_ordinal1(X80)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 0.13/0.39  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (r1_ordinal1(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 0.13/0.39  cnf(c_0_61, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_50]), c_0_49])])).
% 0.13/0.39  fof(c_0_64, plain, ![X76]:((v1_ordinal1(X76)|~v3_ordinal1(X76))&(v2_ordinal1(X76)|~v3_ordinal1(X76))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.13/0.39  fof(c_0_65, plain, ![X88, X89]:(~r2_hidden(X88,X89)|~r1_tarski(X89,X88)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.39  fof(c_0_66, plain, ![X51, X52]:(~r2_hidden(X51,X52)|r1_tarski(X51,k3_tarski(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.13/0.39  fof(c_0_67, plain, ![X22]:k2_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.13/0.39  cnf(c_0_68, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~v1_ordinal1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.13/0.39  cnf(c_0_70, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.39  fof(c_0_71, plain, ![X20, X21]:(((r1_tarski(X20,X21)|~r2_xboole_0(X20,X21))&(X20!=X21|~r2_xboole_0(X20,X21)))&(~r1_tarski(X20,X21)|X20=X21|r2_xboole_0(X20,X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.39  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.39  cnf(c_0_73, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.39  cnf(c_0_74, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.39  cnf(c_0_75, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_50])])).
% 0.13/0.39  fof(c_0_78, plain, ![X84, X85]:(~v1_ordinal1(X84)|(~v3_ordinal1(X85)|(~r2_xboole_0(X84,X85)|r2_hidden(X84,X85)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.13/0.39  cnf(c_0_79, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_58]), c_0_49]), c_0_50])])).
% 0.13/0.39  cnf(c_0_81, plain, (~r2_hidden(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.39  cnf(c_0_82, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.39  cnf(c_0_83, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_75])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_46]), c_0_28]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_77])).
% 0.13/0.39  cnf(c_0_86, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (esk5_0=esk4_0|r2_xboole_0(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.13/0.39  cnf(c_0_88, plain, (~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.13/0.39  cnf(c_0_89, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.13/0.39  cnf(c_0_90, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_91, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)|~v1_ordinal1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_49])])).
% 0.13/0.39  cnf(c_0_92, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_58])).
% 0.13/0.39  cnf(c_0_93, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.13/0.39  cnf(c_0_94, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk4_0,esk5_0)|r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_70]), c_0_50])])).
% 0.13/0.39  cnf(c_0_95, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_92]), c_0_49]), c_0_50])])).
% 0.13/0.39  fof(c_0_96, plain, ![X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72, X73, X74]:(((~r2_hidden(X64,X63)|(X64=X55|X64=X56|X64=X57|X64=X58|X64=X59|X64=X60|X64=X61|X64=X62)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62))&((((((((X65!=X55|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62))&(X65!=X56|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(X65!=X57|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(X65!=X58|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(X65!=X59|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(X65!=X60|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(X65!=X61|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62)))&(X65!=X62|r2_hidden(X65,X63)|X63!=k6_enumset1(X55,X56,X57,X58,X59,X60,X61,X62))))&(((((((((esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X66|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73))&(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X67|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))&(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X68|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))&(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X69|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))&(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X70|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))&(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X71|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))&(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X72|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))&(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)!=X73|~r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))&(r2_hidden(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74),X74)|(esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X66|esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X67|esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X68|esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X69|esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X70|esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X71|esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X72|esk2_9(X66,X67,X68,X69,X70,X71,X72,X73,X74)=X73)|X74=k6_enumset1(X66,X67,X68,X69,X70,X71,X72,X73)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.13/0.39  cnf(c_0_97, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_93])).
% 0.13/0.39  cnf(c_0_98, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[c_0_94, c_0_85])).
% 0.13/0.39  cnf(c_0_99, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_95])).
% 0.13/0.39  cnf(c_0_100, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.13/0.39  cnf(c_0_101, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_97])).
% 0.13/0.39  cnf(c_0_102, negated_conjecture, (esk5_0=esk4_0), inference(sr,[status(thm)],[c_0_98, c_0_99])).
% 0.13/0.39  cnf(c_0_103, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_100])])).
% 0.13/0.39  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_92])]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_103])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 105
% 0.13/0.39  # Proof object clause steps            : 62
% 0.13/0.39  # Proof object formula steps           : 43
% 0.13/0.39  # Proof object conjectures             : 31
% 0.13/0.39  # Proof object clause conjectures      : 28
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 26
% 0.13/0.39  # Proof object initial formulas used   : 21
% 0.13/0.39  # Proof object generating inferences   : 21
% 0.13/0.39  # Proof object simplifying inferences  : 89
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 21
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 52
% 0.13/0.39  # Removed in clause preprocessing      : 9
% 0.13/0.39  # Initial clauses in saturation        : 43
% 0.13/0.39  # Processed clauses                    : 168
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 24
% 0.13/0.39  # ...remaining for further processing  : 142
% 0.13/0.39  # Other redundant clauses eliminated   : 21
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 7
% 0.13/0.39  # Backward-rewritten                   : 22
% 0.13/0.39  # Generated clauses                    : 170
% 0.13/0.39  # ...of the previous two non-trivial   : 159
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 149
% 0.13/0.39  # Factorizations                       : 2
% 0.13/0.39  # Equation resolutions                 : 21
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 51
% 0.13/0.39  #    Positive orientable unit clauses  : 13
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 16
% 0.13/0.39  #    Non-unit-clauses                  : 22
% 0.13/0.39  # Current number of unprocessed clauses: 77
% 0.13/0.39  # ...number of literals in the above   : 174
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 87
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 297
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 211
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 13
% 0.13/0.39  # Unit Clause-clause subsumption calls : 136
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 82
% 0.13/0.39  # BW rewrite match successes           : 4
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 4866
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.041 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
