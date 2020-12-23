%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:32 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  118 (1390 expanded)
%              Number of clauses        :   81 ( 637 expanded)
%              Number of leaves         :   18 ( 338 expanded)
%              Depth                    :   24
%              Number of atoms          :  311 (4693 expanded)
%              Number of equality atoms :   63 ( 737 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t30_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

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

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_19,plain,(
    ! [X44,X45] :
      ( ~ v3_ordinal1(X44)
      | ~ v3_ordinal1(X45)
      | r2_hidden(X44,X45)
      | X44 = X45
      | r2_hidden(X45,X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_20,negated_conjecture,(
    ! [X52] :
      ( v3_ordinal1(esk7_0)
      & ( v3_ordinal1(esk8_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( v4_ordinal1(esk7_0)
        | ~ v3_ordinal1(X52)
        | ~ r2_hidden(X52,esk7_0)
        | r2_hidden(k1_ordinal1(X52),esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).

fof(c_0_21,plain,(
    ! [X37] : k1_ordinal1(X37) = k2_xboole_0(X37,k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_22,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(X19,esk2_3(X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k3_tarski(X17) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k3_tarski(X17) )
      & ( ~ r2_hidden(X21,X22)
        | ~ r2_hidden(X22,X17)
        | r2_hidden(X21,X18)
        | X18 != k3_tarski(X17) )
      & ( ~ r2_hidden(esk3_2(X23,X24),X24)
        | ~ r2_hidden(esk3_2(X23,X24),X26)
        | ~ r2_hidden(X26,X23)
        | X24 = k3_tarski(X23) )
      & ( r2_hidden(esk3_2(X23,X24),esk4_2(X23,X24))
        | r2_hidden(esk3_2(X23,X24),X24)
        | X24 = k3_tarski(X23) )
      & ( r2_hidden(esk4_2(X23,X24),X23)
        | r2_hidden(esk3_2(X23,X24),X24)
        | X24 = k3_tarski(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X47] :
      ( ~ v3_ordinal1(X47)
      | v3_ordinal1(k3_tarski(X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_ordinal1])])).

fof(c_0_27,plain,(
    ! [X48,X49] :
      ( ~ r2_hidden(X48,X49)
      | ~ r1_tarski(X49,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_28,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | r1_tarski(X28,k3_tarski(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_29,plain,(
    ! [X43] : r2_hidden(X43,k1_ordinal1(X43)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_30,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_ordinal1(X38)
        | ~ r2_hidden(X39,X38)
        | r1_tarski(X39,X38) )
      & ( r2_hidden(esk6_1(X40),X40)
        | v1_ordinal1(X40) )
      & ( ~ r1_tarski(esk6_1(X40),X40)
        | v1_ordinal1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(X1,esk7_0)
    | r2_hidden(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k1_ordinal1(X1),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( k3_tarski(X1) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_46,plain,(
    ! [X42] :
      ( ( ~ v4_ordinal1(X42)
        | X42 = k3_tarski(X42) )
      & ( X42 != k3_tarski(X42)
        | v4_ordinal1(X42) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_47,plain,
    ( r1_tarski(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(k2_xboole_0(k3_tarski(X1),k2_tarski(k3_tarski(X1),k3_tarski(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( ~ v1_ordinal1(X1)
    | ~ r2_hidden(X1,esk2_3(X1,k3_tarski(X1),X2))
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | ~ v3_ordinal1(k3_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( ~ v1_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_25])])).

fof(c_0_58,plain,(
    ! [X36] :
      ( ( v1_ordinal1(X36)
        | ~ v3_ordinal1(X36) )
      & ( v2_ordinal1(X36)
        | ~ v3_ordinal1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_60,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | ~ v1_ordinal1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_63,plain,(
    ! [X31,X32] :
      ( ( r2_hidden(esk5_2(X31,X32),X31)
        | r1_tarski(k3_tarski(X31),X32) )
      & ( ~ r1_tarski(esk5_2(X31,X32),X32)
        | r1_tarski(k3_tarski(X31),X32) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_64,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | k3_tarski(esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_25])])).

cnf(c_0_68,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

fof(c_0_72,plain,(
    ! [X30] : k3_tarski(k1_tarski(X30)) = X30 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_73,plain,(
    ! [X46] :
      ( ~ v3_ordinal1(X46)
      | v3_ordinal1(k1_ordinal1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_74,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r2_hidden(esk5_2(X1,k3_tarski(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_37])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_67])).

cnf(c_0_77,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_78,plain,(
    ! [X34,X35] : k3_tarski(k2_xboole_0(X34,X35)) = k2_xboole_0(k3_tarski(X34),k3_tarski(X35)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_79,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( v3_ordinal1(esk8_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_82,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(k2_xboole_0(X2,X3)))
    | ~ r2_hidden(esk5_2(X1,k3_tarski(k2_xboole_0(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k3_tarski(esk8_0),X1)
    | r2_hidden(esk5_2(esk8_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_79,c_0_31])).

cnf(c_0_86,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_39])).

cnf(c_0_87,negated_conjecture,
    ( v3_ordinal1(esk8_0)
    | k3_tarski(esk7_0) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_60])).

fof(c_0_88,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k3_tarski(esk8_0),k3_tarski(k2_xboole_0(esk7_0,X1))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( k3_tarski(k2_xboole_0(X1,k2_tarski(X2,X2))) = k2_xboole_0(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(X1,k2_tarski(X1,X1)) = esk7_0
    | r2_hidden(esk7_0,k2_xboole_0(X1,k2_tarski(X1,X1)))
    | r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_67])])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k3_tarski(esk8_0),k2_xboole_0(esk7_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_67])).

cnf(c_0_96,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_39])).

cnf(c_0_97,negated_conjecture,
    ( k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)),esk7_0)
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk8_0,esk7_0)
    | ~ v1_ordinal1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_71])).

cnf(c_0_99,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_100,negated_conjecture,
    ( k2_xboole_0(k3_tarski(esk8_0),k2_xboole_0(esk7_0,X1)) = k2_xboole_0(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,plain,
    ( k2_xboole_0(X1,k3_tarski(X2)) = k3_tarski(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_37])).

cnf(c_0_102,negated_conjecture,
    ( k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)) = esk7_0
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)))
    | ~ v4_ordinal1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_62]),c_0_25])])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k3_tarski(k2_xboole_0(esk8_0,X1)) = k3_tarski(X1)
    | ~ r2_hidden(esk7_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_84])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)) = esk7_0
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_60]),c_0_67])])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_103])).

cnf(c_0_108,plain,
    ( r1_tarski(k3_tarski(k2_xboole_0(X1,X2)),X3)
    | r2_hidden(esk5_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk5_2(k2_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_77])).

cnf(c_0_109,negated_conjecture,
    ( ~ r2_hidden(X1,k2_xboole_0(esk8_0,X2))
    | ~ r2_hidden(k3_tarski(X2),X1)
    | ~ r2_hidden(esk7_0,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)) = esk7_0
    | r2_hidden(esk7_0,k2_tarski(esk8_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_106]),c_0_107])).

cnf(c_0_111,plain,
    ( r1_tarski(k3_tarski(k2_xboole_0(X1,X2)),k3_tarski(X2))
    | r2_hidden(esk5_2(k2_xboole_0(X1,X2),k3_tarski(X2)),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)) = esk7_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_106]),c_0_85]),c_0_71])]),c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0)
    | r2_hidden(esk5_2(esk7_0,esk8_0),esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_67]),c_0_85]),c_0_85])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk5_2(esk7_0,esk8_0),esk8_0)
    | r1_tarski(esk7_0,esk8_0)
    | ~ v1_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_113])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk5_2(esk7_0,esk8_0),esk8_0)
    | r1_tarski(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_62]),c_0_93])])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_115]),c_0_67])])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_116]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:42:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.38/4.57  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 4.38/4.57  # and selection function PSelectComplexExceptUniqMaxHorn.
% 4.38/4.57  #
% 4.38/4.57  # Preprocessing time       : 0.028 s
% 4.38/4.57  # Presaturation interreduction done
% 4.38/4.57  
% 4.38/4.57  # Proof found!
% 4.38/4.57  # SZS status Theorem
% 4.38/4.57  # SZS output start CNFRefutation
% 4.38/4.57  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 4.38/4.57  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 4.38/4.57  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.38/4.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.38/4.57  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 4.38/4.57  fof(t30_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 4.38/4.57  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.38/4.57  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.38/4.57  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 4.38/4.57  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 4.38/4.57  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_ordinal1)).
% 4.38/4.57  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 4.38/4.57  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 4.38/4.57  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.38/4.57  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 4.38/4.57  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 4.38/4.57  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 4.38/4.57  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.38/4.57  fof(c_0_18, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 4.38/4.57  fof(c_0_19, plain, ![X44, X45]:(~v3_ordinal1(X44)|(~v3_ordinal1(X45)|(r2_hidden(X44,X45)|X44=X45|r2_hidden(X45,X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 4.38/4.57  fof(c_0_20, negated_conjecture, ![X52]:(v3_ordinal1(esk7_0)&(((v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0))&((r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0))&(~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0))))&(v4_ordinal1(esk7_0)|(~v3_ordinal1(X52)|(~r2_hidden(X52,esk7_0)|r2_hidden(k1_ordinal1(X52),esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).
% 4.38/4.57  fof(c_0_21, plain, ![X37]:k1_ordinal1(X37)=k2_xboole_0(X37,k1_tarski(X37)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 4.38/4.57  fof(c_0_22, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.38/4.57  fof(c_0_23, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:((((r2_hidden(X19,esk2_3(X17,X18,X19))|~r2_hidden(X19,X18)|X18!=k3_tarski(X17))&(r2_hidden(esk2_3(X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k3_tarski(X17)))&(~r2_hidden(X21,X22)|~r2_hidden(X22,X17)|r2_hidden(X21,X18)|X18!=k3_tarski(X17)))&((~r2_hidden(esk3_2(X23,X24),X24)|(~r2_hidden(esk3_2(X23,X24),X26)|~r2_hidden(X26,X23))|X24=k3_tarski(X23))&((r2_hidden(esk3_2(X23,X24),esk4_2(X23,X24))|r2_hidden(esk3_2(X23,X24),X24)|X24=k3_tarski(X23))&(r2_hidden(esk4_2(X23,X24),X23)|r2_hidden(esk3_2(X23,X24),X24)|X24=k3_tarski(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 4.38/4.57  cnf(c_0_24, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.38/4.57  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.38/4.57  fof(c_0_26, plain, ![X47]:(~v3_ordinal1(X47)|v3_ordinal1(k3_tarski(X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_ordinal1])])).
% 4.38/4.57  fof(c_0_27, plain, ![X48, X49]:(~r2_hidden(X48,X49)|~r1_tarski(X49,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 4.38/4.57  fof(c_0_28, plain, ![X28, X29]:(~r2_hidden(X28,X29)|r1_tarski(X28,k3_tarski(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 4.38/4.57  fof(c_0_29, plain, ![X43]:r2_hidden(X43,k1_ordinal1(X43)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 4.38/4.57  cnf(c_0_30, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.38/4.57  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.38/4.57  fof(c_0_32, plain, ![X38, X39, X40]:((~v1_ordinal1(X38)|(~r2_hidden(X39,X38)|r1_tarski(X39,X38)))&((r2_hidden(esk6_1(X40),X40)|v1_ordinal1(X40))&(~r1_tarski(esk6_1(X40),X40)|v1_ordinal1(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 4.38/4.57  cnf(c_0_33, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.38/4.57  cnf(c_0_34, negated_conjecture, (X1=esk7_0|r2_hidden(X1,esk7_0)|r2_hidden(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 4.38/4.57  cnf(c_0_35, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.38/4.57  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.38/4.57  cnf(c_0_37, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.38/4.57  cnf(c_0_38, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.38/4.57  cnf(c_0_39, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 4.38/4.57  cnf(c_0_40, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.38/4.57  cnf(c_0_41, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_33])).
% 4.38/4.57  cnf(c_0_42, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k1_ordinal1(X1),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.38/4.57  cnf(c_0_43, negated_conjecture, (k3_tarski(X1)=esk7_0|r2_hidden(esk7_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 4.38/4.57  cnf(c_0_44, plain, (~r2_hidden(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 4.38/4.57  cnf(c_0_45, plain, (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 4.38/4.57  fof(c_0_46, plain, ![X42]:((~v4_ordinal1(X42)|X42=k3_tarski(X42))&(X42!=k3_tarski(X42)|v4_ordinal1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 4.38/4.57  cnf(c_0_47, plain, (r1_tarski(esk2_3(X1,k3_tarski(X1),X2),X1)|~v1_ordinal1(X1)|~r2_hidden(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 4.38/4.57  cnf(c_0_48, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.38/4.57  cnf(c_0_49, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_42, c_0_39])).
% 4.38/4.57  cnf(c_0_50, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_43, c_0_25])).
% 4.38/4.57  cnf(c_0_51, plain, (~r2_hidden(k2_xboole_0(k3_tarski(X1),k2_tarski(k3_tarski(X1),k3_tarski(X1))),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 4.38/4.57  cnf(c_0_52, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 4.38/4.57  cnf(c_0_53, plain, (~v1_ordinal1(X1)|~r2_hidden(X1,esk2_3(X1,k3_tarski(X1),X2))|~r2_hidden(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_36, c_0_47])).
% 4.38/4.57  cnf(c_0_54, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_48])).
% 4.38/4.57  cnf(c_0_55, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|~v3_ordinal1(k3_tarski(esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])).
% 4.38/4.57  cnf(c_0_56, plain, (~v1_ordinal1(X1)|~r2_hidden(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 4.38/4.57  cnf(c_0_57, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_35]), c_0_25])])).
% 4.38/4.57  fof(c_0_58, plain, ![X36]:((v1_ordinal1(X36)|~v3_ordinal1(X36))&(v2_ordinal1(X36)|~v3_ordinal1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 4.38/4.57  cnf(c_0_59, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.38/4.57  cnf(c_0_60, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 4.38/4.57  cnf(c_0_61, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|~v1_ordinal1(esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 4.38/4.57  cnf(c_0_62, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 4.38/4.57  fof(c_0_63, plain, ![X31, X32]:((r2_hidden(esk5_2(X31,X32),X31)|r1_tarski(k3_tarski(X31),X32))&(~r1_tarski(esk5_2(X31,X32),X32)|r1_tarski(k3_tarski(X31),X32))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 4.38/4.57  fof(c_0_64, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 4.38/4.57  cnf(c_0_65, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.38/4.57  cnf(c_0_66, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|k3_tarski(esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 4.38/4.57  cnf(c_0_67, negated_conjecture, (k3_tarski(esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_25])])).
% 4.38/4.57  cnf(c_0_68, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk5_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 4.38/4.57  cnf(c_0_69, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 4.38/4.57  cnf(c_0_70, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_65])).
% 4.38/4.57  cnf(c_0_71, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 4.38/4.57  fof(c_0_72, plain, ![X30]:k3_tarski(k1_tarski(X30))=X30, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 4.38/4.57  fof(c_0_73, plain, ![X46]:(~v3_ordinal1(X46)|v3_ordinal1(k1_ordinal1(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 4.38/4.57  cnf(c_0_74, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r2_hidden(esk5_2(X1,k3_tarski(X2)),X2)), inference(spm,[status(thm)],[c_0_68, c_0_37])).
% 4.38/4.57  cnf(c_0_75, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_69])).
% 4.38/4.57  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_67])).
% 4.38/4.57  cnf(c_0_77, plain, (r2_hidden(esk5_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 4.38/4.57  fof(c_0_78, plain, ![X34, X35]:k3_tarski(k2_xboole_0(X34,X35))=k2_xboole_0(k3_tarski(X34),k3_tarski(X35)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 4.38/4.57  cnf(c_0_79, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 4.38/4.57  cnf(c_0_80, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 4.38/4.57  cnf(c_0_81, negated_conjecture, (v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.38/4.57  cnf(c_0_82, plain, (r1_tarski(k3_tarski(X1),k3_tarski(k2_xboole_0(X2,X3)))|~r2_hidden(esk5_2(X1,k3_tarski(k2_xboole_0(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 4.38/4.57  cnf(c_0_83, negated_conjecture, (r1_tarski(k3_tarski(esk8_0),X1)|r2_hidden(esk5_2(esk8_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 4.38/4.57  cnf(c_0_84, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 4.38/4.57  cnf(c_0_85, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_79, c_0_31])).
% 4.38/4.57  cnf(c_0_86, plain, (v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_80, c_0_39])).
% 4.38/4.57  cnf(c_0_87, negated_conjecture, (v3_ordinal1(esk8_0)|k3_tarski(esk7_0)!=esk7_0), inference(spm,[status(thm)],[c_0_81, c_0_60])).
% 4.38/4.57  fof(c_0_88, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.38/4.57  cnf(c_0_89, negated_conjecture, (r1_tarski(k3_tarski(esk8_0),k3_tarski(k2_xboole_0(esk7_0,X1)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 4.38/4.57  cnf(c_0_90, plain, (k3_tarski(k2_xboole_0(X1,k2_tarski(X2,X2)))=k2_xboole_0(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 4.38/4.57  cnf(c_0_91, negated_conjecture, (~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.38/4.57  cnf(c_0_92, negated_conjecture, (k2_xboole_0(X1,k2_tarski(X1,X1))=esk7_0|r2_hidden(esk7_0,k2_xboole_0(X1,k2_tarski(X1,X1)))|r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_86])).
% 4.38/4.57  cnf(c_0_93, negated_conjecture, (v3_ordinal1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_67])])).
% 4.38/4.57  cnf(c_0_94, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 4.38/4.57  cnf(c_0_95, negated_conjecture, (r1_tarski(k3_tarski(esk8_0),k2_xboole_0(esk7_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_67])).
% 4.38/4.57  cnf(c_0_96, negated_conjecture, (~v4_ordinal1(esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)),esk7_0)), inference(rw,[status(thm)],[c_0_91, c_0_39])).
% 4.38/4.57  cnf(c_0_97, negated_conjecture, (k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)),esk7_0)|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 4.38/4.57  cnf(c_0_98, negated_conjecture, (r1_tarski(esk8_0,esk7_0)|~v1_ordinal1(esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_71])).
% 4.38/4.57  cnf(c_0_99, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 4.38/4.57  cnf(c_0_100, negated_conjecture, (k2_xboole_0(k3_tarski(esk8_0),k2_xboole_0(esk7_0,X1))=k2_xboole_0(esk7_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 4.38/4.57  cnf(c_0_101, plain, (k2_xboole_0(X1,k3_tarski(X2))=k3_tarski(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_94, c_0_37])).
% 4.38/4.57  cnf(c_0_102, negated_conjecture, (k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))=esk7_0|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)))|~v4_ordinal1(esk7_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 4.38/4.57  cnf(c_0_103, negated_conjecture, (r1_tarski(esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_62]), c_0_25])])).
% 4.38/4.57  cnf(c_0_104, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_99])).
% 4.38/4.57  cnf(c_0_105, negated_conjecture, (k3_tarski(k2_xboole_0(esk8_0,X1))=k3_tarski(X1)|~r2_hidden(esk7_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_84])).
% 4.38/4.57  cnf(c_0_106, negated_conjecture, (k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))=esk7_0|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_60]), c_0_67])])).
% 4.38/4.57  cnf(c_0_107, negated_conjecture, (~r2_hidden(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_103])).
% 4.38/4.57  cnf(c_0_108, plain, (r1_tarski(k3_tarski(k2_xboole_0(X1,X2)),X3)|r2_hidden(esk5_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk5_2(k2_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_104, c_0_77])).
% 4.38/4.57  cnf(c_0_109, negated_conjecture, (~r2_hidden(X1,k2_xboole_0(esk8_0,X2))|~r2_hidden(k3_tarski(X2),X1)|~r2_hidden(esk7_0,X2)), inference(spm,[status(thm)],[c_0_44, c_0_105])).
% 4.38/4.57  cnf(c_0_110, negated_conjecture, (k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))=esk7_0|r2_hidden(esk7_0,k2_tarski(esk8_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_106]), c_0_107])).
% 4.38/4.57  cnf(c_0_111, plain, (r1_tarski(k3_tarski(k2_xboole_0(X1,X2)),k3_tarski(X2))|r2_hidden(esk5_2(k2_xboole_0(X1,X2),k3_tarski(X2)),X1)), inference(spm,[status(thm)],[c_0_74, c_0_108])).
% 4.38/4.57  cnf(c_0_112, negated_conjecture, (k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))=esk7_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_106]), c_0_85]), c_0_71])]), c_0_110])).
% 4.38/4.57  cnf(c_0_113, negated_conjecture, (r1_tarski(esk7_0,esk8_0)|r2_hidden(esk5_2(esk7_0,esk8_0),esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_67]), c_0_85]), c_0_85])).
% 4.38/4.57  cnf(c_0_114, negated_conjecture, (r1_tarski(esk5_2(esk7_0,esk8_0),esk8_0)|r1_tarski(esk7_0,esk8_0)|~v1_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_113])).
% 4.38/4.57  cnf(c_0_115, negated_conjecture, (r1_tarski(esk5_2(esk7_0,esk8_0),esk8_0)|r1_tarski(esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_62]), c_0_93])])).
% 4.38/4.57  cnf(c_0_116, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_115]), c_0_67])])).
% 4.38/4.57  cnf(c_0_117, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_116]), c_0_71])]), ['proof']).
% 4.38/4.57  # SZS output end CNFRefutation
% 4.38/4.57  # Proof object total steps             : 118
% 4.38/4.57  # Proof object clause steps            : 81
% 4.38/4.57  # Proof object formula steps           : 37
% 4.38/4.57  # Proof object conjectures             : 42
% 4.38/4.57  # Proof object clause conjectures      : 39
% 4.38/4.57  # Proof object formula conjectures     : 3
% 4.38/4.57  # Proof object initial clauses used    : 27
% 4.38/4.57  # Proof object initial formulas used   : 18
% 4.38/4.57  # Proof object generating inferences   : 41
% 4.38/4.57  # Proof object simplifying inferences  : 42
% 4.38/4.57  # Training examples: 0 positive, 0 negative
% 4.38/4.57  # Parsed axioms                        : 18
% 4.38/4.57  # Removed by relevancy pruning/SinE    : 0
% 4.38/4.57  # Initial clauses                      : 37
% 4.38/4.57  # Removed in clause preprocessing      : 2
% 4.38/4.57  # Initial clauses in saturation        : 35
% 4.38/4.57  # Processed clauses                    : 38194
% 4.38/4.57  # ...of these trivial                  : 85
% 4.38/4.57  # ...subsumed                          : 33976
% 4.38/4.57  # ...remaining for further processing  : 4133
% 4.38/4.57  # Other redundant clauses eliminated   : 6
% 4.38/4.57  # Clauses deleted for lack of memory   : 0
% 4.38/4.57  # Backward-subsumed                    : 129
% 4.38/4.57  # Backward-rewritten                   : 294
% 4.38/4.57  # Generated clauses                    : 481675
% 4.38/4.57  # ...of the previous two non-trivial   : 470672
% 4.38/4.57  # Contextual simplify-reflections      : 27
% 4.38/4.57  # Paramodulations                      : 481176
% 4.38/4.57  # Factorizations                       : 488
% 4.38/4.57  # Equation resolutions                 : 6
% 4.38/4.57  # Propositional unsat checks           : 0
% 4.38/4.57  #    Propositional check models        : 0
% 4.38/4.57  #    Propositional check unsatisfiable : 0
% 4.38/4.57  #    Propositional clauses             : 0
% 4.38/4.57  #    Propositional clauses after purity: 0
% 4.38/4.57  #    Propositional unsat core size     : 0
% 4.38/4.57  #    Propositional preprocessing time  : 0.000
% 4.38/4.57  #    Propositional encoding time       : 0.000
% 4.38/4.57  #    Propositional solver time         : 0.000
% 4.38/4.57  #    Success case prop preproc time    : 0.000
% 4.38/4.57  #    Success case prop encoding time   : 0.000
% 4.38/4.57  #    Success case prop solver time     : 0.000
% 4.38/4.57  # Current number of processed clauses  : 3664
% 4.38/4.57  #    Positive orientable unit clauses  : 119
% 4.38/4.57  #    Positive unorientable unit clauses: 0
% 4.38/4.57  #    Negative unit clauses             : 507
% 4.38/4.57  #    Non-unit-clauses                  : 3038
% 4.38/4.57  # Current number of unprocessed clauses: 430423
% 4.38/4.57  # ...number of literals in the above   : 1438129
% 4.38/4.57  # Current number of archived formulas  : 0
% 4.38/4.57  # Current number of archived clauses   : 465
% 4.38/4.57  # Clause-clause subsumption calls (NU) : 1923623
% 4.38/4.57  # Rec. Clause-clause subsumption calls : 964406
% 4.38/4.57  # Non-unit clause-clause subsumptions  : 13156
% 4.38/4.57  # Unit Clause-clause subsumption calls : 80949
% 4.38/4.57  # Rewrite failures with RHS unbound    : 0
% 4.38/4.57  # BW rewrite match attempts            : 802
% 4.38/4.57  # BW rewrite match successes           : 60
% 4.38/4.57  # Condensation attempts                : 0
% 4.38/4.57  # Condensation successes               : 0
% 4.38/4.57  # Termbank termtop insertions          : 8936323
% 4.38/4.59  
% 4.38/4.59  # -------------------------------------------------
% 4.38/4.59  # User time                : 4.062 s
% 4.38/4.59  # System time              : 0.176 s
% 4.38/4.59  # Total time               : 4.238 s
% 4.38/4.59  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
