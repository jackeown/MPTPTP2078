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

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  164 (8290 expanded)
%              Number of clauses        :  113 (3916 expanded)
%              Number of leaves         :   25 (2090 expanded)
%              Depth                    :   25
%              Number of atoms          :  391 (22271 expanded)
%              Number of equality atoms :   93 (5173 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t41_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t35_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

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

fof(c_0_25,plain,(
    ! [X61,X62] :
      ( ~ r2_hidden(X61,X62)
      | ~ r1_tarski(X62,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_26,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_27,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X40,X41] :
      ( ( r2_hidden(esk5_2(X40,X41),X40)
        | r1_tarski(k3_tarski(X40),X41) )
      & ( ~ r1_tarski(esk5_2(X40,X41),X41)
        | r1_tarski(k3_tarski(X40),X41) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_34,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_35,plain,(
    ! [X43,X44] : k3_tarski(k2_xboole_0(X43,X44)) = k2_xboole_0(k3_tarski(X43),k3_tarski(X44)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_tarski(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( r2_hidden(X28,esk2_3(X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k3_tarski(X26) )
      & ( r2_hidden(esk2_3(X26,X27,X28),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k3_tarski(X26) )
      & ( ~ r2_hidden(X30,X31)
        | ~ r2_hidden(X31,X26)
        | r2_hidden(X30,X27)
        | X27 != k3_tarski(X26) )
      & ( ~ r2_hidden(esk3_2(X32,X33),X33)
        | ~ r2_hidden(esk3_2(X32,X33),X35)
        | ~ r2_hidden(X35,X32)
        | X33 = k3_tarski(X32) )
      & ( r2_hidden(esk3_2(X32,X33),esk4_2(X32,X33))
        | r2_hidden(esk3_2(X32,X33),X33)
        | X33 = k3_tarski(X32) )
      & ( r2_hidden(esk4_2(X32,X33),X32)
        | r2_hidden(esk3_2(X32,X33),X33)
        | X33 = k3_tarski(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_41,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k2_xboole_0(X20,X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k1_xboole_0,k3_tarski(X1)) = k3_tarski(k2_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_50,plain,(
    ! [X39] : k3_tarski(k1_tarski(X39)) = X39 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_51,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_52,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_53,plain,(
    ! [X56,X57] :
      ( ~ v3_ordinal1(X56)
      | ~ v3_ordinal1(X57)
      | r2_hidden(X56,X57)
      | X56 = X57
      | r2_hidden(X57,X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_54,negated_conjecture,(
    ! [X65] :
      ( v3_ordinal1(esk8_0)
      & ( v3_ordinal1(esk9_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( r2_hidden(esk9_0,esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( v4_ordinal1(esk8_0)
        | ~ v3_ordinal1(X65)
        | ~ r2_hidden(X65,esk8_0)
        | r2_hidden(k1_ordinal1(X65),esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])])])).

fof(c_0_55,plain,(
    ! [X54,X55] :
      ( ~ v3_ordinal1(X55)
      | ~ r2_hidden(X54,X55)
      | v3_ordinal1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_56,plain,(
    ! [X59] :
      ( ( r2_hidden(esk7_1(X59),X59)
        | v3_ordinal1(k3_tarski(X59)) )
      & ( ~ v3_ordinal1(esk7_1(X59))
        | v3_ordinal1(k3_tarski(X59)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,X2),X3)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_60,plain,
    ( k3_tarski(k2_xboole_0(k1_xboole_0,X1)) = k3_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29])])).

cnf(c_0_61,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_64,plain,(
    ! [X46] : k1_ordinal1(X46) = k2_xboole_0(X46,k1_tarski(X46)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(esk2_3(X1,k3_tarski(X1),k2_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(k2_xboole_0(X2,X3),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_71,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( k2_xboole_0(k1_xboole_0,k3_tarski(X1)) = k3_tarski(X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_60])).

cnf(c_0_73,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

fof(c_0_74,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | r1_tarski(X37,k3_tarski(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_75,plain,(
    ! [X52] : r2_hidden(X52,k1_ordinal1(X52)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_76,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(X1,esk8_0)
    | r2_hidden(esk8_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,X2),k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_62])).

cnf(c_0_84,negated_conjecture,
    ( k3_tarski(X1) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_87,plain,(
    ! [X58] :
      ( ~ v3_ordinal1(X58)
      | v3_ordinal1(k1_ordinal1(X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_88,plain,(
    ! [X51] :
      ( ( ~ v4_ordinal1(X51)
        | X51 = k3_tarski(X51) )
      & ( X51 != k3_tarski(X51)
        | v4_ordinal1(X51) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_89,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k1_ordinal1(X1),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_90,plain,
    ( ~ r2_hidden(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_81])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_63])).

cnf(c_0_92,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(k3_tarski(esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_66]),c_0_85])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_94,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( v3_ordinal1(esk9_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_96,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_83]),c_0_63])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(k2_xboole_0(k3_tarski(X1),k1_enumset1(k3_tarski(X1),k3_tarski(X1),k3_tarski(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | v3_ordinal1(k3_tarski(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_92]),c_0_66])])).

cnf(c_0_100,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_93])).

fof(c_0_102,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_103,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_83]),c_0_63])).

cnf(c_0_104,negated_conjecture,
    ( v3_ordinal1(esk9_0)
    | k3_tarski(esk8_0) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_92]),c_0_98]),c_0_99]),c_0_100])).

cnf(c_0_106,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_46])).

cnf(c_0_107,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_109,negated_conjecture,
    ( k2_xboole_0(X1,k1_enumset1(X1,X1,X1)) = esk8_0
    | r2_hidden(esk8_0,k2_xboole_0(X1,k1_enumset1(X1,X1,X1)))
    | r2_hidden(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)),esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( v3_ordinal1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105])])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_112,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_106,c_0_46])).

cnf(c_0_113,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_48])).

cnf(c_0_114,negated_conjecture,
    ( ~ v4_ordinal1(esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_83]),c_0_63])).

cnf(c_0_115,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) = esk8_0
    | r2_hidden(k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk8_0)
    | r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | k3_tarski(esk8_0) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_111,c_0_96])).

cnf(c_0_117,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_118,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k3_tarski(X2)
    | ~ r1_tarski(k3_tarski(X1),k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_42])).

cnf(c_0_119,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k2_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_120,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_121,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)))
    | ~ v4_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_105])])).

cnf(c_0_123,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_117])).

cnf(c_0_124,plain,
    ( k3_tarski(k2_xboole_0(k1_enumset1(X1,X1,X1),X2)) = k2_xboole_0(X1,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_73])).

cnf(c_0_125,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k3_tarski(X2)
    | ~ r2_hidden(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_118,c_0_81])).

cnf(c_0_126,plain,
    ( ~ r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),k1_enumset1(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_119,c_0_91])).

cnf(c_0_127,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_120])).

cnf(c_0_128,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_96]),c_0_105])])).

cnf(c_0_129,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_122])).

fof(c_0_130,plain,(
    ! [X53] : X53 != k1_ordinal1(X53) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

cnf(c_0_131,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_123])).

cnf(c_0_132,plain,
    ( k2_xboole_0(X1,k3_tarski(X2)) = k3_tarski(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_73])).

cnf(c_0_133,plain,
    ( ~ r1_tarski(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_80])).

cnf(c_0_134,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])).

cnf(c_0_135,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

fof(c_0_136,plain,(
    ! [X47,X48,X49] :
      ( ( ~ v1_ordinal1(X47)
        | ~ r2_hidden(X48,X47)
        | r1_tarski(X48,X47) )
      & ( r2_hidden(esk6_1(X49),X49)
        | v1_ordinal1(X49) )
      & ( ~ r1_tarski(esk6_1(X49),X49)
        | v1_ordinal1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_137,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(k3_tarski(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_138,plain,
    ( k3_tarski(k2_xboole_0(X1,k1_enumset1(X2,X2,X2))) = k2_xboole_0(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_73])).

cnf(c_0_139,plain,
    ( ~ r2_hidden(X1,k1_enumset1(X2,X2,X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_73])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0))
    | ~ r1_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_141,plain,
    ( X1 != k2_xboole_0(X1,k1_enumset1(X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_83]),c_0_63])).

cnf(c_0_142,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

fof(c_0_143,plain,(
    ! [X45] :
      ( ( v1_ordinal1(X45)
        | ~ v3_ordinal1(X45) )
      & ( v2_ordinal1(X45)
        | ~ v3_ordinal1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_144,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_137,c_0_78])).

cnf(c_0_145,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_73])).

cnf(c_0_146,negated_conjecture,
    ( k2_xboole_0(esk9_0,k3_tarski(esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_134]),c_0_105]),c_0_107])).

cnf(c_0_147,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_122])])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0))
    | esk9_0 != esk8_0 ),
    inference(spm,[status(thm)],[c_0_141,c_0_134])).

cnf(c_0_149,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ v1_ordinal1(k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_142,c_0_46])).

cnf(c_0_150,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_151,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(X1,esk9_0)
    | r2_hidden(esk9_0,X1)
    | k3_tarski(esk8_0) != esk8_0
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_104])).

cnf(c_0_152,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_68]),c_0_69])).

cnf(c_0_153,negated_conjecture,
    ( k2_xboole_0(esk9_0,k3_tarski(esk9_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_147])).

cnf(c_0_154,negated_conjecture,
    ( esk9_0 != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_148]),c_0_122])])).

cnf(c_0_155,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ v3_ordinal1(k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_156,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(esk9_0,X1)
    | r2_hidden(X1,esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_105])])).

cnf(c_0_157,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_122]),c_0_66])])).

cnf(c_0_158,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_153]),c_0_154])).

cnf(c_0_159,plain,
    ( r1_tarski(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_155,c_0_80])).

cnf(c_0_160,negated_conjecture,
    ( k3_tarski(esk9_0) = esk9_0
    | r2_hidden(k3_tarski(esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_85])).

cnf(c_0_161,negated_conjecture,
    ( ~ r2_hidden(k3_tarski(esk9_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_159]),c_0_110])])).

cnf(c_0_162,negated_conjecture,
    ( k3_tarski(esk9_0) = esk9_0 ),
    inference(sr,[status(thm)],[c_0_160,c_0_161])).

cnf(c_0_163,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158,c_0_162]),c_0_93])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:01:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.83/1.03  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.83/1.03  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.83/1.03  #
% 0.83/1.03  # Preprocessing time       : 0.028 s
% 0.83/1.03  # Presaturation interreduction done
% 0.83/1.03  
% 0.83/1.03  # Proof found!
% 0.83/1.03  # SZS status Theorem
% 0.83/1.03  # SZS output start CNFRefutation
% 0.83/1.03  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.83/1.03  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.83/1.03  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.83/1.03  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.83/1.03  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.83/1.03  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 0.83/1.03  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.83/1.03  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.83/1.03  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.83/1.03  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.83/1.03  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.83/1.03  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.83/1.03  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.83/1.03  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.83/1.03  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.83/1.03  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 0.83/1.03  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.83/1.03  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.83/1.03  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.83/1.03  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.83/1.03  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_ordinal1)).
% 0.83/1.03  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.83/1.03  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.83/1.03  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.83/1.03  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.83/1.03  fof(c_0_25, plain, ![X61, X62]:(~r2_hidden(X61,X62)|~r1_tarski(X62,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.83/1.03  fof(c_0_26, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.83/1.03  fof(c_0_27, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.83/1.03  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.83/1.03  cnf(c_0_29, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.83/1.03  fof(c_0_30, plain, ![X40, X41]:((r2_hidden(esk5_2(X40,X41),X40)|r1_tarski(k3_tarski(X40),X41))&(~r1_tarski(esk5_2(X40,X41),X41)|r1_tarski(k3_tarski(X40),X41))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.83/1.03  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.83/1.03  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.83/1.03  cnf(c_0_33, plain, (r2_hidden(esk5_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.83/1.03  fof(c_0_34, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(r2_hidden(X12,X9)|r2_hidden(X12,X10))|X11!=k2_xboole_0(X9,X10))&((~r2_hidden(X13,X9)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))&(~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))))&(((~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15)))&(r2_hidden(esk1_3(X14,X15,X16),X16)|(r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k2_xboole_0(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.83/1.03  fof(c_0_35, plain, ![X43, X44]:k3_tarski(k2_xboole_0(X43,X44))=k2_xboole_0(k3_tarski(X43),k3_tarski(X44)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 0.83/1.03  cnf(c_0_36, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.83/1.03  cnf(c_0_37, plain, (r1_tarski(k3_tarski(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.83/1.03  fof(c_0_38, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.83/1.03  cnf(c_0_39, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.83/1.03  fof(c_0_40, plain, ![X26, X27, X28, X30, X31, X32, X33, X35]:((((r2_hidden(X28,esk2_3(X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k3_tarski(X26))&(r2_hidden(esk2_3(X26,X27,X28),X26)|~r2_hidden(X28,X27)|X27!=k3_tarski(X26)))&(~r2_hidden(X30,X31)|~r2_hidden(X31,X26)|r2_hidden(X30,X27)|X27!=k3_tarski(X26)))&((~r2_hidden(esk3_2(X32,X33),X33)|(~r2_hidden(esk3_2(X32,X33),X35)|~r2_hidden(X35,X32))|X33=k3_tarski(X32))&((r2_hidden(esk3_2(X32,X33),esk4_2(X32,X33))|r2_hidden(esk3_2(X32,X33),X33)|X33=k3_tarski(X32))&(r2_hidden(esk4_2(X32,X33),X32)|r2_hidden(esk3_2(X32,X33),X33)|X33=k3_tarski(X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.83/1.03  fof(c_0_41, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k2_xboole_0(X20,X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.83/1.03  cnf(c_0_42, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.83/1.03  cnf(c_0_43, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.83/1.03  fof(c_0_44, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 0.83/1.03  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.83/1.03  cnf(c_0_46, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_39])).
% 0.83/1.03  cnf(c_0_47, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.83/1.03  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.83/1.03  cnf(c_0_49, plain, (k2_xboole_0(k1_xboole_0,k3_tarski(X1))=k3_tarski(k2_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.83/1.03  fof(c_0_50, plain, ![X39]:k3_tarski(k1_tarski(X39))=X39, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.83/1.03  fof(c_0_51, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.83/1.03  fof(c_0_52, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.83/1.03  fof(c_0_53, plain, ![X56, X57]:(~v3_ordinal1(X56)|(~v3_ordinal1(X57)|(r2_hidden(X56,X57)|X56=X57|r2_hidden(X57,X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.83/1.03  fof(c_0_54, negated_conjecture, ![X65]:(v3_ordinal1(esk8_0)&(((v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0))&((r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0))&(~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0))))&(v4_ordinal1(esk8_0)|(~v3_ordinal1(X65)|(~r2_hidden(X65,esk8_0)|r2_hidden(k1_ordinal1(X65),esk8_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])])])).
% 0.83/1.03  fof(c_0_55, plain, ![X54, X55]:(~v3_ordinal1(X55)|(~r2_hidden(X54,X55)|v3_ordinal1(X54))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.83/1.03  fof(c_0_56, plain, ![X59]:((r2_hidden(esk7_1(X59),X59)|v3_ordinal1(k3_tarski(X59)))&(~v3_ordinal1(esk7_1(X59))|v3_ordinal1(k3_tarski(X59)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 0.83/1.03  cnf(c_0_57, plain, (~r2_hidden(k2_xboole_0(X1,X2),X3)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.83/1.03  cnf(c_0_58, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_47])).
% 0.83/1.03  cnf(c_0_59, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.83/1.03  cnf(c_0_60, plain, (k3_tarski(k2_xboole_0(k1_xboole_0,X1))=k3_tarski(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_29])])).
% 0.83/1.03  cnf(c_0_61, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.83/1.03  cnf(c_0_62, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.83/1.03  cnf(c_0_63, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.83/1.03  fof(c_0_64, plain, ![X46]:k1_ordinal1(X46)=k2_xboole_0(X46,k1_tarski(X46)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.83/1.03  cnf(c_0_65, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.83/1.03  cnf(c_0_66, negated_conjecture, (v3_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.83/1.03  cnf(c_0_67, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.83/1.03  cnf(c_0_68, plain, (r2_hidden(esk7_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.83/1.03  cnf(c_0_69, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.83/1.03  cnf(c_0_70, plain, (~r2_hidden(esk2_3(X1,k3_tarski(X1),k2_xboole_0(X2,X3)),X3)|~r2_hidden(k2_xboole_0(X2,X3),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.83/1.03  cnf(c_0_71, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_59])).
% 0.83/1.03  cnf(c_0_72, plain, (k2_xboole_0(k1_xboole_0,k3_tarski(X1))=k3_tarski(X1)), inference(rw,[status(thm)],[c_0_49, c_0_60])).
% 0.83/1.03  cnf(c_0_73, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.83/1.03  fof(c_0_74, plain, ![X37, X38]:(~r2_hidden(X37,X38)|r1_tarski(X37,k3_tarski(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.83/1.03  fof(c_0_75, plain, ![X52]:r2_hidden(X52,k1_ordinal1(X52)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.83/1.03  cnf(c_0_76, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.83/1.03  cnf(c_0_77, negated_conjecture, (X1=esk8_0|r2_hidden(X1,esk8_0)|r2_hidden(esk8_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.83/1.03  cnf(c_0_78, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.83/1.03  cnf(c_0_79, plain, (~r2_hidden(k2_xboole_0(X1,X2),k3_tarski(X2))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.83/1.03  cnf(c_0_80, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.83/1.03  cnf(c_0_81, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.83/1.03  cnf(c_0_82, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.83/1.03  cnf(c_0_83, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_76, c_0_62])).
% 0.83/1.03  cnf(c_0_84, negated_conjecture, (k3_tarski(X1)=esk8_0|r2_hidden(esk8_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.83/1.03  cnf(c_0_85, plain, (~r2_hidden(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.83/1.03  cnf(c_0_86, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.83/1.03  fof(c_0_87, plain, ![X58]:(~v3_ordinal1(X58)|v3_ordinal1(k1_ordinal1(X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.83/1.03  fof(c_0_88, plain, ![X51]:((~v4_ordinal1(X51)|X51=k3_tarski(X51))&(X51!=k3_tarski(X51)|v4_ordinal1(X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 0.83/1.03  cnf(c_0_89, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k1_ordinal1(X1),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.83/1.03  cnf(c_0_90, plain, (~r2_hidden(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_81])).
% 0.83/1.03  cnf(c_0_91, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_63])).
% 0.83/1.03  cnf(c_0_92, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(k3_tarski(esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_66]), c_0_85])).
% 0.83/1.03  cnf(c_0_93, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_86])).
% 0.83/1.03  cnf(c_0_94, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.83/1.03  cnf(c_0_95, negated_conjecture, (v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.83/1.03  cnf(c_0_96, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.83/1.03  cnf(c_0_97, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_83]), c_0_63])).
% 0.83/1.03  cnf(c_0_98, plain, (~r2_hidden(k2_xboole_0(k3_tarski(X1),k1_enumset1(k3_tarski(X1),k3_tarski(X1),k3_tarski(X1))),X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.83/1.03  cnf(c_0_99, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|v3_ordinal1(k3_tarski(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_92]), c_0_66])])).
% 0.83/1.03  cnf(c_0_100, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.83/1.03  cnf(c_0_101, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_28, c_0_93])).
% 0.83/1.03  fof(c_0_102, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.83/1.03  cnf(c_0_103, plain, (v3_ordinal1(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_83]), c_0_63])).
% 0.83/1.03  cnf(c_0_104, negated_conjecture, (v3_ordinal1(esk9_0)|k3_tarski(esk8_0)!=esk8_0), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.83/1.03  cnf(c_0_105, negated_conjecture, (k3_tarski(esk8_0)=esk8_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_92]), c_0_98]), c_0_99]), c_0_100])).
% 0.83/1.03  cnf(c_0_106, plain, (~r2_hidden(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_101, c_0_46])).
% 0.83/1.03  cnf(c_0_107, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.83/1.03  cnf(c_0_108, negated_conjecture, (~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.83/1.03  cnf(c_0_109, negated_conjecture, (k2_xboole_0(X1,k1_enumset1(X1,X1,X1))=esk8_0|r2_hidden(esk8_0,k2_xboole_0(X1,k1_enumset1(X1,X1,X1)))|r2_hidden(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)),esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_103])).
% 0.83/1.03  cnf(c_0_110, negated_conjecture, (v3_ordinal1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105])])).
% 0.83/1.03  cnf(c_0_111, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.83/1.03  cnf(c_0_112, plain, (~r2_hidden(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_106, c_0_46])).
% 0.83/1.03  cnf(c_0_113, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_107, c_0_48])).
% 0.83/1.03  cnf(c_0_114, negated_conjecture, (~v4_ordinal1(esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_83]), c_0_63])).
% 0.83/1.03  cnf(c_0_115, negated_conjecture, (k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0))=esk8_0|r2_hidden(k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk8_0)|r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.83/1.03  cnf(c_0_116, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|k3_tarski(esk8_0)!=esk8_0), inference(spm,[status(thm)],[c_0_111, c_0_96])).
% 0.83/1.03  cnf(c_0_117, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.83/1.03  cnf(c_0_118, plain, (k3_tarski(k2_xboole_0(X1,X2))=k3_tarski(X2)|~r1_tarski(k3_tarski(X1),k3_tarski(X2))), inference(spm,[status(thm)],[c_0_48, c_0_42])).
% 0.83/1.03  cnf(c_0_119, plain, (~r1_tarski(X1,X2)|~r2_hidden(k2_xboole_0(X3,X2),X1)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.83/1.03  cnf(c_0_120, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.83/1.03  cnf(c_0_121, negated_conjecture, (k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0))=esk8_0|r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)))|~v4_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.83/1.03  cnf(c_0_122, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_105])])).
% 0.83/1.03  cnf(c_0_123, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_117])).
% 0.83/1.03  cnf(c_0_124, plain, (k3_tarski(k2_xboole_0(k1_enumset1(X1,X1,X1),X2))=k2_xboole_0(X1,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_42, c_0_73])).
% 0.83/1.03  cnf(c_0_125, plain, (k3_tarski(k2_xboole_0(X1,X2))=k3_tarski(X2)|~r2_hidden(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_118, c_0_81])).
% 0.83/1.03  cnf(c_0_126, plain, (~r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),k1_enumset1(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_119, c_0_91])).
% 0.83/1.03  cnf(c_0_127, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_120])).
% 0.83/1.03  cnf(c_0_128, negated_conjecture, (k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0))=esk8_0|r2_hidden(esk8_0,k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_96]), c_0_105])])).
% 0.83/1.03  cnf(c_0_129, negated_conjecture, (~r2_hidden(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_45, c_0_122])).
% 0.83/1.03  fof(c_0_130, plain, ![X53]:X53!=k1_ordinal1(X53), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.83/1.03  cnf(c_0_131, plain, (v3_ordinal1(X1)|~v3_ordinal1(k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_123])).
% 0.83/1.03  cnf(c_0_132, plain, (k2_xboole_0(X1,k3_tarski(X2))=k3_tarski(X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_73])).
% 0.83/1.03  cnf(c_0_133, plain, (~r1_tarski(k2_xboole_0(X1,k1_enumset1(X1,X1,X1)),X1)), inference(spm,[status(thm)],[c_0_126, c_0_80])).
% 0.83/1.03  cnf(c_0_134, negated_conjecture, (k2_xboole_0(esk9_0,k1_enumset1(esk9_0,esk9_0,esk9_0))=esk8_0|r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129])).
% 0.83/1.03  cnf(c_0_135, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_130])).
% 0.83/1.03  fof(c_0_136, plain, ![X47, X48, X49]:((~v1_ordinal1(X47)|(~r2_hidden(X48,X47)|r1_tarski(X48,X47)))&((r2_hidden(esk6_1(X49),X49)|v1_ordinal1(X49))&(~r1_tarski(esk6_1(X49),X49)|v1_ordinal1(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.83/1.03  cnf(c_0_137, plain, (v3_ordinal1(X1)|~v3_ordinal1(k3_tarski(X2))|~r2_hidden(X1,X3)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.83/1.03  cnf(c_0_138, plain, (k3_tarski(k2_xboole_0(X1,k1_enumset1(X2,X2,X2)))=k2_xboole_0(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_73])).
% 0.83/1.03  cnf(c_0_139, plain, (~r2_hidden(X1,k1_enumset1(X2,X2,X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_90, c_0_73])).
% 0.83/1.03  cnf(c_0_140, negated_conjecture, (r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0))|~r1_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 0.83/1.03  cnf(c_0_141, plain, (X1!=k2_xboole_0(X1,k1_enumset1(X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_83]), c_0_63])).
% 0.83/1.03  cnf(c_0_142, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_136])).
% 0.83/1.03  fof(c_0_143, plain, ![X45]:((v1_ordinal1(X45)|~v3_ordinal1(X45))&(v2_ordinal1(X45)|~v3_ordinal1(X45))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.83/1.03  cnf(c_0_144, plain, (v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X3)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_137, c_0_78])).
% 0.83/1.03  cnf(c_0_145, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(spm,[status(thm)],[c_0_81, c_0_73])).
% 0.83/1.03  cnf(c_0_146, negated_conjecture, (k2_xboole_0(esk9_0,k3_tarski(esk9_0))=esk8_0|r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_134]), c_0_105]), c_0_107])).
% 0.83/1.03  cnf(c_0_147, negated_conjecture, (~r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_122])])).
% 0.83/1.03  cnf(c_0_148, negated_conjecture, (r2_hidden(esk8_0,k1_enumset1(esk9_0,esk9_0,esk9_0))|esk9_0!=esk8_0), inference(spm,[status(thm)],[c_0_141, c_0_134])).
% 0.83/1.03  cnf(c_0_149, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~v1_ordinal1(k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_142, c_0_46])).
% 0.83/1.03  cnf(c_0_150, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_143])).
% 0.83/1.03  cnf(c_0_151, negated_conjecture, (X1=esk9_0|r2_hidden(X1,esk9_0)|r2_hidden(esk9_0,X1)|k3_tarski(esk8_0)!=esk8_0|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_104])).
% 0.83/1.03  cnf(c_0_152, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_68]), c_0_69])).
% 0.83/1.03  cnf(c_0_153, negated_conjecture, (k2_xboole_0(esk9_0,k3_tarski(esk9_0))=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_147])).
% 0.83/1.03  cnf(c_0_154, negated_conjecture, (esk9_0!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_148]), c_0_122])])).
% 0.83/1.03  cnf(c_0_155, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~v3_ordinal1(k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 0.83/1.03  cnf(c_0_156, negated_conjecture, (X1=esk9_0|r2_hidden(esk9_0,X1)|r2_hidden(X1,esk9_0)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_105])])).
% 0.83/1.03  cnf(c_0_157, negated_conjecture, (v3_ordinal1(k3_tarski(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_122]), c_0_66])])).
% 0.83/1.03  cnf(c_0_158, negated_conjecture, (~r1_tarski(k3_tarski(esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_153]), c_0_154])).
% 0.83/1.03  cnf(c_0_159, plain, (r1_tarski(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_155, c_0_80])).
% 0.83/1.03  cnf(c_0_160, negated_conjecture, (k3_tarski(esk9_0)=esk9_0|r2_hidden(k3_tarski(esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_157]), c_0_85])).
% 0.83/1.03  cnf(c_0_161, negated_conjecture, (~r2_hidden(k3_tarski(esk9_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_159]), c_0_110])])).
% 0.83/1.03  cnf(c_0_162, negated_conjecture, (k3_tarski(esk9_0)=esk9_0), inference(sr,[status(thm)],[c_0_160, c_0_161])).
% 0.83/1.03  cnf(c_0_163, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_158, c_0_162]), c_0_93])]), ['proof']).
% 0.83/1.03  # SZS output end CNFRefutation
% 0.83/1.03  # Proof object total steps             : 164
% 0.83/1.03  # Proof object clause steps            : 113
% 0.83/1.03  # Proof object formula steps           : 51
% 0.83/1.03  # Proof object conjectures             : 39
% 0.83/1.03  # Proof object clause conjectures      : 36
% 0.83/1.03  # Proof object formula conjectures     : 3
% 0.83/1.03  # Proof object initial clauses used    : 35
% 0.83/1.03  # Proof object initial formulas used   : 25
% 0.83/1.03  # Proof object generating inferences   : 59
% 0.83/1.03  # Proof object simplifying inferences  : 57
% 0.83/1.03  # Training examples: 0 positive, 0 negative
% 0.83/1.03  # Parsed axioms                        : 25
% 0.83/1.03  # Removed by relevancy pruning/SinE    : 0
% 0.83/1.03  # Initial clauses                      : 47
% 0.83/1.03  # Removed in clause preprocessing      : 3
% 0.83/1.03  # Initial clauses in saturation        : 44
% 0.83/1.03  # Processed clauses                    : 7404
% 0.83/1.03  # ...of these trivial                  : 30
% 0.83/1.03  # ...subsumed                          : 6075
% 0.83/1.03  # ...remaining for further processing  : 1299
% 0.83/1.03  # Other redundant clauses eliminated   : 8
% 0.83/1.03  # Clauses deleted for lack of memory   : 0
% 0.83/1.03  # Backward-subsumed                    : 47
% 0.83/1.03  # Backward-rewritten                   : 175
% 0.83/1.03  # Generated clauses                    : 52676
% 0.83/1.03  # ...of the previous two non-trivial   : 51018
% 0.83/1.03  # Contextual simplify-reflections      : 16
% 0.83/1.03  # Paramodulations                      : 52521
% 0.83/1.03  # Factorizations                       : 142
% 0.83/1.03  # Equation resolutions                 : 8
% 0.83/1.03  # Propositional unsat checks           : 0
% 0.83/1.03  #    Propositional check models        : 0
% 0.83/1.03  #    Propositional check unsatisfiable : 0
% 0.83/1.03  #    Propositional clauses             : 0
% 0.83/1.03  #    Propositional clauses after purity: 0
% 0.83/1.03  #    Propositional unsat core size     : 0
% 0.83/1.03  #    Propositional preprocessing time  : 0.000
% 0.83/1.03  #    Propositional encoding time       : 0.000
% 0.83/1.03  #    Propositional solver time         : 0.000
% 0.83/1.03  #    Success case prop preproc time    : 0.000
% 0.83/1.03  #    Success case prop encoding time   : 0.000
% 0.83/1.03  #    Success case prop solver time     : 0.000
% 0.83/1.03  # Current number of processed clauses  : 1021
% 0.83/1.03  #    Positive orientable unit clauses  : 42
% 0.83/1.03  #    Positive unorientable unit clauses: 1
% 0.83/1.03  #    Negative unit clauses             : 144
% 0.83/1.03  #    Non-unit-clauses                  : 834
% 0.83/1.03  # Current number of unprocessed clauses: 43433
% 0.83/1.03  # ...number of literals in the above   : 142439
% 0.83/1.03  # Current number of archived formulas  : 0
% 0.83/1.03  # Current number of archived clauses   : 273
% 0.83/1.03  # Clause-clause subsumption calls (NU) : 219555
% 0.83/1.03  # Rec. Clause-clause subsumption calls : 93271
% 0.83/1.03  # Non-unit clause-clause subsumptions  : 3318
% 0.83/1.03  # Unit Clause-clause subsumption calls : 11065
% 0.83/1.03  # Rewrite failures with RHS unbound    : 0
% 0.83/1.03  # BW rewrite match attempts            : 53
% 0.83/1.03  # BW rewrite match successes           : 24
% 0.83/1.03  # Condensation attempts                : 0
% 0.83/1.03  # Condensation successes               : 0
% 0.83/1.03  # Termbank termtop insertions          : 713110
% 0.83/1.04  
% 0.83/1.04  # -------------------------------------------------
% 0.83/1.04  # User time                : 0.646 s
% 0.83/1.04  # System time              : 0.031 s
% 0.83/1.04  # Total time               : 0.677 s
% 0.83/1.04  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
