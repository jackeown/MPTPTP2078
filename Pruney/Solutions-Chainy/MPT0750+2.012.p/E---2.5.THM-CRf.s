%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:33 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :  160 (96005 expanded)
%              Number of clauses        :  131 (43506 expanded)
%              Number of leaves         :   14 (22454 expanded)
%              Depth                    :   51
%              Number of atoms          :  420 (380054 expanded)
%              Number of equality atoms :   41 (37407 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t35_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_15,plain,(
    ! [X32,X33] :
      ( ~ v3_ordinal1(X32)
      | ~ v3_ordinal1(X33)
      | r2_hidden(X32,X33)
      | X32 = X33
      | r2_hidden(X33,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X46] :
      ( v3_ordinal1(esk7_0)
      & ( v3_ordinal1(esk8_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( v4_ordinal1(esk7_0)
        | ~ v3_ordinal1(X46)
        | ~ r2_hidden(X46,esk7_0)
        | r2_hidden(k1_ordinal1(X46),esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X37] :
      ( ( r2_hidden(esk5_1(X37),X37)
        | v3_ordinal1(k3_tarski(X37)) )
      & ( ~ v3_ordinal1(esk5_1(X37))
        | v3_ordinal1(k3_tarski(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_20,plain,(
    ! [X19] :
      ( ( ~ v4_ordinal1(X19)
        | X19 = k3_tarski(X19) )
      & ( X19 != k3_tarski(X19)
        | v4_ordinal1(X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_21,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(X1,esk7_0)
    | r2_hidden(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X30,X31] :
      ( ~ v3_ordinal1(X31)
      | ~ r2_hidden(X30,X31)
      | v3_ordinal1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_24,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k3_tarski(X1) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(X1))
    | r2_hidden(k3_tarski(X1),esk7_0)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_31,plain,(
    ! [X18] : k1_ordinal1(X18) = k2_xboole_0(X18,k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_32,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k1_ordinal1(X1),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29])).

fof(c_0_37,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(X9,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(esk2_2(X13,X14),X16)
        | ~ r2_hidden(X16,X13)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk2_2(X13,X14),esk3_2(X13,X14))
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_36])).

fof(c_0_40,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_41,plain,(
    ! [X34] :
      ( ~ v3_ordinal1(X34)
      | v3_ordinal1(k1_ordinal1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_39]),c_0_27])).

fof(c_0_45,plain,(
    ! [X26] : r2_hidden(X26,k1_ordinal1(X26)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_46,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | ~ r1_tarski(X43,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_27])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_54,plain,(
    ! [X35,X36] :
      ( ( ~ r2_hidden(X35,k1_ordinal1(X36))
        | r1_ordinal1(X35,X36)
        | ~ v3_ordinal1(X36)
        | ~ v3_ordinal1(X35) )
      & ( ~ r1_ordinal1(X35,X36)
        | r2_hidden(X35,k1_ordinal1(X36))
        | ~ v3_ordinal1(X36)
        | ~ v3_ordinal1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

cnf(c_0_55,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_35])).

fof(c_0_56,plain,(
    ! [X27,X28] :
      ( ( ~ r2_hidden(X27,k1_ordinal1(X28))
        | r2_hidden(X27,X28)
        | X27 = X28 )
      & ( ~ r2_hidden(X27,X28)
        | r2_hidden(X27,k1_ordinal1(X28)) )
      & ( X27 != X28
        | r2_hidden(X27,k1_ordinal1(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_35])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_18])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

fof(c_0_66,plain,(
    ! [X20,X21] :
      ( ( ~ r1_ordinal1(X20,X21)
        | r1_tarski(X20,X21)
        | ~ v3_ordinal1(X20)
        | ~ v3_ordinal1(X21) )
      & ( ~ r1_tarski(X20,X21)
        | r1_ordinal1(X20,X21)
        | ~ v3_ordinal1(X20)
        | ~ v3_ordinal1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_67,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_35])).

cnf(c_0_68,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_18]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_18])).

cnf(c_0_76,negated_conjecture,
    ( v3_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,esk1_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk7_0,esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_62])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_79]),c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk8_0,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r1_ordinal1(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | ~ r2_hidden(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_81]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk8_0,k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( X1 = k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))
    | r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | ~ r1_ordinal1(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( r1_ordinal1(esk8_0,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_62]),c_0_90])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k2_xboole_0(k2_xboole_0(X1,k1_tarski(X1)),k1_tarski(k2_xboole_0(X1,k1_tarski(X1))))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_59])).

cnf(c_0_98,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))) = k2_xboole_0(esk8_0,k1_tarski(esk8_0))
    | r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk8_0,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_87]),c_0_94])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( r1_ordinal1(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_86])).

cnf(c_0_102,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_103,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_82])).

cnf(c_0_104,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_96,c_0_35])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_87]),c_0_101])])).

cnf(c_0_108,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))) = esk8_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk1_3(esk7_0,esk7_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_92])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_109]),c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_82])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,esk1_3(esk7_0,esk7_0,X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_87]),c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = k2_xboole_0(esk7_0,k1_tarski(esk7_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_114])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_82])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_87])).

cnf(c_0_121,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_59])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0)
    | ~ r1_ordinal1(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_18])).

cnf(c_0_125,negated_conjecture,
    ( r1_ordinal1(esk7_0,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_59]),c_0_116])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk1_3(esk7_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_59])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r1_tarski(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_128]),c_0_82])])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( v3_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( v3_ordinal1(esk1_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_108])).

cnf(c_0_136,negated_conjecture,
    ( r1_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_131])).

cnf(c_0_137,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_138,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0)
    | ~ r1_ordinal1(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( r1_ordinal1(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_108])).

cnf(c_0_140,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_137,c_0_35])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk5_1(esk7_0),esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_28])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_141]),c_0_119])).

cnf(c_0_144,negated_conjecture,
    ( r2_hidden(esk5_1(esk7_0),esk7_0)
    | r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143])])).

cnf(c_0_145,negated_conjecture,
    ( v3_ordinal1(esk5_1(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_144])).

cnf(c_0_146,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_145]),c_0_29])).

cnf(c_0_147,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(k3_tarski(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_146])).

cnf(c_0_148,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_143])])).

cnf(c_0_149,negated_conjecture,
    ( r2_hidden(k3_tarski(esk7_0),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_147]),c_0_148])).

cnf(c_0_150,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)
    | r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_149]),c_0_148])).

cnf(c_0_151,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_150])).

cnf(c_0_152,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_59]),c_0_60])).

cnf(c_0_153,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_152])).

cnf(c_0_154,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_153])).

cnf(c_0_155,negated_conjecture,
    ( v3_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_153])).

cnf(c_0_156,negated_conjecture,
    ( r1_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_154])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_155]),c_0_156])])).

cnf(c_0_158,negated_conjecture,
    ( r2_hidden(esk7_0,esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_152])).

cnf(c_0_159,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_157]),c_0_158])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 8.55/8.75  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 8.55/8.75  # and selection function SelectCQIArEqFirst.
% 8.55/8.75  #
% 8.55/8.75  # Preprocessing time       : 0.028 s
% 8.55/8.75  # Presaturation interreduction done
% 8.55/8.75  
% 8.55/8.75  # Proof found!
% 8.55/8.75  # SZS status Theorem
% 8.55/8.75  # SZS output start CNFRefutation
% 8.55/8.75  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 8.55/8.75  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 8.55/8.75  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_ordinal1)).
% 8.55/8.75  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 8.55/8.75  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 8.55/8.75  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 8.55/8.75  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 8.55/8.75  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.55/8.75  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 8.55/8.75  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 8.55/8.75  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.55/8.75  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 8.55/8.75  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 8.55/8.75  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.55/8.75  fof(c_0_14, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 8.55/8.75  fof(c_0_15, plain, ![X32, X33]:(~v3_ordinal1(X32)|(~v3_ordinal1(X33)|(r2_hidden(X32,X33)|X32=X33|r2_hidden(X33,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 8.55/8.75  fof(c_0_16, negated_conjecture, ![X46]:(v3_ordinal1(esk7_0)&(((v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0))&((r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0))&(~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0))))&(v4_ordinal1(esk7_0)|(~v3_ordinal1(X46)|(~r2_hidden(X46,esk7_0)|r2_hidden(k1_ordinal1(X46),esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).
% 8.55/8.75  cnf(c_0_17, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.55/8.75  cnf(c_0_18, negated_conjecture, (v3_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.55/8.75  fof(c_0_19, plain, ![X37]:((r2_hidden(esk5_1(X37),X37)|v3_ordinal1(k3_tarski(X37)))&(~v3_ordinal1(esk5_1(X37))|v3_ordinal1(k3_tarski(X37)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 8.55/8.75  fof(c_0_20, plain, ![X19]:((~v4_ordinal1(X19)|X19=k3_tarski(X19))&(X19!=k3_tarski(X19)|v4_ordinal1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 8.55/8.75  cnf(c_0_21, negated_conjecture, (X1=esk7_0|r2_hidden(X1,esk7_0)|r2_hidden(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 8.55/8.75  cnf(c_0_22, plain, (r2_hidden(esk5_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 8.55/8.75  fof(c_0_23, plain, ![X30, X31]:(~v3_ordinal1(X31)|(~r2_hidden(X30,X31)|v3_ordinal1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 8.55/8.75  cnf(c_0_24, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 8.55/8.75  cnf(c_0_25, negated_conjecture, (k3_tarski(X1)=esk7_0|r2_hidden(esk7_0,k3_tarski(X1))|r2_hidden(k3_tarski(X1),esk7_0)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 8.55/8.75  cnf(c_0_26, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.55/8.75  cnf(c_0_27, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.55/8.75  cnf(c_0_28, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25])])).
% 8.55/8.75  cnf(c_0_29, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_18])).
% 8.55/8.75  cnf(c_0_30, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 8.55/8.75  fof(c_0_31, plain, ![X18]:k1_ordinal1(X18)=k2_xboole_0(X18,k1_tarski(X18)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 8.55/8.75  cnf(c_0_32, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 8.55/8.75  cnf(c_0_33, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 8.55/8.75  cnf(c_0_34, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k1_ordinal1(X1),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.55/8.75  cnf(c_0_35, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 8.55/8.75  cnf(c_0_36, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29])).
% 8.55/8.75  fof(c_0_37, plain, ![X7, X8, X9, X11, X12, X13, X14, X16]:((((r2_hidden(X9,esk1_3(X7,X8,X9))|~r2_hidden(X9,X8)|X8!=k3_tarski(X7))&(r2_hidden(esk1_3(X7,X8,X9),X7)|~r2_hidden(X9,X8)|X8!=k3_tarski(X7)))&(~r2_hidden(X11,X12)|~r2_hidden(X12,X7)|r2_hidden(X11,X8)|X8!=k3_tarski(X7)))&((~r2_hidden(esk2_2(X13,X14),X14)|(~r2_hidden(esk2_2(X13,X14),X16)|~r2_hidden(X16,X13))|X14=k3_tarski(X13))&((r2_hidden(esk2_2(X13,X14),esk3_2(X13,X14))|r2_hidden(esk2_2(X13,X14),X14)|X14=k3_tarski(X13))&(r2_hidden(esk3_2(X13,X14),X13)|r2_hidden(esk2_2(X13,X14),X14)|X14=k3_tarski(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 8.55/8.75  cnf(c_0_38, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 8.55/8.75  cnf(c_0_39, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_36])).
% 8.55/8.75  fof(c_0_40, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 8.55/8.75  fof(c_0_41, plain, ![X34]:(~v3_ordinal1(X34)|v3_ordinal1(k1_ordinal1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 8.55/8.75  cnf(c_0_42, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.55/8.75  cnf(c_0_43, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[c_0_38, c_0_29])).
% 8.55/8.75  cnf(c_0_44, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_39]), c_0_27])).
% 8.55/8.75  fof(c_0_45, plain, ![X26]:r2_hidden(X26,k1_ordinal1(X26)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 8.55/8.75  fof(c_0_46, plain, ![X42, X43]:(~r2_hidden(X42,X43)|~r1_tarski(X43,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 8.55/8.75  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 8.55/8.75  cnf(c_0_48, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 8.55/8.75  cnf(c_0_49, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_42])).
% 8.55/8.75  cnf(c_0_50, negated_conjecture, (r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_27])).
% 8.55/8.75  cnf(c_0_51, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 8.55/8.75  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 8.55/8.75  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 8.55/8.75  fof(c_0_54, plain, ![X35, X36]:((~r2_hidden(X35,k1_ordinal1(X36))|r1_ordinal1(X35,X36)|~v3_ordinal1(X36)|~v3_ordinal1(X35))&(~r1_ordinal1(X35,X36)|r2_hidden(X35,k1_ordinal1(X36))|~v3_ordinal1(X36)|~v3_ordinal1(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 8.55/8.75  cnf(c_0_55, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_48, c_0_35])).
% 8.55/8.75  fof(c_0_56, plain, ![X27, X28]:((~r2_hidden(X27,k1_ordinal1(X28))|(r2_hidden(X27,X28)|X27=X28))&((~r2_hidden(X27,X28)|r2_hidden(X27,k1_ordinal1(X28)))&(X27!=X28|r2_hidden(X27,k1_ordinal1(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 8.55/8.75  cnf(c_0_57, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.55/8.75  cnf(c_0_58, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 8.55/8.75  cnf(c_0_59, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_51, c_0_35])).
% 8.55/8.75  cnf(c_0_60, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 8.55/8.75  cnf(c_0_61, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 8.55/8.75  cnf(c_0_62, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_55, c_0_18])).
% 8.55/8.75  cnf(c_0_63, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 8.55/8.75  cnf(c_0_64, plain, (r2_hidden(esk1_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_57])).
% 8.55/8.75  cnf(c_0_65, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 8.55/8.75  fof(c_0_66, plain, ![X20, X21]:((~r1_ordinal1(X20,X21)|r1_tarski(X20,X21)|(~v3_ordinal1(X20)|~v3_ordinal1(X21)))&(~r1_tarski(X20,X21)|r1_ordinal1(X20,X21)|(~v3_ordinal1(X20)|~v3_ordinal1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 8.55/8.75  cnf(c_0_67, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_61, c_0_35])).
% 8.55/8.75  cnf(c_0_68, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_26, c_0_62])).
% 8.55/8.75  cnf(c_0_69, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_63, c_0_35])).
% 8.55/8.75  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 8.55/8.75  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 8.55/8.75  cnf(c_0_72, negated_conjecture, (r1_ordinal1(X1,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_18]), c_0_68])).
% 8.55/8.75  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 8.55/8.75  cnf(c_0_74, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.55/8.75  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_18])).
% 8.55/8.75  cnf(c_0_76, negated_conjecture, (v3_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_70])).
% 8.55/8.75  cnf(c_0_77, negated_conjecture, (r1_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 8.55/8.75  cnf(c_0_78, plain, (r2_hidden(X1,esk1_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_74])).
% 8.55/8.75  cnf(c_0_79, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|r1_tarski(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 8.55/8.75  cnf(c_0_80, negated_conjecture, (r2_hidden(esk7_0,esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_78, c_0_65])).
% 8.55/8.75  cnf(c_0_81, negated_conjecture, (v3_ordinal1(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_55, c_0_62])).
% 8.55/8.75  cnf(c_0_82, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_79]), c_0_80])).
% 8.55/8.75  cnf(c_0_83, negated_conjecture, (v3_ordinal1(k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))))), inference(spm,[status(thm)],[c_0_55, c_0_81])).
% 8.55/8.75  cnf(c_0_84, negated_conjecture, (r2_hidden(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_69, c_0_82])).
% 8.55/8.75  cnf(c_0_85, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))))), inference(spm,[status(thm)],[c_0_26, c_0_83])).
% 8.55/8.75  cnf(c_0_86, negated_conjecture, (r2_hidden(esk8_0,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_69, c_0_84])).
% 8.55/8.75  cnf(c_0_87, negated_conjecture, (v3_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_82])).
% 8.55/8.75  cnf(c_0_88, negated_conjecture, (r1_ordinal1(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|~r2_hidden(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_81]), c_0_85])).
% 8.55/8.75  cnf(c_0_89, negated_conjecture, (r2_hidden(esk8_0,k2_xboole_0(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k1_tarski(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))))), inference(spm,[status(thm)],[c_0_69, c_0_86])).
% 8.55/8.75  cnf(c_0_90, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_26, c_0_81])).
% 8.55/8.75  cnf(c_0_91, negated_conjecture, (X1=k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))|r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_81])).
% 8.55/8.75  cnf(c_0_92, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_55, c_0_87])).
% 8.55/8.75  cnf(c_0_93, negated_conjecture, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|~r1_ordinal1(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_81])).
% 8.55/8.75  cnf(c_0_94, negated_conjecture, (r1_ordinal1(esk8_0,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 8.55/8.75  cnf(c_0_95, negated_conjecture, (r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r2_hidden(X1,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_62]), c_0_90])).
% 8.55/8.75  cnf(c_0_96, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 8.55/8.75  cnf(c_0_97, plain, (r2_hidden(X1,k2_xboole_0(k2_xboole_0(X1,k1_tarski(X1)),k1_tarski(k2_xboole_0(X1,k1_tarski(X1)))))), inference(spm,[status(thm)],[c_0_69, c_0_59])).
% 8.55/8.75  cnf(c_0_98, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))=k2_xboole_0(esk8_0,k1_tarski(esk8_0))|r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 8.55/8.75  cnf(c_0_99, negated_conjecture, (r1_tarski(esk8_0,k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_87]), c_0_94])])).
% 8.55/8.75  cnf(c_0_100, negated_conjecture, (r1_tarski(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_62])).
% 8.55/8.75  cnf(c_0_101, negated_conjecture, (r1_ordinal1(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_95, c_0_86])).
% 8.55/8.75  cnf(c_0_102, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 8.55/8.75  cnf(c_0_103, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_43, c_0_82])).
% 8.55/8.75  cnf(c_0_104, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_96, c_0_35])).
% 8.55/8.75  cnf(c_0_105, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 8.55/8.75  cnf(c_0_106, negated_conjecture, (~r2_hidden(k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))),esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_99])).
% 8.55/8.75  cnf(c_0_107, negated_conjecture, (r1_tarski(esk8_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_87]), c_0_101])])).
% 8.55/8.75  cnf(c_0_108, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 8.55/8.75  cnf(c_0_109, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0))))=esk8_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])).
% 8.55/8.75  cnf(c_0_110, negated_conjecture, (~r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_107])).
% 8.55/8.75  cnf(c_0_111, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk1_3(esk7_0,esk7_0,X1),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_108])).
% 8.55/8.75  cnf(c_0_112, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_26, c_0_92])).
% 8.55/8.75  cnf(c_0_113, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k1_tarski(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))))|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_109]), c_0_110])).
% 8.55/8.75  cnf(c_0_114, negated_conjecture, (r2_hidden(esk1_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_111, c_0_82])).
% 8.55/8.75  cnf(c_0_115, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,esk1_3(esk7_0,esk7_0,X1))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_78, c_0_108])).
% 8.55/8.75  cnf(c_0_116, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_87]), c_0_112])).
% 8.55/8.75  cnf(c_0_117, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=k2_xboole_0(esk7_0,k1_tarski(esk7_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_104, c_0_113])).
% 8.55/8.75  cnf(c_0_118, negated_conjecture, (r2_hidden(esk1_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_49, c_0_114])).
% 8.55/8.75  cnf(c_0_119, negated_conjecture, (r2_hidden(esk8_0,esk1_3(esk7_0,esk7_0,esk8_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_115, c_0_82])).
% 8.55/8.75  cnf(c_0_120, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_87])).
% 8.55/8.75  cnf(c_0_121, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 8.55/8.75  cnf(c_0_122, negated_conjecture, (r2_hidden(esk1_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_118, c_0_59])).
% 8.55/8.75  cnf(c_0_123, negated_conjecture, (r2_hidden(esk8_0,esk1_3(esk7_0,esk7_0,esk8_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_49, c_0_119])).
% 8.55/8.75  cnf(c_0_124, negated_conjecture, (r1_tarski(esk7_0,esk8_0)|~r1_ordinal1(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_120, c_0_18])).
% 8.55/8.75  cnf(c_0_125, negated_conjecture, (r1_ordinal1(esk7_0,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_59]), c_0_116])).
% 8.55/8.75  cnf(c_0_126, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,esk1_3(esk7_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_49, c_0_122])).
% 8.55/8.75  cnf(c_0_127, negated_conjecture, (r2_hidden(esk8_0,esk1_3(esk7_0,esk7_0,esk8_0))|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_123, c_0_59])).
% 8.55/8.75  cnf(c_0_128, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r1_tarski(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 8.55/8.75  cnf(c_0_129, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 8.55/8.75  cnf(c_0_130, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_128]), c_0_82])])).
% 8.55/8.75  cnf(c_0_131, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_129])).
% 8.55/8.75  cnf(c_0_132, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_104, c_0_130])).
% 8.55/8.75  cnf(c_0_133, negated_conjecture, (v3_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_29, c_0_131])).
% 8.55/8.75  cnf(c_0_134, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_116, c_0_132])).
% 8.55/8.75  cnf(c_0_135, negated_conjecture, (v3_ordinal1(esk1_3(esk7_0,esk7_0,esk8_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_133, c_0_108])).
% 8.55/8.75  cnf(c_0_136, negated_conjecture, (r1_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_134, c_0_131])).
% 8.55/8.75  cnf(c_0_137, negated_conjecture, (~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.55/8.75  cnf(c_0_138, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0)|~r1_ordinal1(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_120, c_0_135])).
% 8.55/8.75  cnf(c_0_139, negated_conjecture, (r1_ordinal1(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_136, c_0_108])).
% 8.55/8.75  cnf(c_0_140, negated_conjecture, (~v4_ordinal1(esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(rw,[status(thm)],[c_0_137, c_0_35])).
% 8.55/8.75  cnf(c_0_141, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk1_3(esk7_0,esk7_0,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 8.55/8.75  cnf(c_0_142, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk5_1(esk7_0),esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_140, c_0_28])).
% 8.55/8.75  cnf(c_0_143, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_141]), c_0_119])).
% 8.55/8.75  cnf(c_0_144, negated_conjecture, (r2_hidden(esk5_1(esk7_0),esk7_0)|r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_143])])).
% 8.55/8.75  cnf(c_0_145, negated_conjecture, (v3_ordinal1(esk5_1(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_144])).
% 8.55/8.75  cnf(c_0_146, negated_conjecture, (v3_ordinal1(k3_tarski(esk7_0))|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_145]), c_0_29])).
% 8.55/8.75  cnf(c_0_147, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(k3_tarski(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_146])).
% 8.55/8.75  cnf(c_0_148, negated_conjecture, (~v4_ordinal1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_143])])).
% 8.55/8.75  cnf(c_0_149, negated_conjecture, (r2_hidden(k3_tarski(esk7_0),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_147]), c_0_148])).
% 8.55/8.75  cnf(c_0_150, negated_conjecture, (r2_hidden(k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))),esk7_0)|r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_149]), c_0_148])).
% 8.55/8.75  cnf(c_0_151, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk7_0),k1_tarski(k3_tarski(esk7_0))))), inference(spm,[status(thm)],[c_0_49, c_0_150])).
% 8.55/8.75  cnf(c_0_152, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_59]), c_0_60])).
% 8.55/8.75  cnf(c_0_153, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_152])).
% 8.55/8.75  cnf(c_0_154, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_69, c_0_153])).
% 8.55/8.75  cnf(c_0_155, negated_conjecture, (v3_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_153])).
% 8.55/8.75  cnf(c_0_156, negated_conjecture, (r1_ordinal1(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_154])).
% 8.55/8.75  cnf(c_0_157, negated_conjecture, (r1_tarski(esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_155]), c_0_156])])).
% 8.55/8.75  cnf(c_0_158, negated_conjecture, (r2_hidden(esk7_0,esk1_3(esk7_0,k3_tarski(esk7_0),esk7_0))), inference(spm,[status(thm)],[c_0_78, c_0_152])).
% 8.55/8.75  cnf(c_0_159, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_157]), c_0_158])]), ['proof']).
% 8.55/8.75  # SZS output end CNFRefutation
% 8.55/8.75  # Proof object total steps             : 160
% 8.55/8.75  # Proof object clause steps            : 131
% 8.55/8.75  # Proof object formula steps           : 29
% 8.55/8.75  # Proof object conjectures             : 105
% 8.55/8.75  # Proof object clause conjectures      : 102
% 8.55/8.75  # Proof object formula conjectures     : 3
% 8.55/8.75  # Proof object initial clauses used    : 22
% 8.55/8.75  # Proof object initial formulas used   : 14
% 8.55/8.75  # Proof object generating inferences   : 95
% 8.55/8.75  # Proof object simplifying inferences  : 45
% 8.55/8.75  # Training examples: 0 positive, 0 negative
% 8.55/8.75  # Parsed axioms                        : 17
% 8.55/8.75  # Removed by relevancy pruning/SinE    : 0
% 8.55/8.75  # Initial clauses                      : 38
% 8.55/8.75  # Removed in clause preprocessing      : 1
% 8.55/8.75  # Initial clauses in saturation        : 37
% 8.55/8.75  # Processed clauses                    : 11528
% 8.55/8.75  # ...of these trivial                  : 179
% 8.55/8.75  # ...subsumed                          : 5021
% 8.55/8.75  # ...remaining for further processing  : 6328
% 8.55/8.75  # Other redundant clauses eliminated   : 465
% 8.55/8.75  # Clauses deleted for lack of memory   : 0
% 8.55/8.75  # Backward-subsumed                    : 1330
% 8.55/8.75  # Backward-rewritten                   : 1408
% 8.55/8.75  # Generated clauses                    : 657958
% 8.55/8.75  # ...of the previous two non-trivial   : 608706
% 8.55/8.75  # Contextual simplify-reflections      : 108
% 8.55/8.75  # Paramodulations                      : 657417
% 8.55/8.75  # Factorizations                       : 14
% 8.55/8.75  # Equation resolutions                 : 465
% 8.55/8.75  # Propositional unsat checks           : 0
% 8.55/8.75  #    Propositional check models        : 0
% 8.55/8.75  #    Propositional check unsatisfiable : 0
% 8.55/8.75  #    Propositional clauses             : 0
% 8.55/8.75  #    Propositional clauses after purity: 0
% 8.55/8.75  #    Propositional unsat core size     : 0
% 8.55/8.75  #    Propositional preprocessing time  : 0.000
% 8.55/8.75  #    Propositional encoding time       : 0.000
% 8.55/8.75  #    Propositional solver time         : 0.000
% 8.55/8.75  #    Success case prop preproc time    : 0.000
% 8.55/8.75  #    Success case prop encoding time   : 0.000
% 8.55/8.75  #    Success case prop solver time     : 0.000
% 8.55/8.75  # Current number of processed clauses  : 3487
% 8.55/8.75  #    Positive orientable unit clauses  : 798
% 8.55/8.75  #    Positive unorientable unit clauses: 0
% 8.55/8.75  #    Negative unit clauses             : 50
% 8.55/8.75  #    Non-unit-clauses                  : 2639
% 8.55/8.75  # Current number of unprocessed clauses: 593570
% 8.55/8.75  # ...number of literals in the above   : 3330637
% 8.55/8.75  # Current number of archived formulas  : 0
% 8.55/8.75  # Current number of archived clauses   : 2836
% 8.55/8.75  # Clause-clause subsumption calls (NU) : 2886930
% 8.55/8.75  # Rec. Clause-clause subsumption calls : 910757
% 8.55/8.75  # Non-unit clause-clause subsumptions  : 5221
% 8.55/8.75  # Unit Clause-clause subsumption calls : 514496
% 8.55/8.75  # Rewrite failures with RHS unbound    : 0
% 8.55/8.75  # BW rewrite match attempts            : 9151
% 8.55/8.75  # BW rewrite match successes           : 129
% 8.55/8.75  # Condensation attempts                : 0
% 8.55/8.75  # Condensation successes               : 0
% 8.55/8.75  # Termbank termtop insertions          : 19186498
% 8.61/8.78  
% 8.61/8.78  # -------------------------------------------------
% 8.61/8.78  # User time                : 8.196 s
% 8.61/8.78  # System time              : 0.243 s
% 8.61/8.78  # Total time               : 8.439 s
% 8.61/8.78  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
