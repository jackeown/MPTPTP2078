%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:34 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  129 (35314 expanded)
%              Number of clauses        :  102 (15928 expanded)
%              Number of leaves         :   13 (8384 expanded)
%              Depth                    :   37
%              Number of atoms          :  367 (146281 expanded)
%              Number of equality atoms :   32 (17788 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t41_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_13,plain,(
    ! [X35] :
      ( ~ v3_ordinal1(X35)
      | v3_ordinal1(k1_ordinal1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_14,plain,(
    ! [X22] : k1_ordinal1(X22) = k2_xboole_0(X22,k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

cnf(c_0_16,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ! [X44] :
      ( v3_ordinal1(esk6_0)
      & ( v3_ordinal1(esk7_0)
        | ~ v4_ordinal1(esk6_0) )
      & ( r2_hidden(esk7_0,esk6_0)
        | ~ v4_ordinal1(esk6_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk7_0),esk6_0)
        | ~ v4_ordinal1(esk6_0) )
      & ( v4_ordinal1(esk6_0)
        | ~ v3_ordinal1(X44)
        | ~ r2_hidden(X44,esk6_0)
        | r2_hidden(k1_ordinal1(X44),esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

fof(c_0_19,plain,(
    ! [X27] :
      ( ( ~ v4_ordinal1(X27)
        | X27 = k3_tarski(X27) )
      & ( X27 != k3_tarski(X27)
        | v4_ordinal1(X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

fof(c_0_20,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X38,X39] :
      ( ( ~ r2_hidden(X38,k1_ordinal1(X39))
        | r1_ordinal1(X38,X39)
        | ~ v3_ordinal1(X39)
        | ~ v3_ordinal1(X38) )
      & ( ~ r1_ordinal1(X38,X39)
        | r2_hidden(X38,k1_ordinal1(X39))
        | ~ v3_ordinal1(X39)
        | ~ v3_ordinal1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

fof(c_0_22,plain,(
    ! [X33,X34] :
      ( ~ v3_ordinal1(X34)
      | ~ r2_hidden(X33,X34)
      | v3_ordinal1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_23,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X31,X32] :
      ( ( ~ r2_hidden(X31,k1_ordinal1(X32))
        | r2_hidden(X31,X32)
        | X31 = X32 )
      & ( ~ r2_hidden(X31,X32)
        | r2_hidden(X31,k1_ordinal1(X32)) )
      & ( X31 != X32
        | r2_hidden(X31,k1_ordinal1(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_26,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk6_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ v4_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk4_2(X1,X1),X1)
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

fof(c_0_34,plain,(
    ! [X28,X29] :
      ( ( ~ r1_ordinal1(X28,X29)
        | r1_tarski(X28,X29)
        | ~ v3_ordinal1(X28)
        | ~ v3_ordinal1(X29) )
      & ( ~ r1_tarski(X28,X29)
        | r1_ordinal1(X28,X29)
        | ~ v3_ordinal1(X28)
        | ~ v3_ordinal1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_35,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( r1_ordinal1(X1,esk6_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk6_0),k2_xboole_0(esk6_0,k1_tarski(esk6_0)))
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_43,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r1_ordinal1(X1,esk6_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( v3_ordinal1(esk4_2(esk6_0,esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_ordinal1(esk4_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( v4_ordinal1(esk6_0)
    | r2_hidden(k1_ordinal1(X1),esk6_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0)
    | r1_tarski(esk4_2(esk6_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_47])])).

cnf(c_0_52,negated_conjecture,
    ( v4_ordinal1(esk6_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk6_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_2(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk4_2(esk6_0,esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( v4_ordinal1(esk6_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_57,plain,(
    ! [X30] : r2_hidden(X30,k1_ordinal1(X30)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_58,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))),esk6_0)
    | r2_hidden(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_32])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k3_tarski(esk6_0)
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk3_2(esk6_0,X1),k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))))
    | ~ r2_hidden(esk3_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( k3_tarski(esk6_0) = esk6_0
    | r2_hidden(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_63]),c_0_32])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( v4_ordinal1(esk6_0)
    | r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_64])).

cnf(c_0_68,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k3_tarski(esk6_0) = esk6_0
    | r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_71,plain,(
    ! [X36,X37] :
      ( ( ~ r2_hidden(X36,X37)
        | r1_ordinal1(k1_ordinal1(X36),X37)
        | ~ v3_ordinal1(X37)
        | ~ v3_ordinal1(X36) )
      & ( ~ r1_ordinal1(k1_ordinal1(X36),X37)
        | r2_hidden(X36,X37)
        | ~ v3_ordinal1(X37)
        | ~ v3_ordinal1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)
    | r2_hidden(esk2_3(esk6_0,esk6_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk6_0,esk7_0),esk6_0)
    | r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)
    | r2_hidden(X1,esk2_3(esk6_0,esk6_0,X1))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_69])).

cnf(c_0_79,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_17])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk6_0,esk7_0),esk6_0)
    | r2_hidden(X1,k3_tarski(esk6_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk6_0,esk6_0,esk7_0))
    | r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_64])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_83,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_79,c_0_29])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,esk6_0,esk7_0),esk6_0)
    | r2_hidden(esk7_0,k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_62])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk6_0,esk6_0,esk7_0))
    | r2_hidden(X1,k3_tarski(esk6_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_64])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_82,c_0_17])).

cnf(c_0_88,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk6_0))
    | r2_hidden(X1,k3_tarski(esk6_0))
    | ~ r2_hidden(X1,esk2_3(esk6_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk6_0,esk6_0,esk7_0))
    | r2_hidden(esk7_0,k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_62])).

cnf(c_0_91,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_86])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))
    | ~ r1_ordinal1(X1,esk6_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_24])).

cnf(c_0_94,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_64])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_91])).

cnf(c_0_97,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_92,c_0_17])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k2_xboole_0(esk6_0,k1_tarski(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_91]),c_0_94])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_86]),c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( k2_xboole_0(esk7_0,k1_tarski(esk7_0)) = esk6_0
    | r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk7_0),esk6_0)
    | ~ v4_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_106,plain,(
    ! [X40,X41] :
      ( ~ r2_hidden(X40,X41)
      | ~ r1_tarski(X41,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0)
    | ~ r1_ordinal1(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0)
    | r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_99])).

cnf(c_0_109,negated_conjecture,
    ( ~ v4_ordinal1(esk6_0)
    | ~ r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_17])).

cnf(c_0_110,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)
    | r1_tarski(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk7_0,esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_95])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(esk6_0,esk6_0),esk6_0)
    | ~ r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_33])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk6_0),k2_xboole_0(esk6_0,k1_tarski(esk6_0)))
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( v3_ordinal1(esk4_2(esk6_0,esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( r1_ordinal1(esk4_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r1_tarski(esk4_2(esk6_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_117]),c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk4_2(esk6_0,esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | ~ r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_51])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_2(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk4_2(esk6_0,esk6_0))
    | r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_114])])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_124,negated_conjecture,
    ( ~ v4_ordinal1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_114])])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_123]),c_0_124])).

cnf(c_0_126,negated_conjecture,
    ( X1 = k3_tarski(esk6_0)
    | ~ r2_hidden(esk3_2(esk6_0,X1),k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))))
    | ~ r2_hidden(esk3_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_125])).

cnf(c_0_127,negated_conjecture,
    ( k3_tarski(esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_123]),c_0_62])])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_127]),c_0_124]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.11/5.28  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 5.11/5.28  # and selection function SelectCQIArEqFirst.
% 5.11/5.28  #
% 5.11/5.28  # Preprocessing time       : 0.029 s
% 5.11/5.28  # Presaturation interreduction done
% 5.11/5.28  
% 5.11/5.28  # Proof found!
% 5.11/5.28  # SZS status Theorem
% 5.11/5.28  # SZS output start CNFRefutation
% 5.11/5.28  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.11/5.28  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.11/5.28  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 5.11/5.28  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 5.11/5.28  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 5.11/5.28  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 5.11/5.28  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 5.11/5.28  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.11/5.28  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.11/5.28  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.11/5.28  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 5.11/5.28  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.11/5.28  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.11/5.28  fof(c_0_13, plain, ![X35]:(~v3_ordinal1(X35)|v3_ordinal1(k1_ordinal1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 5.11/5.28  fof(c_0_14, plain, ![X22]:k1_ordinal1(X22)=k2_xboole_0(X22,k1_tarski(X22)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 5.11/5.28  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 5.11/5.28  cnf(c_0_16, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.11/5.28  cnf(c_0_17, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.11/5.28  fof(c_0_18, negated_conjecture, ![X44]:(v3_ordinal1(esk6_0)&(((v3_ordinal1(esk7_0)|~v4_ordinal1(esk6_0))&((r2_hidden(esk7_0,esk6_0)|~v4_ordinal1(esk6_0))&(~r2_hidden(k1_ordinal1(esk7_0),esk6_0)|~v4_ordinal1(esk6_0))))&(v4_ordinal1(esk6_0)|(~v3_ordinal1(X44)|(~r2_hidden(X44,esk6_0)|r2_hidden(k1_ordinal1(X44),esk6_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).
% 5.11/5.28  fof(c_0_19, plain, ![X27]:((~v4_ordinal1(X27)|X27=k3_tarski(X27))&(X27!=k3_tarski(X27)|v4_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 5.11/5.28  fof(c_0_20, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(X13,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k3_tarski(X11))&(r2_hidden(esk2_3(X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k3_tarski(X11)))&(~r2_hidden(X15,X16)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k3_tarski(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|(~r2_hidden(esk3_2(X17,X18),X20)|~r2_hidden(X20,X17))|X18=k3_tarski(X17))&((r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))&(r2_hidden(esk4_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 5.11/5.28  fof(c_0_21, plain, ![X38, X39]:((~r2_hidden(X38,k1_ordinal1(X39))|r1_ordinal1(X38,X39)|~v3_ordinal1(X39)|~v3_ordinal1(X38))&(~r1_ordinal1(X38,X39)|r2_hidden(X38,k1_ordinal1(X39))|~v3_ordinal1(X39)|~v3_ordinal1(X38))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 5.11/5.28  fof(c_0_22, plain, ![X33, X34]:(~v3_ordinal1(X34)|(~r2_hidden(X33,X34)|v3_ordinal1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 5.11/5.28  cnf(c_0_23, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 5.11/5.28  cnf(c_0_24, negated_conjecture, (v3_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.11/5.28  fof(c_0_25, plain, ![X31, X32]:((~r2_hidden(X31,k1_ordinal1(X32))|(r2_hidden(X31,X32)|X31=X32))&((~r2_hidden(X31,X32)|r2_hidden(X31,k1_ordinal1(X32)))&(X31!=X32|r2_hidden(X31,k1_ordinal1(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 5.11/5.28  cnf(c_0_26, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.11/5.28  cnf(c_0_27, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.11/5.28  cnf(c_0_28, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.11/5.28  cnf(c_0_29, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.11/5.28  cnf(c_0_30, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk6_0,k1_tarski(esk6_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 5.11/5.28  cnf(c_0_31, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.11/5.28  cnf(c_0_32, negated_conjecture, (r2_hidden(esk7_0,esk6_0)|~v4_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.11/5.28  cnf(c_0_33, plain, (v4_ordinal1(X1)|r2_hidden(esk4_2(X1,X1),X1)|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 5.11/5.28  fof(c_0_34, plain, ![X28, X29]:((~r1_ordinal1(X28,X29)|r1_tarski(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))&(~r1_tarski(X28,X29)|r1_ordinal1(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 5.11/5.28  cnf(c_0_35, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_28, c_0_17])).
% 5.11/5.28  cnf(c_0_36, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 5.11/5.28  cnf(c_0_37, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_17])).
% 5.11/5.28  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk4_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.11/5.28  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 5.11/5.28  cnf(c_0_40, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_24])).
% 5.11/5.28  cnf(c_0_41, negated_conjecture, (r1_ordinal1(X1,esk6_0)|~r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_24]), c_0_36])).
% 5.11/5.28  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk6_0),k2_xboole_0(esk6_0,k1_tarski(esk6_0)))|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 5.11/5.28  fof(c_0_43, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 5.11/5.28  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,esk6_0)|~r1_ordinal1(X1,esk6_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 5.11/5.28  cnf(c_0_45, negated_conjecture, (v3_ordinal1(esk4_2(esk6_0,esk6_0))|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 5.11/5.28  cnf(c_0_46, negated_conjecture, (r1_ordinal1(esk4_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 5.11/5.28  cnf(c_0_47, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.11/5.28  cnf(c_0_48, negated_conjecture, (v4_ordinal1(esk6_0)|r2_hidden(k1_ordinal1(X1),esk6_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.11/5.28  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.11/5.28  cnf(c_0_50, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)|r1_tarski(esk4_2(esk6_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 5.11/5.28  cnf(c_0_51, plain, (v4_ordinal1(X1)|r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_47])])).
% 5.11/5.28  cnf(c_0_52, negated_conjecture, (v4_ordinal1(esk6_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk6_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_48, c_0_17])).
% 5.11/5.28  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_2(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 5.11/5.28  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk4_2(esk6_0,esk6_0))|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_51])).
% 5.11/5.28  cnf(c_0_55, negated_conjecture, (v4_ordinal1(esk6_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk6_0)|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[c_0_52, c_0_40])).
% 5.11/5.28  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 5.11/5.28  fof(c_0_57, plain, ![X30]:r2_hidden(X30,k1_ordinal1(X30)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 5.11/5.28  cnf(c_0_58, plain, (X2=k3_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(esk3_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.11/5.28  cnf(c_0_59, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))),esk6_0)|r2_hidden(esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_32])).
% 5.11/5.28  cnf(c_0_60, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 5.11/5.28  cnf(c_0_61, negated_conjecture, (X1=k3_tarski(esk6_0)|r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk3_2(esk6_0,X1),k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))))|~r2_hidden(esk3_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 5.11/5.28  cnf(c_0_62, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_60, c_0_17])).
% 5.11/5.28  cnf(c_0_63, negated_conjecture, (k3_tarski(esk6_0)=esk6_0|r2_hidden(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_62])])).
% 5.11/5.28  cnf(c_0_64, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_63]), c_0_32])).
% 5.11/5.28  cnf(c_0_65, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.11/5.28  cnf(c_0_66, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.11/5.28  cnf(c_0_67, negated_conjecture, (v4_ordinal1(esk6_0)|r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_64])).
% 5.11/5.28  cnf(c_0_68, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_65])).
% 5.11/5.28  cnf(c_0_69, negated_conjecture, (k3_tarski(esk6_0)=esk6_0|r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 5.11/5.28  cnf(c_0_70, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.11/5.28  fof(c_0_71, plain, ![X36, X37]:((~r2_hidden(X36,X37)|r1_ordinal1(k1_ordinal1(X36),X37)|~v3_ordinal1(X37)|~v3_ordinal1(X36))&(~r1_ordinal1(k1_ordinal1(X36),X37)|r2_hidden(X36,X37)|~v3_ordinal1(X37)|~v3_ordinal1(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 5.11/5.28  cnf(c_0_72, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.11/5.28  cnf(c_0_73, negated_conjecture, (r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)|r2_hidden(esk2_3(esk6_0,esk6_0,X1),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 5.11/5.28  cnf(c_0_74, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_70])).
% 5.11/5.28  cnf(c_0_75, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 5.11/5.28  cnf(c_0_76, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_72])).
% 5.11/5.28  cnf(c_0_77, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk6_0,esk7_0),esk6_0)|r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_73, c_0_64])).
% 5.11/5.28  cnf(c_0_78, negated_conjecture, (r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)|r2_hidden(X1,esk2_3(esk6_0,esk6_0,X1))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_74, c_0_69])).
% 5.11/5.28  cnf(c_0_79, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_75, c_0_17])).
% 5.11/5.28  cnf(c_0_80, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk6_0,esk7_0),esk6_0)|r2_hidden(X1,k3_tarski(esk6_0))|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 5.11/5.28  cnf(c_0_81, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk6_0,esk6_0,esk7_0))|r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_78, c_0_64])).
% 5.11/5.28  cnf(c_0_82, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.11/5.28  cnf(c_0_83, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_79, c_0_29])).
% 5.11/5.28  cnf(c_0_84, negated_conjecture, (r2_hidden(esk2_3(esk6_0,esk6_0,esk7_0),esk6_0)|r2_hidden(esk7_0,k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_80, c_0_62])).
% 5.11/5.28  cnf(c_0_85, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk6_0,esk6_0,esk7_0))|r2_hidden(X1,k3_tarski(esk6_0))|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_76, c_0_81])).
% 5.11/5.28  cnf(c_0_86, negated_conjecture, (v3_ordinal1(esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_64])).
% 5.11/5.28  cnf(c_0_87, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_82, c_0_17])).
% 5.11/5.28  cnf(c_0_88, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_83, c_0_24])).
% 5.11/5.28  cnf(c_0_89, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk6_0))|r2_hidden(X1,k3_tarski(esk6_0))|~r2_hidden(X1,esk2_3(esk6_0,esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_76, c_0_84])).
% 5.11/5.28  cnf(c_0_90, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk6_0,esk6_0,esk7_0))|r2_hidden(esk7_0,k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_85, c_0_62])).
% 5.11/5.28  cnf(c_0_91, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_23, c_0_86])).
% 5.11/5.28  cnf(c_0_92, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.11/5.28  cnf(c_0_93, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))|~r1_ordinal1(X1,esk6_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_87, c_0_24])).
% 5.11/5.28  cnf(c_0_94, negated_conjecture, (r1_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_88, c_0_64])).
% 5.11/5.28  cnf(c_0_95, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 5.11/5.28  cnf(c_0_96, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_29, c_0_91])).
% 5.11/5.28  cnf(c_0_97, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_92, c_0_17])).
% 5.11/5.28  cnf(c_0_98, negated_conjecture, (r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),k2_xboole_0(esk6_0,k1_tarski(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_91]), c_0_94])])).
% 5.11/5.28  cnf(c_0_99, negated_conjecture, (r2_hidden(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_95])).
% 5.11/5.28  cnf(c_0_100, negated_conjecture, (r1_ordinal1(X1,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_86]), c_0_96])).
% 5.11/5.28  cnf(c_0_101, negated_conjecture, (k2_xboole_0(esk7_0,k1_tarski(esk7_0))=esk6_0|r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 5.11/5.28  cnf(c_0_102, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_86])).
% 5.11/5.28  cnf(c_0_103, negated_conjecture, (v3_ordinal1(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_40, c_0_99])).
% 5.11/5.28  cnf(c_0_104, negated_conjecture, (r1_ordinal1(X1,esk7_0)|r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 5.11/5.28  cnf(c_0_105, negated_conjecture, (~r2_hidden(k1_ordinal1(esk7_0),esk6_0)|~v4_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.11/5.28  fof(c_0_106, plain, ![X40, X41]:(~r2_hidden(X40,X41)|~r1_tarski(X41,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 5.11/5.28  cnf(c_0_107, negated_conjecture, (r1_tarski(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0)|~r1_ordinal1(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 5.11/5.28  cnf(c_0_108, negated_conjecture, (r1_ordinal1(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0)|r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_104, c_0_99])).
% 5.11/5.28  cnf(c_0_109, negated_conjecture, (~v4_ordinal1(esk6_0)|~r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(rw,[status(thm)],[c_0_105, c_0_17])).
% 5.11/5.28  cnf(c_0_110, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 5.11/5.28  cnf(c_0_111, negated_conjecture, (r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)|r1_tarski(esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 5.11/5.28  cnf(c_0_112, negated_conjecture, (r2_hidden(esk7_0,esk2_3(esk6_0,k3_tarski(esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_74, c_0_95])).
% 5.11/5.28  cnf(c_0_113, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk4_2(esk6_0,esk6_0),esk6_0)|~r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_109, c_0_33])).
% 5.11/5.28  cnf(c_0_114, negated_conjecture, (r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112])])).
% 5.11/5.28  cnf(c_0_115, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114])])).
% 5.11/5.28  cnf(c_0_116, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk6_0),k2_xboole_0(esk6_0,k1_tarski(esk6_0)))|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_115])).
% 5.11/5.28  cnf(c_0_117, negated_conjecture, (v3_ordinal1(esk4_2(esk6_0,esk6_0))|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_115])).
% 5.11/5.28  cnf(c_0_118, negated_conjecture, (r1_ordinal1(esk4_2(esk6_0,esk6_0),esk6_0)|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_116])).
% 5.11/5.28  cnf(c_0_119, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r1_tarski(esk4_2(esk6_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_117]), c_0_118])).
% 5.11/5.28  cnf(c_0_120, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk4_2(esk6_0,esk6_0))|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|~r2_hidden(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_109, c_0_51])).
% 5.11/5.28  cnf(c_0_121, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_2(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_119])).
% 5.11/5.28  cnf(c_0_122, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk4_2(esk6_0,esk6_0))|r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_114])])).
% 5.11/5.28  cnf(c_0_123, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 5.11/5.28  cnf(c_0_124, negated_conjecture, (~v4_ordinal1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_114])])).
% 5.11/5.28  cnf(c_0_125, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_123]), c_0_124])).
% 5.11/5.28  cnf(c_0_126, negated_conjecture, (X1=k3_tarski(esk6_0)|~r2_hidden(esk3_2(esk6_0,X1),k2_xboole_0(esk3_2(esk6_0,esk6_0),k1_tarski(esk3_2(esk6_0,esk6_0))))|~r2_hidden(esk3_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_58, c_0_125])).
% 5.11/5.28  cnf(c_0_127, negated_conjecture, (k3_tarski(esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_123]), c_0_62])])).
% 5.11/5.28  cnf(c_0_128, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_127]), c_0_124]), ['proof']).
% 5.11/5.28  # SZS output end CNFRefutation
% 5.11/5.28  # Proof object total steps             : 129
% 5.11/5.28  # Proof object clause steps            : 102
% 5.11/5.28  # Proof object formula steps           : 27
% 5.11/5.28  # Proof object conjectures             : 72
% 5.11/5.28  # Proof object clause conjectures      : 69
% 5.11/5.28  # Proof object formula conjectures     : 3
% 5.11/5.28  # Proof object initial clauses used    : 24
% 5.11/5.28  # Proof object initial formulas used   : 13
% 5.11/5.28  # Proof object generating inferences   : 61
% 5.11/5.28  # Proof object simplifying inferences  : 38
% 5.11/5.28  # Training examples: 0 positive, 0 negative
% 5.11/5.28  # Parsed axioms                        : 14
% 5.11/5.28  # Removed by relevancy pruning/SinE    : 0
% 5.11/5.28  # Initial clauses                      : 33
% 5.11/5.28  # Removed in clause preprocessing      : 1
% 5.11/5.28  # Initial clauses in saturation        : 32
% 5.11/5.28  # Processed clauses                    : 9131
% 5.11/5.28  # ...of these trivial                  : 114
% 5.11/5.28  # ...subsumed                          : 4031
% 5.11/5.28  # ...remaining for further processing  : 4986
% 5.11/5.28  # Other redundant clauses eliminated   : 20
% 5.11/5.28  # Clauses deleted for lack of memory   : 0
% 5.11/5.28  # Backward-subsumed                    : 722
% 5.11/5.28  # Backward-rewritten                   : 2459
% 5.11/5.28  # Generated clauses                    : 490126
% 5.11/5.28  # ...of the previous two non-trivial   : 478144
% 5.11/5.28  # Contextual simplify-reflections      : 134
% 5.11/5.28  # Paramodulations                      : 490091
% 5.11/5.28  # Factorizations                       : 4
% 5.11/5.28  # Equation resolutions                 : 20
% 5.11/5.28  # Propositional unsat checks           : 0
% 5.11/5.28  #    Propositional check models        : 0
% 5.11/5.28  #    Propositional check unsatisfiable : 0
% 5.11/5.28  #    Propositional clauses             : 0
% 5.11/5.28  #    Propositional clauses after purity: 0
% 5.11/5.28  #    Propositional unsat core size     : 0
% 5.11/5.28  #    Propositional preprocessing time  : 0.000
% 5.11/5.28  #    Propositional encoding time       : 0.000
% 5.11/5.28  #    Propositional solver time         : 0.000
% 5.11/5.28  #    Success case prop preproc time    : 0.000
% 5.11/5.28  #    Success case prop encoding time   : 0.000
% 5.11/5.28  #    Success case prop solver time     : 0.000
% 5.11/5.28  # Current number of processed clauses  : 1759
% 5.11/5.28  #    Positive orientable unit clauses  : 299
% 5.11/5.28  #    Positive unorientable unit clauses: 0
% 5.11/5.28  #    Negative unit clauses             : 81
% 5.11/5.28  #    Non-unit-clauses                  : 1379
% 5.11/5.28  # Current number of unprocessed clauses: 467776
% 5.11/5.28  # ...number of literals in the above   : 2705495
% 5.11/5.28  # Current number of archived formulas  : 0
% 5.11/5.28  # Current number of archived clauses   : 3224
% 5.11/5.28  # Clause-clause subsumption calls (NU) : 1151080
% 5.11/5.28  # Rec. Clause-clause subsumption calls : 307989
% 5.11/5.28  # Non-unit clause-clause subsumptions  : 3950
% 5.11/5.28  # Unit Clause-clause subsumption calls : 84629
% 5.11/5.28  # Rewrite failures with RHS unbound    : 0
% 5.11/5.28  # BW rewrite match attempts            : 836
% 5.11/5.28  # BW rewrite match successes           : 101
% 5.11/5.28  # Condensation attempts                : 0
% 5.11/5.28  # Condensation successes               : 0
% 5.11/5.28  # Termbank termtop insertions          : 16438872
% 5.11/5.29  
% 5.11/5.29  # -------------------------------------------------
% 5.11/5.29  # User time                : 4.778 s
% 5.11/5.29  # System time              : 0.176 s
% 5.11/5.29  # Total time               : 4.955 s
% 5.11/5.29  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
