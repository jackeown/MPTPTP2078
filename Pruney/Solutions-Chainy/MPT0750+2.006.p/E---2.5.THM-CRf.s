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
% DateTime   : Thu Dec  3 10:56:32 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :  143 (58218 expanded)
%              Number of clauses        :  112 (26112 expanded)
%              Number of leaves         :   15 (13794 expanded)
%              Depth                    :   40
%              Number of atoms          :  407 (226883 expanded)
%              Number of equality atoms :   37 (21882 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,axiom,(
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

fof(t41_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

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

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

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

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

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

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(c_0_15,plain,(
    ! [X42,X43] :
      ( ( ~ r2_hidden(X42,k1_ordinal1(X43))
        | r1_ordinal1(X42,X43)
        | ~ v3_ordinal1(X43)
        | ~ v3_ordinal1(X42) )
      & ( ~ r1_ordinal1(X42,X43)
        | r2_hidden(X42,k1_ordinal1(X43))
        | ~ v3_ordinal1(X43)
        | ~ v3_ordinal1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

fof(c_0_16,plain,(
    ! [X26] : k1_ordinal1(X26) = k2_xboole_0(X26,k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_18,plain,(
    ! [X39] :
      ( ~ v3_ordinal1(X39)
      | v3_ordinal1(k1_ordinal1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,negated_conjecture,(
    ! [X51] :
      ( v3_ordinal1(esk7_0)
      & ( v3_ordinal1(esk8_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
        | ~ v4_ordinal1(esk7_0) )
      & ( v4_ordinal1(esk7_0)
        | ~ v3_ordinal1(X51)
        | ~ r2_hidden(X51,esk7_0)
        | r2_hidden(k1_ordinal1(X51),esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])])).

cnf(c_0_23,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | ~ r1_tarski(X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X24)
      | ~ v3_ordinal1(X25)
      | r1_ordinal1(X24,X25)
      | r1_ordinal1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | r1_ordinal1(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_40,plain,(
    ! [X27] :
      ( ( ~ v4_ordinal1(X27)
        | X27 = k3_tarski(X27) )
      & ( X27 != k3_tarski(X27)
        | v4_ordinal1(X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

fof(c_0_41,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(X15,esk2_3(X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(esk3_2(X19,X20),X22)
        | ~ r2_hidden(X22,X19)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X19)
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_42,plain,(
    ! [X35,X36] :
      ( ~ v3_ordinal1(X36)
      | ~ r2_hidden(X35,X36)
      | v3_ordinal1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

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
    ( r1_tarski(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_ordinal1(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_39])).

cnf(c_0_46,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_28]),c_0_45])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk4_2(X1,X1),X1)
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_54,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk4_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( r1_ordinal1(X1,esk7_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_ordinal1(X1,esk7_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( v3_ordinal1(esk4_2(esk7_0,esk7_0))
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_ordinal1(esk4_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k1_ordinal1(X1),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0)
    | r1_tarski(esk4_2(esk7_0,esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_67,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_64])])).

cnf(c_0_68,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0)
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk4_2(esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk4_2(esk7_0,esk7_0))
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[c_0_68,c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_73,plain,(
    ! [X34] : r2_hidden(X34,k1_ordinal1(X34)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_74,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_52])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( X1 = k3_tarski(esk7_0)
    | r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(esk3_2(esk7_0,X1),k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))))
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_76,c_0_21])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_72]),c_0_78])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_79]),c_0_52])).

cnf(c_0_81,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_82,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( v4_ordinal1(esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_80])).

fof(c_0_84,plain,(
    ! [X40,X41] :
      ( ( ~ r2_hidden(X40,X41)
        | r1_ordinal1(k1_ordinal1(X40),X41)
        | ~ v3_ordinal1(X41)
        | ~ v3_ordinal1(X40) )
      & ( ~ r1_ordinal1(k1_ordinal1(X40),X41)
        | r2_hidden(X40,X41)
        | ~ v3_ordinal1(X41)
        | ~ v3_ordinal1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_85,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_88,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_92,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_88,c_0_21])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_80])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_86])).

cnf(c_0_96,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_92,c_0_49])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_80])).

fof(c_0_99,plain,(
    ! [X37,X38] :
      ( ~ v3_ordinal1(X37)
      | ~ v3_ordinal1(X38)
      | r2_hidden(X37,X38)
      | X37 = X38
      | r2_hidden(X38,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_100,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_80])).

cnf(c_0_101,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_28])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_78])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_98])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_80])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0))
    | r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))
    | r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_78])).

cnf(c_0_109,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(X1,esk7_0)
    | r2_hidden(esk7_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_28])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_105]),c_0_106])])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk8_0,k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = esk7_0
    | r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_100]),c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(esk8_0,k1_tarski(esk8_0)) = esk7_0
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(sr,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_100])).

cnf(c_0_119,negated_conjecture,
    ( v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk8_0),esk7_0)
    | ~ v4_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | ~ r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)
    | r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_121,c_0_21])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)
    | r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_111])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk4_2(esk7_0,esk7_0),esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_53])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_125]),c_0_126])])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128])])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( v3_ordinal1(esk4_2(esk7_0,esk7_0))
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( r1_ordinal1(esk4_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r1_tarski(esk4_2(esk7_0,esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_131]),c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk4_2(esk7_0,esk7_0))
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | ~ r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_67])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk4_2(esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk4_2(esk7_0,esk7_0))
    | r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_128])])).

cnf(c_0_137,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_138,negated_conjecture,
    ( ~ v4_ordinal1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_128])])).

cnf(c_0_139,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_137]),c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( X1 = k3_tarski(esk7_0)
    | ~ r2_hidden(esk3_2(esk7_0,X1),k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))))
    | ~ r2_hidden(esk3_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_139])).

cnf(c_0_141,negated_conjecture,
    ( k3_tarski(esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_137]),c_0_78])])).

cnf(c_0_142,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_141]),c_0_138]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 5.62/5.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 5.62/5.78  # and selection function SelectCQIArEqFirst.
% 5.62/5.78  #
% 5.62/5.78  # Preprocessing time       : 0.029 s
% 5.62/5.78  # Presaturation interreduction done
% 5.62/5.78  
% 5.62/5.78  # Proof found!
% 5.62/5.78  # SZS status Theorem
% 5.62/5.78  # SZS output start CNFRefutation
% 5.62/5.78  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 5.62/5.78  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.62/5.78  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 5.62/5.78  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.62/5.78  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.63/5.78  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.63/5.78  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 5.63/5.78  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.63/5.78  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 5.63/5.78  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 5.63/5.78  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 5.63/5.78  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.63/5.78  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 5.63/5.78  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.63/5.78  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 5.63/5.78  fof(c_0_15, plain, ![X42, X43]:((~r2_hidden(X42,k1_ordinal1(X43))|r1_ordinal1(X42,X43)|~v3_ordinal1(X43)|~v3_ordinal1(X42))&(~r1_ordinal1(X42,X43)|r2_hidden(X42,k1_ordinal1(X43))|~v3_ordinal1(X43)|~v3_ordinal1(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 5.63/5.78  fof(c_0_16, plain, ![X26]:k1_ordinal1(X26)=k2_xboole_0(X26,k1_tarski(X26)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 5.63/5.78  fof(c_0_17, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 5.63/5.78  fof(c_0_18, plain, ![X39]:(~v3_ordinal1(X39)|v3_ordinal1(k1_ordinal1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 5.63/5.78  fof(c_0_19, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.63/5.78  cnf(c_0_20, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.63/5.78  cnf(c_0_21, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.63/5.78  fof(c_0_22, negated_conjecture, ![X51]:(v3_ordinal1(esk7_0)&(((v3_ordinal1(esk8_0)|~v4_ordinal1(esk7_0))&((r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0))&(~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0))))&(v4_ordinal1(esk7_0)|(~v3_ordinal1(X51)|(~r2_hidden(X51,esk7_0)|r2_hidden(k1_ordinal1(X51),esk7_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])])).
% 5.63/5.78  cnf(c_0_23, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.63/5.78  fof(c_0_24, plain, ![X47, X48]:(~r2_hidden(X47,X48)|~r1_tarski(X48,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 5.63/5.78  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.63/5.78  fof(c_0_26, plain, ![X24, X25]:(~v3_ordinal1(X24)|~v3_ordinal1(X25)|(r1_ordinal1(X24,X25)|r1_ordinal1(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 5.63/5.78  cnf(c_0_27, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 5.63/5.78  cnf(c_0_28, negated_conjecture, (v3_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.63/5.78  cnf(c_0_29, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_23, c_0_21])).
% 5.63/5.78  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.63/5.78  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 5.63/5.78  fof(c_0_32, plain, ![X28, X29]:((~r1_ordinal1(X28,X29)|r1_tarski(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))&(~r1_tarski(X28,X29)|r1_ordinal1(X28,X29)|(~v3_ordinal1(X28)|~v3_ordinal1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 5.63/5.78  cnf(c_0_33, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.63/5.78  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 5.63/5.78  cnf(c_0_35, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 5.63/5.78  cnf(c_0_36, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 5.63/5.78  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.63/5.78  cnf(c_0_38, negated_conjecture, (r1_ordinal1(X1,esk7_0)|r1_ordinal1(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 5.63/5.78  cnf(c_0_39, negated_conjecture, (~r1_ordinal1(k2_xboole_0(esk7_0,k1_tarski(esk7_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 5.63/5.78  fof(c_0_40, plain, ![X27]:((~v4_ordinal1(X27)|X27=k3_tarski(X27))&(X27!=k3_tarski(X27)|v4_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 5.63/5.78  fof(c_0_41, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 5.63/5.78  fof(c_0_42, plain, ![X35, X36]:(~v3_ordinal1(X36)|(~r2_hidden(X35,X36)|v3_ordinal1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 5.63/5.78  fof(c_0_43, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 5.63/5.78  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r1_ordinal1(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 5.63/5.78  cnf(c_0_45, negated_conjecture, (r1_ordinal1(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_39])).
% 5.63/5.78  cnf(c_0_46, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.63/5.78  cnf(c_0_47, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.63/5.78  cnf(c_0_48, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.63/5.78  cnf(c_0_49, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.63/5.78  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.63/5.78  cnf(c_0_51, negated_conjecture, (r1_tarski(esk7_0,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_28]), c_0_45])])).
% 5.63/5.78  cnf(c_0_52, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.63/5.78  cnf(c_0_53, plain, (v4_ordinal1(X1)|r2_hidden(esk4_2(X1,X1),X1)|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47])])).
% 5.63/5.78  cnf(c_0_54, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_48, c_0_21])).
% 5.63/5.78  cnf(c_0_55, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(spm,[status(thm)],[c_0_49, c_0_35])).
% 5.63/5.78  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 5.63/5.78  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk4_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 5.63/5.78  cnf(c_0_58, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_28])).
% 5.63/5.78  cnf(c_0_59, negated_conjecture, (r1_ordinal1(X1,esk7_0)|~r2_hidden(X1,k2_xboole_0(esk7_0,k1_tarski(esk7_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_28]), c_0_55])).
% 5.63/5.78  cnf(c_0_60, negated_conjecture, (r2_hidden(esk4_2(esk7_0,esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 5.63/5.78  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_ordinal1(X1,esk7_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_28])).
% 5.63/5.78  cnf(c_0_62, negated_conjecture, (v3_ordinal1(esk4_2(esk7_0,esk7_0))|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 5.63/5.78  cnf(c_0_63, negated_conjecture, (r1_ordinal1(esk4_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 5.63/5.78  cnf(c_0_64, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.63/5.78  cnf(c_0_65, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k1_ordinal1(X1),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.63/5.78  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)|r1_tarski(esk4_2(esk7_0,esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 5.63/5.78  cnf(c_0_67, plain, (v4_ordinal1(X1)|r2_hidden(esk3_2(X1,X1),esk4_2(X1,X1))|r2_hidden(esk3_2(X1,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_64])])).
% 5.63/5.78  cnf(c_0_68, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_65, c_0_21])).
% 5.63/5.78  cnf(c_0_69, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)|r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk4_2(esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_66])).
% 5.63/5.78  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk4_2(esk7_0,esk7_0))|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_67])).
% 5.63/5.78  cnf(c_0_71, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(csr,[status(thm)],[c_0_68, c_0_58])).
% 5.63/5.78  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 5.63/5.78  fof(c_0_73, plain, ![X34]:r2_hidden(X34,k1_ordinal1(X34)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 5.63/5.78  cnf(c_0_74, plain, (X2=k3_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(esk3_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.63/5.78  cnf(c_0_75, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_52])).
% 5.63/5.78  cnf(c_0_76, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 5.63/5.78  cnf(c_0_77, negated_conjecture, (X1=k3_tarski(esk7_0)|r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk3_2(esk7_0,X1),k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))))|~r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 5.63/5.78  cnf(c_0_78, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_76, c_0_21])).
% 5.63/5.78  cnf(c_0_79, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_72]), c_0_78])])).
% 5.63/5.78  cnf(c_0_80, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_79]), c_0_52])).
% 5.63/5.78  cnf(c_0_81, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.63/5.78  cnf(c_0_82, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.63/5.78  cnf(c_0_83, negated_conjecture, (v4_ordinal1(esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_71, c_0_80])).
% 5.63/5.78  fof(c_0_84, plain, ![X40, X41]:((~r2_hidden(X40,X41)|r1_ordinal1(k1_ordinal1(X40),X41)|~v3_ordinal1(X41)|~v3_ordinal1(X40))&(~r1_ordinal1(k1_ordinal1(X40),X41)|r2_hidden(X40,X41)|~v3_ordinal1(X41)|~v3_ordinal1(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 5.63/5.78  cnf(c_0_85, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_81])).
% 5.63/5.78  cnf(c_0_86, negated_conjecture, (k3_tarski(esk7_0)=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 5.63/5.78  cnf(c_0_87, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.63/5.78  cnf(c_0_88, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 5.63/5.78  cnf(c_0_89, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.63/5.78  cnf(c_0_90, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(esk2_3(esk7_0,esk7_0,X1),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 5.63/5.78  cnf(c_0_91, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_87])).
% 5.63/5.78  cnf(c_0_92, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_88, c_0_21])).
% 5.63/5.78  cnf(c_0_93, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_89])).
% 5.63/5.78  cnf(c_0_94, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_80])).
% 5.63/5.78  cnf(c_0_95, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r2_hidden(X1,esk2_3(esk7_0,esk7_0,X1))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_91, c_0_86])).
% 5.63/5.78  cnf(c_0_96, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_92, c_0_49])).
% 5.63/5.78  cnf(c_0_97, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 5.63/5.78  cnf(c_0_98, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_95, c_0_80])).
% 5.63/5.78  fof(c_0_99, plain, ![X37, X38]:(~v3_ordinal1(X37)|(~v3_ordinal1(X38)|(r2_hidden(X37,X38)|X37=X38|r2_hidden(X38,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 5.63/5.78  cnf(c_0_100, negated_conjecture, (v3_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_58, c_0_80])).
% 5.63/5.78  cnf(c_0_101, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_96, c_0_28])).
% 5.63/5.78  cnf(c_0_102, negated_conjecture, (r2_hidden(esk2_3(esk7_0,esk7_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_97, c_0_78])).
% 5.63/5.78  cnf(c_0_103, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_93, c_0_98])).
% 5.63/5.78  cnf(c_0_104, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 5.63/5.78  cnf(c_0_105, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_29, c_0_100])).
% 5.63/5.78  cnf(c_0_106, negated_conjecture, (r1_ordinal1(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_101, c_0_80])).
% 5.63/5.78  cnf(c_0_107, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))|r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,esk2_3(esk7_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_93, c_0_102])).
% 5.63/5.78  cnf(c_0_108, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,esk7_0,esk8_0))|r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_103, c_0_78])).
% 5.63/5.78  cnf(c_0_109, negated_conjecture, (X1=esk7_0|r2_hidden(X1,esk7_0)|r2_hidden(esk7_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_104, c_0_28])).
% 5.63/5.78  cnf(c_0_110, negated_conjecture, (r1_tarski(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_105]), c_0_106])])).
% 5.63/5.78  cnf(c_0_111, negated_conjecture, (r2_hidden(esk8_0,k3_tarski(esk7_0))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 5.63/5.78  cnf(c_0_112, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_49, c_0_105])).
% 5.63/5.78  cnf(c_0_113, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=esk7_0|r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_109, c_0_105])).
% 5.63/5.78  cnf(c_0_114, negated_conjecture, (~r2_hidden(esk7_0,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(spm,[status(thm)],[c_0_30, c_0_110])).
% 5.63/5.78  cnf(c_0_115, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_85, c_0_111])).
% 5.63/5.78  cnf(c_0_116, negated_conjecture, (r1_ordinal1(X1,esk8_0)|~r2_hidden(X1,k2_xboole_0(esk8_0,k1_tarski(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_100]), c_0_112])).
% 5.63/5.78  cnf(c_0_117, negated_conjecture, (k2_xboole_0(esk8_0,k1_tarski(esk8_0))=esk7_0|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(sr,[status(thm)],[c_0_113, c_0_114])).
% 5.63/5.78  cnf(c_0_118, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_100])).
% 5.63/5.78  cnf(c_0_119, negated_conjecture, (v3_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_58, c_0_115])).
% 5.63/5.78  cnf(c_0_120, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 5.63/5.78  cnf(c_0_121, negated_conjecture, (~r2_hidden(k1_ordinal1(esk8_0),esk7_0)|~v4_ordinal1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.63/5.78  cnf(c_0_122, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|~r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 5.63/5.78  cnf(c_0_123, negated_conjecture, (r1_ordinal1(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)|r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_120, c_0_115])).
% 5.63/5.78  cnf(c_0_124, negated_conjecture, (~v4_ordinal1(esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(rw,[status(thm)],[c_0_121, c_0_21])).
% 5.63/5.78  cnf(c_0_125, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)|r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 5.63/5.78  cnf(c_0_126, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_91, c_0_111])).
% 5.63/5.78  cnf(c_0_127, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk4_2(esk7_0,esk7_0),esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_124, c_0_53])).
% 5.63/5.78  cnf(c_0_128, negated_conjecture, (r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_125]), c_0_126])])).
% 5.63/5.78  cnf(c_0_129, negated_conjecture, (r2_hidden(esk4_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128])])).
% 5.63/5.78  cnf(c_0_130, negated_conjecture, (r2_hidden(esk4_2(esk7_0,esk7_0),k2_xboole_0(esk7_0,k1_tarski(esk7_0)))|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_129])).
% 5.63/5.78  cnf(c_0_131, negated_conjecture, (v3_ordinal1(esk4_2(esk7_0,esk7_0))|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_129])).
% 5.63/5.78  cnf(c_0_132, negated_conjecture, (r1_ordinal1(esk4_2(esk7_0,esk7_0),esk7_0)|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_130])).
% 5.63/5.78  cnf(c_0_133, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r1_tarski(esk4_2(esk7_0,esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_131]), c_0_132])).
% 5.63/5.78  cnf(c_0_134, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk4_2(esk7_0,esk7_0))|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|~r2_hidden(k2_xboole_0(esk8_0,k1_tarski(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_124, c_0_67])).
% 5.63/5.78  cnf(c_0_135, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)|r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk4_2(esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_50, c_0_133])).
% 5.63/5.78  cnf(c_0_136, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk4_2(esk7_0,esk7_0))|r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_128])])).
% 5.63/5.78  cnf(c_0_137, negated_conjecture, (r2_hidden(esk3_2(esk7_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 5.63/5.78  cnf(c_0_138, negated_conjecture, (~v4_ordinal1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_128])])).
% 5.63/5.78  cnf(c_0_139, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_137]), c_0_138])).
% 5.63/5.78  cnf(c_0_140, negated_conjecture, (X1=k3_tarski(esk7_0)|~r2_hidden(esk3_2(esk7_0,X1),k2_xboole_0(esk3_2(esk7_0,esk7_0),k1_tarski(esk3_2(esk7_0,esk7_0))))|~r2_hidden(esk3_2(esk7_0,X1),X1)), inference(spm,[status(thm)],[c_0_74, c_0_139])).
% 5.63/5.78  cnf(c_0_141, negated_conjecture, (k3_tarski(esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_137]), c_0_78])])).
% 5.63/5.78  cnf(c_0_142, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_141]), c_0_138]), ['proof']).
% 5.63/5.78  # SZS output end CNFRefutation
% 5.63/5.78  # Proof object total steps             : 143
% 5.63/5.78  # Proof object clause steps            : 112
% 5.63/5.78  # Proof object formula steps           : 31
% 5.63/5.78  # Proof object conjectures             : 81
% 5.63/5.78  # Proof object clause conjectures      : 78
% 5.63/5.78  # Proof object formula conjectures     : 3
% 5.63/5.78  # Proof object initial clauses used    : 25
% 5.63/5.78  # Proof object initial formulas used   : 15
% 5.63/5.78  # Proof object generating inferences   : 70
% 5.63/5.78  # Proof object simplifying inferences  : 42
% 5.63/5.78  # Training examples: 0 positive, 0 negative
% 5.63/5.78  # Parsed axioms                        : 17
% 5.63/5.78  # Removed by relevancy pruning/SinE    : 0
% 5.63/5.78  # Initial clauses                      : 38
% 5.63/5.78  # Removed in clause preprocessing      : 1
% 5.63/5.78  # Initial clauses in saturation        : 37
% 5.63/5.78  # Processed clauses                    : 10605
% 5.63/5.78  # ...of these trivial                  : 399
% 5.63/5.78  # ...subsumed                          : 4168
% 5.63/5.78  # ...remaining for further processing  : 6038
% 5.63/5.78  # Other redundant clauses eliminated   : 23
% 5.63/5.78  # Clauses deleted for lack of memory   : 0
% 5.63/5.78  # Backward-subsumed                    : 282
% 5.63/5.78  # Backward-rewritten                   : 1564
% 5.63/5.78  # Generated clauses                    : 636852
% 5.63/5.78  # ...of the previous two non-trivial   : 571651
% 5.63/5.78  # Contextual simplify-reflections      : 51
% 5.63/5.78  # Paramodulations                      : 636803
% 5.63/5.78  # Factorizations                       : 2
% 5.63/5.78  # Equation resolutions                 : 23
% 5.63/5.78  # Propositional unsat checks           : 0
% 5.63/5.78  #    Propositional check models        : 0
% 5.63/5.78  #    Propositional check unsatisfiable : 0
% 5.63/5.78  #    Propositional clauses             : 0
% 5.63/5.78  #    Propositional clauses after purity: 0
% 5.63/5.78  #    Propositional unsat core size     : 0
% 5.63/5.78  #    Propositional preprocessing time  : 0.000
% 5.63/5.78  #    Propositional encoding time       : 0.000
% 5.63/5.78  #    Propositional solver time         : 0.000
% 5.63/5.78  #    Success case prop preproc time    : 0.000
% 5.63/5.78  #    Success case prop encoding time   : 0.000
% 5.63/5.78  #    Success case prop solver time     : 0.000
% 5.63/5.78  # Current number of processed clauses  : 4127
% 5.63/5.78  #    Positive orientable unit clauses  : 1080
% 5.63/5.78  #    Positive unorientable unit clauses: 0
% 5.63/5.78  #    Negative unit clauses             : 189
% 5.63/5.78  #    Non-unit-clauses                  : 2858
% 5.63/5.78  # Current number of unprocessed clauses: 558671
% 5.63/5.78  # ...number of literals in the above   : 2614108
% 5.63/5.78  # Current number of archived formulas  : 0
% 5.63/5.78  # Current number of archived clauses   : 1907
% 5.63/5.78  # Clause-clause subsumption calls (NU) : 1404686
% 5.63/5.78  # Rec. Clause-clause subsumption calls : 850130
% 5.63/5.78  # Non-unit clause-clause subsumptions  : 2792
% 5.63/5.78  # Unit Clause-clause subsumption calls : 389067
% 5.63/5.78  # Rewrite failures with RHS unbound    : 0
% 5.63/5.78  # BW rewrite match attempts            : 11126
% 5.63/5.78  # BW rewrite match successes           : 89
% 5.63/5.78  # Condensation attempts                : 0
% 5.63/5.78  # Condensation successes               : 0
% 5.63/5.78  # Termbank termtop insertions          : 15379694
% 5.65/5.80  
% 5.65/5.80  # -------------------------------------------------
% 5.65/5.80  # User time                : 5.214 s
% 5.65/5.80  # System time              : 0.241 s
% 5.65/5.80  # Total time               : 5.455 s
% 5.65/5.80  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
