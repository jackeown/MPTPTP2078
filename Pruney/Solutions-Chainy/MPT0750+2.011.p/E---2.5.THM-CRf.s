%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:33 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  190 (18774 expanded)
%              Number of clauses        :  155 (8674 expanded)
%              Number of leaves         :   17 (4764 expanded)
%              Depth                    :   26
%              Number of atoms          :  520 (71536 expanded)
%              Number of equality atoms :   74 (7454 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v3_ordinal1(X2)
      & ~ r2_hidden(X2,X1)
      & ! [X3] :
          ( v3_ordinal1(X3)
         => ( ~ r2_hidden(X3,X1)
           => r1_ordinal1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_ordinal1)).

fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,X1)
        & v3_ordinal1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

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

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

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

fof(t35_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(c_0_17,plain,(
    ! [X46,X48] :
      ( v3_ordinal1(esk8_1(X46))
      & ~ r2_hidden(esk8_1(X46),X46)
      & ( ~ v3_ordinal1(X48)
        | r2_hidden(X48,X46)
        | r1_ordinal1(esk8_1(X46),X48) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).

fof(c_0_18,plain,(
    ! [X28,X30,X31] :
      ( ( r2_hidden(X30,X28)
        | ~ r2_hidden(X30,esk5_1(X28)) )
      & ( v3_ordinal1(X30)
        | ~ r2_hidden(X30,esk5_1(X28)) )
      & ( ~ r2_hidden(X31,X28)
        | ~ v3_ordinal1(X31)
        | r2_hidden(X31,esk5_1(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ( ~ r2_hidden(X40,k1_ordinal1(X41))
        | r1_ordinal1(X40,X41)
        | ~ v3_ordinal1(X41)
        | ~ v3_ordinal1(X40) )
      & ( ~ r1_ordinal1(X40,X41)
        | r2_hidden(X40,k1_ordinal1(X41))
        | ~ v3_ordinal1(X41)
        | ~ v3_ordinal1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

fof(c_0_20,plain,(
    ! [X24] : k1_ordinal1(X24) = k2_xboole_0(X24,k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,esk5_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v3_ordinal1(esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,(
    ! [X53] :
      ( v3_ordinal1(esk9_0)
      & ( v3_ordinal1(esk10_0)
        | ~ v4_ordinal1(esk9_0) )
      & ( r2_hidden(esk10_0,esk9_0)
        | ~ v4_ordinal1(esk9_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk10_0),esk9_0)
        | ~ v4_ordinal1(esk9_0) )
      & ( v4_ordinal1(esk9_0)
        | ~ v3_ordinal1(X53)
        | ~ r2_hidden(X53,esk9_0)
        | r2_hidden(k1_ordinal1(X53),esk9_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])])).

fof(c_0_28,plain,(
    ! [X33,X34] :
      ( ( ~ r2_hidden(X33,k1_ordinal1(X34))
        | r2_hidden(X33,X34)
        | X33 = X34 )
      & ( ~ r2_hidden(X33,X34)
        | r2_hidden(X33,k1_ordinal1(X34)) )
      & ( X33 != X34
        | r2_hidden(X33,k1_ordinal1(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

fof(c_0_29,plain,(
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

cnf(c_0_30,plain,
    ( ~ r2_hidden(esk8_1(esk5_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | r1_ordinal1(esk8_1(X2),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( v3_ordinal1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X35,X36] :
      ( ~ v3_ordinal1(X36)
      | ~ r2_hidden(X35,X36)
      | v3_ordinal1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( ~ r1_ordinal1(esk8_1(esk5_1(k2_xboole_0(X1,k1_tarski(X1)))),X1)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])])).

cnf(c_0_39,negated_conjecture,
    ( r1_ordinal1(esk8_1(X1),esk9_0)
    | r2_hidden(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X42] :
      ( ( r2_hidden(esk6_1(X42),X42)
        | v3_ordinal1(k3_tarski(X42)) )
      & ( ~ v3_ordinal1(esk6_1(X42))
        | v3_ordinal1(k3_tarski(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ( ~ r1_ordinal1(X26,X27)
        | r1_tarski(X26,X27)
        | ~ v3_ordinal1(X26)
        | ~ v3_ordinal1(X27) )
      & ( ~ r1_tarski(X26,X27)
        | r1_ordinal1(X26,X27)
        | ~ v3_ordinal1(X26)
        | ~ v3_ordinal1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_42,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_44,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33])])).

cnf(c_0_47,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk5_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ r1_tarski(X50,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk5_1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)))))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( v3_ordinal1(k3_tarski(esk5_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_44])).

cnf(c_0_57,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_58,plain,(
    ! [X37,X38] :
      ( ~ v3_ordinal1(X37)
      | ~ v3_ordinal1(X38)
      | r2_hidden(X37,X38)
      | X37 = X38
      | r2_hidden(X38,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_59,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_53]),c_0_54])])).

cnf(c_0_60,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk6_1(X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_59])).

cnf(c_0_65,plain,
    ( ~ v3_ordinal1(esk2_3(X1,k3_tarski(X1),X2))
    | ~ r2_hidden(X1,esk2_3(X1,k3_tarski(X1),X2))
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( v4_ordinal1(esk9_0)
    | r2_hidden(k1_ordinal1(X1),esk9_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(X1,esk9_0)
    | r2_hidden(esk9_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_48])).

fof(c_0_70,plain,(
    ! [X25] :
      ( ( ~ v4_ordinal1(X25)
        | X25 = k3_tarski(X25) )
      & ( X25 != k3_tarski(X25)
        | v4_ordinal1(X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_71,plain,
    ( ~ v3_ordinal1(esk2_3(X1,k3_tarski(X1),X1))
    | ~ r2_hidden(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_72,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_73,negated_conjecture,
    ( v4_ordinal1(esk9_0)
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk9_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( k3_tarski(esk9_0) = esk9_0
    | r2_hidden(esk9_0,k3_tarski(esk9_0))
    | r2_hidden(k3_tarski(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk2_3(X1,k3_tarski(X1),X1),esk9_0)
    | ~ r2_hidden(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_59])).

fof(c_0_77,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_78,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(esk9_0) = esk9_0
    | r2_hidden(k2_xboole_0(k3_tarski(esk9_0),k1_tarski(k3_tarski(esk9_0))),esk9_0)
    | r2_hidden(esk9_0,k3_tarski(esk9_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_69])]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k3_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_61])).

fof(c_0_81,plain,(
    ! [X32] : r2_hidden(X32,k1_ordinal1(X32)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk2_3(X2,k3_tarski(X2),X1),X1)
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_66])).

cnf(c_0_84,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X3)
    | ~ r2_hidden(X2,k3_tarski(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_61])).

fof(c_0_85,plain,(
    ! [X39] :
      ( ~ v3_ordinal1(X39)
      | v3_ordinal1(k1_ordinal1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_86,negated_conjecture,
    ( k3_tarski(esk9_0) = esk9_0
    | r2_hidden(k2_xboole_0(k3_tarski(esk9_0),k1_tarski(k3_tarski(esk9_0))),esk9_0) ),
    inference(sr,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_89,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k3_tarski(esk2_3(X2,k3_tarski(X2),X3)))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_66])).

cnf(c_0_91,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( v3_ordinal1(esk10_0)
    | ~ v4_ordinal1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_93,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_94,negated_conjecture,
    ( k3_tarski(esk9_0) = esk9_0
    | r2_hidden(X1,k3_tarski(esk9_0))
    | ~ r2_hidden(X1,k2_xboole_0(k3_tarski(esk9_0),k1_tarski(k3_tarski(esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_86])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_87,c_0_26])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_88])).

cnf(c_0_97,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,k3_tarski(X3))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk2_3(X3,k3_tarski(X3),X2),X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | r1_tarski(esk8_1(X1),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_39]),c_0_33]),c_0_24])])).

cnf(c_0_99,negated_conjecture,
    ( esk8_1(X1) = esk9_0
    | r2_hidden(esk9_0,esk8_1(X1))
    | r2_hidden(esk8_1(X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_24])).

cnf(c_0_100,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_91,c_0_26])).

cnf(c_0_101,negated_conjecture,
    ( v3_ordinal1(esk10_0)
    | k3_tarski(esk9_0) != esk9_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_102,negated_conjecture,
    ( k3_tarski(esk9_0) = esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])).

cnf(c_0_103,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk2_3(X2,k3_tarski(X2),X3),X1)
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_97,c_0_56])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk5_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | ~ r2_hidden(esk9_0,esk8_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( esk8_1(esk9_0) = esk9_0
    | r2_hidden(esk9_0,esk8_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk10_0),esk9_0)
    | ~ v4_ordinal1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_108,negated_conjecture,
    ( k2_xboole_0(X1,k1_tarski(X1)) = esk9_0
    | r2_hidden(esk9_0,k2_xboole_0(X1,k1_tarski(X1)))
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( v3_ordinal1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk10_0,esk9_0)
    | ~ v4_ordinal1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_111,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,k3_tarski(X1))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_61])).

cnf(c_0_112,plain,
    ( r2_hidden(esk2_3(esk5_1(X1),k3_tarski(esk5_1(X1)),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(esk5_1(X1))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_61])).

cnf(c_0_113,negated_conjecture,
    ( esk8_1(esk9_0) = esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_96])).

cnf(c_0_114,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_115,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_116,negated_conjecture,
    ( ~ v4_ordinal1(esk9_0)
    | ~ r2_hidden(k2_xboole_0(esk10_0,k1_tarski(esk10_0)),esk9_0) ),
    inference(rw,[status(thm)],[c_0_107,c_0_26])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(esk10_0,k1_tarski(esk10_0)) = esk9_0
    | r2_hidden(k2_xboole_0(esk10_0,k1_tarski(esk10_0)),esk9_0)
    | r2_hidden(esk9_0,k2_xboole_0(esk10_0,k1_tarski(esk10_0))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(esk10_0,esk9_0)
    | k3_tarski(esk9_0) != esk9_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_93])).

cnf(c_0_119,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_120,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_121,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r1_tarski(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_84])).

cnf(c_0_122,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,k3_tarski(esk5_1(X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_112])).

cnf(c_0_123,negated_conjecture,
    ( r1_ordinal1(esk9_0,X1)
    | r2_hidden(X1,esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_113])).

cnf(c_0_124,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_66])).

cnf(c_0_125,plain,
    ( r1_tarski(X1,esk5_1(X2))
    | ~ v3_ordinal1(esk1_2(X1,esk5_1(X2)))
    | ~ r2_hidden(esk1_2(X1,esk5_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_114,c_0_23])).

cnf(c_0_126,plain,
    ( v3_ordinal1(esk1_2(X1,X2))
    | r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_115])).

cnf(c_0_127,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_128,negated_conjecture,
    ( k2_xboole_0(esk10_0,k1_tarski(esk10_0)) = esk9_0
    | r2_hidden(esk9_0,k2_xboole_0(esk10_0,k1_tarski(esk10_0)))
    | ~ v4_ordinal1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk10_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_102])])).

cnf(c_0_130,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk4_2(X2,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_120])).

cnf(c_0_131,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ r1_tarski(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_66])).

cnf(c_0_132,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_48]),c_0_49])).

cnf(c_0_133,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r1_tarski(X2,k3_tarski(esk5_1(X1))) ),
    inference(spm,[status(thm)],[c_0_122,c_0_84])).

cnf(c_0_134,negated_conjecture,
    ( r1_ordinal1(esk9_0,k3_tarski(esk5_1(X1)))
    | r2_hidden(k3_tarski(esk5_1(X1)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_54])).

cnf(c_0_135,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(esk2_3(X2,k3_tarski(X2),X1),esk9_0)
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_59])).

cnf(c_0_136,plain,
    ( r1_tarski(X1,esk5_1(X1))
    | ~ v3_ordinal1(esk1_2(X1,esk5_1(X1))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_115])).

cnf(c_0_137,plain,
    ( v3_ordinal1(esk1_2(esk5_1(X1),X2))
    | r1_tarski(esk5_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_115])).

cnf(c_0_138,plain,
    ( r2_hidden(esk1_2(esk5_1(X1),X2),X1)
    | r1_tarski(esk5_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_104,c_0_115])).

cnf(c_0_139,negated_conjecture,
    ( v3_ordinal1(esk1_2(esk10_0,X1))
    | r1_tarski(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_109])).

cnf(c_0_140,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_127,c_0_26])).

cnf(c_0_141,negated_conjecture,
    ( k2_xboole_0(esk10_0,k1_tarski(esk10_0)) = esk9_0
    | r2_hidden(esk9_0,k2_xboole_0(esk10_0,k1_tarski(esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_93]),c_0_102])])).

cnf(c_0_142,negated_conjecture,
    ( ~ r2_hidden(esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_129]),c_0_109])])).

cnf(c_0_143,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(esk4_2(esk9_0,esk10_0),esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_129]),c_0_102])).

cnf(c_0_144,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_56]),c_0_132])).

cnf(c_0_145,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ r1_tarski(X2,k3_tarski(esk5_1(X1))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_66])).

cnf(c_0_146,negated_conjecture,
    ( r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)
    | r1_tarski(esk9_0,k3_tarski(esk5_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_134]),c_0_54]),c_0_33])])).

cnf(c_0_147,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_61])).

cnf(c_0_148,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_149,plain,
    ( r1_tarski(esk5_1(X1),esk5_1(esk5_1(X1))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_150,plain,
    ( r1_tarski(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_138])).

cnf(c_0_151,plain,
    ( v3_ordinal1(esk1_2(k3_tarski(esk5_1(X1)),X2))
    | r1_tarski(k3_tarski(esk5_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_126,c_0_54])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(esk10_0,esk5_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_139])).

cnf(c_0_153,negated_conjecture,
    ( k2_xboole_0(esk10_0,k1_tarski(esk10_0)) = esk9_0
    | esk10_0 = esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_142])).

cnf(c_0_154,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk4_2(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_143]),c_0_102])).

cnf(c_0_155,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_156,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_129]),c_0_102])).

cnf(c_0_157,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk2_3(X2,k3_tarski(X2),X3),k3_tarski(X1))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_144,c_0_90])).

cnf(c_0_158,negated_conjecture,
    ( r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)
    | ~ r2_hidden(X1,k3_tarski(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_147])).

cnf(c_0_159,plain,
    ( esk5_1(esk5_1(X1)) = esk5_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_150])])).

cnf(c_0_160,plain,
    ( r1_tarski(k3_tarski(esk5_1(X1)),esk5_1(k3_tarski(esk5_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_151])).

cnf(c_0_161,negated_conjecture,
    ( esk5_1(esk10_0) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_152]),c_0_150])])).

cnf(c_0_162,negated_conjecture,
    ( esk10_0 = esk9_0
    | X1 = esk10_0
    | r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_153])).

cnf(c_0_163,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(esk3_2(esk9_0,esk10_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_102])]),c_0_156])).

cnf(c_0_164,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,k3_tarski(k3_tarski(X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_157,c_0_61])).

cnf(c_0_165,negated_conjecture,
    ( r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)
    | ~ r2_hidden(esk5_1(X1),k3_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_166,plain,
    ( esk5_1(k3_tarski(esk5_1(X1))) = k3_tarski(esk5_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_160]),c_0_150])])).

cnf(c_0_167,negated_conjecture,
    ( r2_hidden(k3_tarski(esk10_0),esk9_0)
    | r1_tarski(esk9_0,k3_tarski(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_161])).

cnf(c_0_168,plain,
    ( v3_ordinal1(esk2_3(esk5_1(X1),k3_tarski(esk5_1(X1)),X2))
    | ~ r2_hidden(X2,k3_tarski(esk5_1(X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_61])).

cnf(c_0_169,negated_conjecture,
    ( esk3_2(esk9_0,esk10_0) = esk10_0
    | esk10_0 = esk9_0
    | r2_hidden(esk3_2(esk9_0,esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_170,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X3))
    | ~ r2_hidden(X3,k3_tarski(X2))
    | ~ r1_tarski(X2,k3_tarski(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_84])).

cnf(c_0_171,negated_conjecture,
    ( r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)
    | ~ r2_hidden(esk5_1(X1),esk9_0) ),
    inference(rw,[status(thm)],[c_0_165,c_0_102])).

cnf(c_0_172,negated_conjecture,
    ( esk5_1(k3_tarski(esk10_0)) = k3_tarski(esk10_0) ),
    inference(spm,[status(thm)],[c_0_166,c_0_161])).

cnf(c_0_173,negated_conjecture,
    ( r2_hidden(k3_tarski(esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_167]),c_0_109]),c_0_102]),c_0_129])])).

cnf(c_0_174,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(esk5_1(X2))) ),
    inference(spm,[status(thm)],[c_0_124,c_0_168])).

cnf(c_0_175,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ v3_ordinal1(esk3_2(X2,X1))
    | ~ r2_hidden(esk4_2(X2,X1),esk3_2(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_155])).

cnf(c_0_176,negated_conjecture,
    ( esk3_2(esk9_0,esk10_0) = esk10_0
    | esk10_0 = esk9_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_169]),c_0_102]),c_0_129])]),c_0_169])).

cnf(c_0_177,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ r1_tarski(X2,k3_tarski(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_170,c_0_66])).

cnf(c_0_178,negated_conjecture,
    ( r2_hidden(k3_tarski(k3_tarski(esk10_0)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_173])])).

cnf(c_0_179,plain,
    ( v3_ordinal1(k3_tarski(k3_tarski(esk5_1(X1)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_48]),c_0_49])).

cnf(c_0_180,negated_conjecture,
    ( esk10_0 = esk9_0
    | ~ r2_hidden(esk4_2(esk9_0,esk10_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_176]),c_0_102]),c_0_109])]),c_0_96])).

cnf(c_0_181,negated_conjecture,
    ( esk4_2(esk9_0,esk10_0) = esk10_0
    | esk10_0 = esk9_0
    | r2_hidden(esk4_2(esk9_0,esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_143])).

cnf(c_0_182,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_177,c_0_88])).

cnf(c_0_183,negated_conjecture,
    ( r2_hidden(k3_tarski(k3_tarski(esk10_0)),X1)
    | ~ r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_178])).

cnf(c_0_184,negated_conjecture,
    ( v3_ordinal1(k3_tarski(k3_tarski(esk10_0))) ),
    inference(spm,[status(thm)],[c_0_179,c_0_161])).

cnf(c_0_185,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(esk10_0,esk4_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_176]),c_0_102])]),c_0_96])).

cnf(c_0_186,negated_conjecture,
    ( esk4_2(esk9_0,esk10_0) = esk10_0
    | esk10_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_180,c_0_181])).

cnf(c_0_187,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(esk10_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_183]),c_0_184])])).

cnf(c_0_188,negated_conjecture,
    ( esk10_0 = esk9_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_186]),c_0_96])).

cnf(c_0_189,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_188]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.17/1.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 1.17/1.34  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.17/1.34  #
% 1.17/1.34  # Preprocessing time       : 0.028 s
% 1.17/1.34  # Presaturation interreduction done
% 1.17/1.34  
% 1.17/1.34  # Proof found!
% 1.17/1.34  # SZS status Theorem
% 1.17/1.34  # SZS output start CNFRefutation
% 1.17/1.34  fof(t39_ordinal1, axiom, ![X1]:?[X2]:((v3_ordinal1(X2)&~(r2_hidden(X2,X1)))&![X3]:(v3_ordinal1(X3)=>(~(r2_hidden(X3,X1))=>r1_ordinal1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_ordinal1)).
% 1.17/1.34  fof(s1_xboole_0__e3_53__ordinal1, axiom, ![X1]:?[X2]:![X3]:(r2_hidden(X3,X2)<=>(r2_hidden(X3,X1)&v3_ordinal1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 1.17/1.34  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 1.17/1.34  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.17/1.34  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 1.17/1.34  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 1.17/1.34  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 1.17/1.34  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 1.17/1.34  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_ordinal1)).
% 1.17/1.34  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.17/1.34  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.17/1.34  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 1.17/1.34  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 1.17/1.34  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.17/1.34  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.17/1.34  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.17/1.34  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 1.17/1.34  fof(c_0_17, plain, ![X46, X48]:((v3_ordinal1(esk8_1(X46))&~r2_hidden(esk8_1(X46),X46))&(~v3_ordinal1(X48)|(r2_hidden(X48,X46)|r1_ordinal1(esk8_1(X46),X48)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).
% 1.17/1.34  fof(c_0_18, plain, ![X28, X30, X31]:(((r2_hidden(X30,X28)|~r2_hidden(X30,esk5_1(X28)))&(v3_ordinal1(X30)|~r2_hidden(X30,esk5_1(X28))))&(~r2_hidden(X31,X28)|~v3_ordinal1(X31)|r2_hidden(X31,esk5_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).
% 1.17/1.34  fof(c_0_19, plain, ![X40, X41]:((~r2_hidden(X40,k1_ordinal1(X41))|r1_ordinal1(X40,X41)|~v3_ordinal1(X41)|~v3_ordinal1(X40))&(~r1_ordinal1(X40,X41)|r2_hidden(X40,k1_ordinal1(X41))|~v3_ordinal1(X41)|~v3_ordinal1(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 1.17/1.34  fof(c_0_20, plain, ![X24]:k1_ordinal1(X24)=k2_xboole_0(X24,k1_tarski(X24)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 1.17/1.34  fof(c_0_21, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 1.17/1.34  cnf(c_0_22, plain, (~r2_hidden(esk8_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.17/1.34  cnf(c_0_23, plain, (r2_hidden(X1,esk5_1(X2))|~r2_hidden(X1,X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.17/1.34  cnf(c_0_24, plain, (v3_ordinal1(esk8_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.17/1.34  cnf(c_0_25, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.17/1.34  cnf(c_0_26, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.17/1.34  fof(c_0_27, negated_conjecture, ![X53]:(v3_ordinal1(esk9_0)&(((v3_ordinal1(esk10_0)|~v4_ordinal1(esk9_0))&((r2_hidden(esk10_0,esk9_0)|~v4_ordinal1(esk9_0))&(~r2_hidden(k1_ordinal1(esk10_0),esk9_0)|~v4_ordinal1(esk9_0))))&(v4_ordinal1(esk9_0)|(~v3_ordinal1(X53)|(~r2_hidden(X53,esk9_0)|r2_hidden(k1_ordinal1(X53),esk9_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])])).
% 1.17/1.34  fof(c_0_28, plain, ![X33, X34]:((~r2_hidden(X33,k1_ordinal1(X34))|(r2_hidden(X33,X34)|X33=X34))&((~r2_hidden(X33,X34)|r2_hidden(X33,k1_ordinal1(X34)))&(X33!=X34|r2_hidden(X33,k1_ordinal1(X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 1.17/1.34  fof(c_0_29, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 1.17/1.34  cnf(c_0_30, plain, (~r2_hidden(esk8_1(esk5_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 1.17/1.34  cnf(c_0_31, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 1.17/1.34  cnf(c_0_32, plain, (r2_hidden(X1,X2)|r1_ordinal1(esk8_1(X2),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.17/1.34  cnf(c_0_33, negated_conjecture, (v3_ordinal1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.17/1.34  cnf(c_0_34, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.17/1.34  cnf(c_0_35, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.17/1.34  fof(c_0_36, plain, ![X35, X36]:(~v3_ordinal1(X36)|(~r2_hidden(X35,X36)|v3_ordinal1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 1.17/1.34  cnf(c_0_37, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.17/1.34  cnf(c_0_38, plain, (~r1_ordinal1(esk8_1(esk5_1(k2_xboole_0(X1,k1_tarski(X1)))),X1)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])])).
% 1.17/1.34  cnf(c_0_39, negated_conjecture, (r1_ordinal1(esk8_1(X1),esk9_0)|r2_hidden(esk9_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.17/1.34  fof(c_0_40, plain, ![X42]:((r2_hidden(esk6_1(X42),X42)|v3_ordinal1(k3_tarski(X42)))&(~v3_ordinal1(esk6_1(X42))|v3_ordinal1(k3_tarski(X42)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 1.17/1.34  fof(c_0_41, plain, ![X26, X27]:((~r1_ordinal1(X26,X27)|r1_tarski(X26,X27)|(~v3_ordinal1(X26)|~v3_ordinal1(X27)))&(~r1_tarski(X26,X27)|r1_ordinal1(X26,X27)|(~v3_ordinal1(X26)|~v3_ordinal1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 1.17/1.34  cnf(c_0_42, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_34, c_0_26])).
% 1.17/1.34  cnf(c_0_43, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_26])).
% 1.17/1.34  cnf(c_0_44, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.17/1.34  cnf(c_0_45, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_37])).
% 1.17/1.34  cnf(c_0_46, negated_conjecture, (r2_hidden(esk9_0,esk5_1(k2_xboole_0(esk9_0,k1_tarski(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33])])).
% 1.17/1.34  cnf(c_0_47, plain, (v3_ordinal1(X1)|~r2_hidden(X1,esk5_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.17/1.34  cnf(c_0_48, plain, (r2_hidden(esk6_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.17/1.34  cnf(c_0_49, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.17/1.34  fof(c_0_50, plain, ![X49, X50]:(~r2_hidden(X49,X50)|~r1_tarski(X50,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 1.17/1.34  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.17/1.34  cnf(c_0_52, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 1.17/1.34  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,k3_tarski(esk5_1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)))))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.17/1.34  cnf(c_0_54, plain, (v3_ordinal1(k3_tarski(esk5_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 1.17/1.34  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.17/1.34  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_44])).
% 1.17/1.34  cnf(c_0_57, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.17/1.34  fof(c_0_58, plain, ![X37, X38]:(~v3_ordinal1(X37)|(~v3_ordinal1(X38)|(r2_hidden(X37,X38)|X37=X38|r2_hidden(X38,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 1.17/1.34  cnf(c_0_59, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_53]), c_0_54])])).
% 1.17/1.34  cnf(c_0_60, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.17/1.34  cnf(c_0_61, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_57])).
% 1.17/1.34  cnf(c_0_62, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.17/1.34  cnf(c_0_63, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.17/1.34  cnf(c_0_64, negated_conjecture, (v3_ordinal1(k3_tarski(X1))|~r2_hidden(esk6_1(X1),esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_59])).
% 1.17/1.34  cnf(c_0_65, plain, (~v3_ordinal1(esk2_3(X1,k3_tarski(X1),X2))|~r2_hidden(X1,esk2_3(X1,k3_tarski(X1),X2))|~r2_hidden(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.17/1.34  cnf(c_0_66, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_62])).
% 1.17/1.34  cnf(c_0_67, negated_conjecture, (v4_ordinal1(esk9_0)|r2_hidden(k1_ordinal1(X1),esk9_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.17/1.34  cnf(c_0_68, negated_conjecture, (X1=esk9_0|r2_hidden(X1,esk9_0)|r2_hidden(esk9_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_33])).
% 1.17/1.34  cnf(c_0_69, negated_conjecture, (v3_ordinal1(k3_tarski(esk9_0))), inference(spm,[status(thm)],[c_0_64, c_0_48])).
% 1.17/1.34  fof(c_0_70, plain, ![X25]:((~v4_ordinal1(X25)|X25=k3_tarski(X25))&(X25!=k3_tarski(X25)|v4_ordinal1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 1.17/1.34  cnf(c_0_71, plain, (~v3_ordinal1(esk2_3(X1,k3_tarski(X1),X1))|~r2_hidden(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.17/1.34  fof(c_0_72, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.17/1.34  cnf(c_0_73, negated_conjecture, (v4_ordinal1(esk9_0)|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk9_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk9_0)), inference(rw,[status(thm)],[c_0_67, c_0_26])).
% 1.17/1.34  cnf(c_0_74, negated_conjecture, (k3_tarski(esk9_0)=esk9_0|r2_hidden(esk9_0,k3_tarski(esk9_0))|r2_hidden(k3_tarski(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.17/1.34  cnf(c_0_75, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.17/1.34  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk2_3(X1,k3_tarski(X1),X1),esk9_0)|~r2_hidden(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_71, c_0_59])).
% 1.17/1.34  fof(c_0_77, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.17/1.34  cnf(c_0_78, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.17/1.34  cnf(c_0_79, negated_conjecture, (k3_tarski(esk9_0)=esk9_0|r2_hidden(k2_xboole_0(k3_tarski(esk9_0),k1_tarski(k3_tarski(esk9_0))),esk9_0)|r2_hidden(esk9_0,k3_tarski(esk9_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_69])]), c_0_75])).
% 1.17/1.34  cnf(c_0_80, negated_conjecture, (~r2_hidden(esk9_0,k3_tarski(esk9_0))), inference(spm,[status(thm)],[c_0_76, c_0_61])).
% 1.17/1.34  fof(c_0_81, plain, ![X32]:r2_hidden(X32,k1_ordinal1(X32)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 1.17/1.34  cnf(c_0_82, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.17/1.34  cnf(c_0_83, plain, (~v3_ordinal1(X1)|~r2_hidden(esk2_3(X2,k3_tarski(X2),X1),X1)|~r2_hidden(X1,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_60, c_0_66])).
% 1.17/1.34  cnf(c_0_84, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X3)|~r2_hidden(X2,k3_tarski(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_78, c_0_61])).
% 1.17/1.34  fof(c_0_85, plain, ![X39]:(~v3_ordinal1(X39)|v3_ordinal1(k1_ordinal1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 1.17/1.34  cnf(c_0_86, negated_conjecture, (k3_tarski(esk9_0)=esk9_0|r2_hidden(k2_xboole_0(k3_tarski(esk9_0),k1_tarski(k3_tarski(esk9_0))),esk9_0)), inference(sr,[status(thm)],[c_0_79, c_0_80])).
% 1.17/1.34  cnf(c_0_87, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 1.17/1.34  cnf(c_0_88, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_82])).
% 1.17/1.34  cnf(c_0_89, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.17/1.34  cnf(c_0_90, plain, (r2_hidden(X1,k3_tarski(esk2_3(X2,k3_tarski(X2),X3)))|~r2_hidden(X3,k3_tarski(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_66])).
% 1.17/1.34  cnf(c_0_91, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.17/1.34  cnf(c_0_92, negated_conjecture, (v3_ordinal1(esk10_0)|~v4_ordinal1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.17/1.34  cnf(c_0_93, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.17/1.34  cnf(c_0_94, negated_conjecture, (k3_tarski(esk9_0)=esk9_0|r2_hidden(X1,k3_tarski(esk9_0))|~r2_hidden(X1,k2_xboole_0(k3_tarski(esk9_0),k1_tarski(k3_tarski(esk9_0))))), inference(spm,[status(thm)],[c_0_45, c_0_86])).
% 1.17/1.34  cnf(c_0_95, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_87, c_0_26])).
% 1.17/1.34  cnf(c_0_96, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_55, c_0_88])).
% 1.17/1.34  cnf(c_0_97, plain, (~v3_ordinal1(X1)|~r2_hidden(X2,k3_tarski(X3))|~r2_hidden(X1,X2)|~r1_tarski(esk2_3(X3,k3_tarski(X3),X2),X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.17/1.34  cnf(c_0_98, negated_conjecture, (r2_hidden(esk9_0,X1)|r1_tarski(esk8_1(X1),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_39]), c_0_33]), c_0_24])])).
% 1.17/1.34  cnf(c_0_99, negated_conjecture, (esk8_1(X1)=esk9_0|r2_hidden(esk9_0,esk8_1(X1))|r2_hidden(esk8_1(X1),esk9_0)), inference(spm,[status(thm)],[c_0_68, c_0_24])).
% 1.17/1.34  cnf(c_0_100, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_91, c_0_26])).
% 1.17/1.34  cnf(c_0_101, negated_conjecture, (v3_ordinal1(esk10_0)|k3_tarski(esk9_0)!=esk9_0), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 1.17/1.34  cnf(c_0_102, negated_conjecture, (k3_tarski(esk9_0)=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])).
% 1.17/1.34  cnf(c_0_103, plain, (~v3_ordinal1(X1)|~r2_hidden(esk2_3(X2,k3_tarski(X2),X3),X1)|~r2_hidden(X3,k3_tarski(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_97, c_0_56])).
% 1.17/1.34  cnf(c_0_104, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,esk5_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.17/1.34  cnf(c_0_105, negated_conjecture, (r2_hidden(esk9_0,X1)|~r2_hidden(esk9_0,esk8_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_98])).
% 1.17/1.34  cnf(c_0_106, negated_conjecture, (esk8_1(esk9_0)=esk9_0|r2_hidden(esk9_0,esk8_1(esk9_0))), inference(spm,[status(thm)],[c_0_22, c_0_99])).
% 1.17/1.34  cnf(c_0_107, negated_conjecture, (~r2_hidden(k1_ordinal1(esk10_0),esk9_0)|~v4_ordinal1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.17/1.34  cnf(c_0_108, negated_conjecture, (k2_xboole_0(X1,k1_tarski(X1))=esk9_0|r2_hidden(esk9_0,k2_xboole_0(X1,k1_tarski(X1)))|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk9_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_100])).
% 1.17/1.34  cnf(c_0_109, negated_conjecture, (v3_ordinal1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 1.17/1.34  cnf(c_0_110, negated_conjecture, (r2_hidden(esk10_0,esk9_0)|~v4_ordinal1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.17/1.34  cnf(c_0_111, plain, (~v3_ordinal1(X1)|~r2_hidden(X2,k3_tarski(X1))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_61])).
% 1.17/1.34  cnf(c_0_112, plain, (r2_hidden(esk2_3(esk5_1(X1),k3_tarski(esk5_1(X1)),X2),X1)|~r2_hidden(X2,k3_tarski(esk5_1(X1)))), inference(spm,[status(thm)],[c_0_104, c_0_61])).
% 1.17/1.34  cnf(c_0_113, negated_conjecture, (esk8_1(esk9_0)=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_96])).
% 1.17/1.34  cnf(c_0_114, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.17/1.34  cnf(c_0_115, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.17/1.34  cnf(c_0_116, negated_conjecture, (~v4_ordinal1(esk9_0)|~r2_hidden(k2_xboole_0(esk10_0,k1_tarski(esk10_0)),esk9_0)), inference(rw,[status(thm)],[c_0_107, c_0_26])).
% 1.17/1.34  cnf(c_0_117, negated_conjecture, (k2_xboole_0(esk10_0,k1_tarski(esk10_0))=esk9_0|r2_hidden(k2_xboole_0(esk10_0,k1_tarski(esk10_0)),esk9_0)|r2_hidden(esk9_0,k2_xboole_0(esk10_0,k1_tarski(esk10_0)))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 1.17/1.34  cnf(c_0_118, negated_conjecture, (r2_hidden(esk10_0,esk9_0)|k3_tarski(esk9_0)!=esk9_0), inference(spm,[status(thm)],[c_0_110, c_0_93])).
% 1.17/1.34  cnf(c_0_119, plain, (X2=k3_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(esk3_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.17/1.34  cnf(c_0_120, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.17/1.34  cnf(c_0_121, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X3))|~r2_hidden(X3,k3_tarski(X2))|~r1_tarski(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_111, c_0_84])).
% 1.17/1.34  cnf(c_0_122, plain, (~v3_ordinal1(X1)|~r2_hidden(X2,k3_tarski(esk5_1(X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_112])).
% 1.17/1.34  cnf(c_0_123, negated_conjecture, (r1_ordinal1(esk9_0,X1)|r2_hidden(X1,esk9_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_113])).
% 1.17/1.34  cnf(c_0_124, plain, (v3_ordinal1(X1)|~v3_ordinal1(esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_44, c_0_66])).
% 1.17/1.34  cnf(c_0_125, plain, (r1_tarski(X1,esk5_1(X2))|~v3_ordinal1(esk1_2(X1,esk5_1(X2)))|~r2_hidden(esk1_2(X1,esk5_1(X2)),X2)), inference(spm,[status(thm)],[c_0_114, c_0_23])).
% 1.17/1.34  cnf(c_0_126, plain, (v3_ordinal1(esk1_2(X1,X2))|r1_tarski(X1,X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_115])).
% 1.17/1.34  cnf(c_0_127, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.17/1.34  cnf(c_0_128, negated_conjecture, (k2_xboole_0(esk10_0,k1_tarski(esk10_0))=esk9_0|r2_hidden(esk9_0,k2_xboole_0(esk10_0,k1_tarski(esk10_0)))|~v4_ordinal1(esk9_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 1.17/1.34  cnf(c_0_129, negated_conjecture, (r2_hidden(esk10_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_102])])).
% 1.17/1.34  cnf(c_0_130, plain, (X1=k3_tarski(X2)|r2_hidden(esk4_2(X2,X1),X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_120])).
% 1.17/1.34  cnf(c_0_131, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(X2))|~r1_tarski(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_121, c_0_66])).
% 1.17/1.34  cnf(c_0_132, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_48]), c_0_49])).
% 1.17/1.34  cnf(c_0_133, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X3))|~r2_hidden(X3,k3_tarski(X2))|~r1_tarski(X2,k3_tarski(esk5_1(X1)))), inference(spm,[status(thm)],[c_0_122, c_0_84])).
% 1.17/1.34  cnf(c_0_134, negated_conjecture, (r1_ordinal1(esk9_0,k3_tarski(esk5_1(X1)))|r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)), inference(spm,[status(thm)],[c_0_123, c_0_54])).
% 1.17/1.34  cnf(c_0_135, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(esk2_3(X2,k3_tarski(X2),X1),esk9_0)|~r2_hidden(X1,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_124, c_0_59])).
% 1.17/1.34  cnf(c_0_136, plain, (r1_tarski(X1,esk5_1(X1))|~v3_ordinal1(esk1_2(X1,esk5_1(X1)))), inference(spm,[status(thm)],[c_0_125, c_0_115])).
% 1.17/1.34  cnf(c_0_137, plain, (v3_ordinal1(esk1_2(esk5_1(X1),X2))|r1_tarski(esk5_1(X1),X2)), inference(spm,[status(thm)],[c_0_47, c_0_115])).
% 1.17/1.34  cnf(c_0_138, plain, (r2_hidden(esk1_2(esk5_1(X1),X2),X1)|r1_tarski(esk5_1(X1),X2)), inference(spm,[status(thm)],[c_0_104, c_0_115])).
% 1.17/1.34  cnf(c_0_139, negated_conjecture, (v3_ordinal1(esk1_2(esk10_0,X1))|r1_tarski(esk10_0,X1)), inference(spm,[status(thm)],[c_0_126, c_0_109])).
% 1.17/1.34  cnf(c_0_140, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_127, c_0_26])).
% 1.17/1.34  cnf(c_0_141, negated_conjecture, (k2_xboole_0(esk10_0,k1_tarski(esk10_0))=esk9_0|r2_hidden(esk9_0,k2_xboole_0(esk10_0,k1_tarski(esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_93]), c_0_102])])).
% 1.17/1.34  cnf(c_0_142, negated_conjecture, (~r2_hidden(esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_129]), c_0_109])])).
% 1.17/1.34  cnf(c_0_143, negated_conjecture, (esk10_0=esk9_0|r2_hidden(esk4_2(esk9_0,esk10_0),esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_129]), c_0_102])).
% 1.17/1.34  cnf(c_0_144, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X2,k3_tarski(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_56]), c_0_132])).
% 1.17/1.34  cnf(c_0_145, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(X2))|~r1_tarski(X2,k3_tarski(esk5_1(X1)))), inference(spm,[status(thm)],[c_0_133, c_0_66])).
% 1.17/1.34  cnf(c_0_146, negated_conjecture, (r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)|r1_tarski(esk9_0,k3_tarski(esk5_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_134]), c_0_54]), c_0_33])])).
% 1.17/1.34  cnf(c_0_147, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(esk9_0))), inference(spm,[status(thm)],[c_0_135, c_0_61])).
% 1.17/1.34  cnf(c_0_148, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.17/1.34  cnf(c_0_149, plain, (r1_tarski(esk5_1(X1),esk5_1(esk5_1(X1)))), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 1.17/1.34  cnf(c_0_150, plain, (r1_tarski(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_114, c_0_138])).
% 1.17/1.34  cnf(c_0_151, plain, (v3_ordinal1(esk1_2(k3_tarski(esk5_1(X1)),X2))|r1_tarski(k3_tarski(esk5_1(X1)),X2)), inference(spm,[status(thm)],[c_0_126, c_0_54])).
% 1.17/1.34  cnf(c_0_152, negated_conjecture, (r1_tarski(esk10_0,esk5_1(esk10_0))), inference(spm,[status(thm)],[c_0_136, c_0_139])).
% 1.17/1.34  cnf(c_0_153, negated_conjecture, (k2_xboole_0(esk10_0,k1_tarski(esk10_0))=esk9_0|esk10_0=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_142])).
% 1.17/1.34  cnf(c_0_154, negated_conjecture, (esk10_0=esk9_0|r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk4_2(esk9_0,esk10_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_143]), c_0_102])).
% 1.17/1.34  cnf(c_0_155, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.17/1.34  cnf(c_0_156, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_129]), c_0_102])).
% 1.17/1.34  cnf(c_0_157, plain, (~v3_ordinal1(X1)|~r2_hidden(esk2_3(X2,k3_tarski(X2),X3),k3_tarski(X1))|~r2_hidden(X3,k3_tarski(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_144, c_0_90])).
% 1.17/1.34  cnf(c_0_158, negated_conjecture, (r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)|~r2_hidden(X1,k3_tarski(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_147])).
% 1.17/1.34  cnf(c_0_159, plain, (esk5_1(esk5_1(X1))=esk5_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_150])])).
% 1.17/1.34  cnf(c_0_160, plain, (r1_tarski(k3_tarski(esk5_1(X1)),esk5_1(k3_tarski(esk5_1(X1))))), inference(spm,[status(thm)],[c_0_136, c_0_151])).
% 1.17/1.34  cnf(c_0_161, negated_conjecture, (esk5_1(esk10_0)=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_152]), c_0_150])])).
% 1.17/1.34  cnf(c_0_162, negated_conjecture, (esk10_0=esk9_0|X1=esk10_0|r2_hidden(X1,esk10_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_140, c_0_153])).
% 1.17/1.34  cnf(c_0_163, negated_conjecture, (esk10_0=esk9_0|r2_hidden(esk3_2(esk9_0,esk10_0),esk9_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_102])]), c_0_156])).
% 1.17/1.34  cnf(c_0_164, plain, (~v3_ordinal1(X1)|~r2_hidden(X2,k3_tarski(k3_tarski(X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_157, c_0_61])).
% 1.17/1.34  cnf(c_0_165, negated_conjecture, (r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)|~r2_hidden(esk5_1(X1),k3_tarski(esk9_0))), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 1.17/1.34  cnf(c_0_166, plain, (esk5_1(k3_tarski(esk5_1(X1)))=k3_tarski(esk5_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_160]), c_0_150])])).
% 1.17/1.34  cnf(c_0_167, negated_conjecture, (r2_hidden(k3_tarski(esk10_0),esk9_0)|r1_tarski(esk9_0,k3_tarski(esk10_0))), inference(spm,[status(thm)],[c_0_146, c_0_161])).
% 1.17/1.34  cnf(c_0_168, plain, (v3_ordinal1(esk2_3(esk5_1(X1),k3_tarski(esk5_1(X1)),X2))|~r2_hidden(X2,k3_tarski(esk5_1(X1)))), inference(spm,[status(thm)],[c_0_47, c_0_61])).
% 1.17/1.34  cnf(c_0_169, negated_conjecture, (esk3_2(esk9_0,esk10_0)=esk10_0|esk10_0=esk9_0|r2_hidden(esk3_2(esk9_0,esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 1.17/1.34  cnf(c_0_170, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X3))|~r2_hidden(X3,k3_tarski(X2))|~r1_tarski(X2,k3_tarski(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_164, c_0_84])).
% 1.17/1.34  cnf(c_0_171, negated_conjecture, (r2_hidden(k3_tarski(esk5_1(X1)),esk9_0)|~r2_hidden(esk5_1(X1),esk9_0)), inference(rw,[status(thm)],[c_0_165, c_0_102])).
% 1.17/1.34  cnf(c_0_172, negated_conjecture, (esk5_1(k3_tarski(esk10_0))=k3_tarski(esk10_0)), inference(spm,[status(thm)],[c_0_166, c_0_161])).
% 1.17/1.34  cnf(c_0_173, negated_conjecture, (r2_hidden(k3_tarski(esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_167]), c_0_109]), c_0_102]), c_0_129])])).
% 1.17/1.34  cnf(c_0_174, plain, (v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(esk5_1(X2)))), inference(spm,[status(thm)],[c_0_124, c_0_168])).
% 1.17/1.34  cnf(c_0_175, plain, (X1=k3_tarski(X2)|r2_hidden(esk3_2(X2,X1),X1)|~v3_ordinal1(esk3_2(X2,X1))|~r2_hidden(esk4_2(X2,X1),esk3_2(X2,X1))), inference(spm,[status(thm)],[c_0_60, c_0_155])).
% 1.17/1.34  cnf(c_0_176, negated_conjecture, (esk3_2(esk9_0,esk10_0)=esk10_0|esk10_0=esk9_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_169]), c_0_102]), c_0_129])]), c_0_169])).
% 1.17/1.34  cnf(c_0_177, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(X2))|~r1_tarski(X2,k3_tarski(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_170, c_0_66])).
% 1.17/1.34  cnf(c_0_178, negated_conjecture, (r2_hidden(k3_tarski(k3_tarski(esk10_0)),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_172]), c_0_173])])).
% 1.17/1.34  cnf(c_0_179, plain, (v3_ordinal1(k3_tarski(k3_tarski(esk5_1(X1))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_48]), c_0_49])).
% 1.17/1.34  cnf(c_0_180, negated_conjecture, (esk10_0=esk9_0|~r2_hidden(esk4_2(esk9_0,esk10_0),esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_176]), c_0_102]), c_0_109])]), c_0_96])).
% 1.17/1.34  cnf(c_0_181, negated_conjecture, (esk4_2(esk9_0,esk10_0)=esk10_0|esk10_0=esk9_0|r2_hidden(esk4_2(esk9_0,esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_162, c_0_143])).
% 1.17/1.34  cnf(c_0_182, plain, (~v3_ordinal1(X1)|~r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(X1))))), inference(spm,[status(thm)],[c_0_177, c_0_88])).
% 1.17/1.34  cnf(c_0_183, negated_conjecture, (r2_hidden(k3_tarski(k3_tarski(esk10_0)),X1)|~r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_78, c_0_178])).
% 1.17/1.34  cnf(c_0_184, negated_conjecture, (v3_ordinal1(k3_tarski(k3_tarski(esk10_0)))), inference(spm,[status(thm)],[c_0_179, c_0_161])).
% 1.17/1.34  cnf(c_0_185, negated_conjecture, (esk10_0=esk9_0|r2_hidden(esk10_0,esk4_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_176]), c_0_102])]), c_0_96])).
% 1.17/1.34  cnf(c_0_186, negated_conjecture, (esk4_2(esk9_0,esk10_0)=esk10_0|esk10_0=esk9_0), inference(spm,[status(thm)],[c_0_180, c_0_181])).
% 1.17/1.34  cnf(c_0_187, negated_conjecture, (~r1_tarski(esk9_0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(esk10_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_183]), c_0_184])])).
% 1.17/1.34  cnf(c_0_188, negated_conjecture, (esk10_0=esk9_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_186]), c_0_96])).
% 1.17/1.34  cnf(c_0_189, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187, c_0_188]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_88])]), ['proof']).
% 1.17/1.34  # SZS output end CNFRefutation
% 1.17/1.34  # Proof object total steps             : 190
% 1.17/1.34  # Proof object clause steps            : 155
% 1.17/1.34  # Proof object formula steps           : 35
% 1.17/1.34  # Proof object conjectures             : 70
% 1.17/1.34  # Proof object clause conjectures      : 67
% 1.17/1.34  # Proof object formula conjectures     : 3
% 1.17/1.34  # Proof object initial clauses used    : 37
% 1.17/1.34  # Proof object initial formulas used   : 17
% 1.17/1.34  # Proof object generating inferences   : 101
% 1.17/1.34  # Proof object simplifying inferences  : 90
% 1.17/1.34  # Training examples: 0 positive, 0 negative
% 1.17/1.34  # Parsed axioms                        : 18
% 1.17/1.34  # Removed by relevancy pruning/SinE    : 0
% 1.17/1.34  # Initial clauses                      : 42
% 1.17/1.34  # Removed in clause preprocessing      : 1
% 1.17/1.34  # Initial clauses in saturation        : 41
% 1.17/1.34  # Processed clauses                    : 12432
% 1.17/1.34  # ...of these trivial                  : 138
% 1.17/1.34  # ...subsumed                          : 8884
% 1.17/1.34  # ...remaining for further processing  : 3410
% 1.17/1.34  # Other redundant clauses eliminated   : 6
% 1.17/1.34  # Clauses deleted for lack of memory   : 0
% 1.17/1.34  # Backward-subsumed                    : 204
% 1.17/1.34  # Backward-rewritten                   : 1493
% 1.17/1.34  # Generated clauses                    : 65900
% 1.17/1.34  # ...of the previous two non-trivial   : 61825
% 1.17/1.34  # Contextual simplify-reflections      : 169
% 1.17/1.34  # Paramodulations                      : 65847
% 1.17/1.34  # Factorizations                       : 39
% 1.17/1.34  # Equation resolutions                 : 6
% 1.17/1.34  # Propositional unsat checks           : 0
% 1.17/1.34  #    Propositional check models        : 0
% 1.17/1.34  #    Propositional check unsatisfiable : 0
% 1.17/1.34  #    Propositional clauses             : 0
% 1.17/1.34  #    Propositional clauses after purity: 0
% 1.17/1.34  #    Propositional unsat core size     : 0
% 1.17/1.34  #    Propositional preprocessing time  : 0.000
% 1.17/1.34  #    Propositional encoding time       : 0.000
% 1.17/1.34  #    Propositional solver time         : 0.000
% 1.17/1.34  #    Success case prop preproc time    : 0.000
% 1.17/1.34  #    Success case prop encoding time   : 0.000
% 1.17/1.34  #    Success case prop solver time     : 0.000
% 1.17/1.34  # Current number of processed clauses  : 1660
% 1.17/1.34  #    Positive orientable unit clauses  : 109
% 1.17/1.34  #    Positive unorientable unit clauses: 0
% 1.17/1.34  #    Negative unit clauses             : 281
% 1.17/1.34  #    Non-unit-clauses                  : 1270
% 1.17/1.34  # Current number of unprocessed clauses: 47602
% 1.17/1.34  # ...number of literals in the above   : 142068
% 1.17/1.34  # Current number of archived formulas  : 0
% 1.17/1.34  # Current number of archived clauses   : 1745
% 1.17/1.34  # Clause-clause subsumption calls (NU) : 465954
% 1.17/1.34  # Rec. Clause-clause subsumption calls : 276819
% 1.17/1.34  # Non-unit clause-clause subsumptions  : 4133
% 1.17/1.34  # Unit Clause-clause subsumption calls : 55979
% 1.17/1.34  # Rewrite failures with RHS unbound    : 0
% 1.17/1.34  # BW rewrite match attempts            : 711
% 1.17/1.34  # BW rewrite match successes           : 115
% 1.17/1.34  # Condensation attempts                : 0
% 1.17/1.34  # Condensation successes               : 0
% 1.17/1.34  # Termbank termtop insertions          : 1580677
% 1.17/1.34  
% 1.17/1.34  # -------------------------------------------------
% 1.17/1.34  # User time                : 0.962 s
% 1.17/1.34  # System time              : 0.032 s
% 1.17/1.34  # Total time               : 0.994 s
% 1.17/1.34  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
