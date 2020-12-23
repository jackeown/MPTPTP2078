%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:25 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 235 expanded)
%              Number of clauses        :   45 ( 105 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 ( 837 expanded)
%              Number of equality atoms :   35 ( 184 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_12,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | ~ r1_ordinal1(esk4_0,esk5_0) )
    & ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | r1_ordinal1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X33] : k1_ordinal1(X33) = k2_xboole_0(X33,k1_tarski(X33)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X22
        | X23 != k1_tarski(X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_tarski(X22) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) != X26
        | X27 = k1_tarski(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) = X26
        | X27 = k1_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X36,X37] :
      ( ( ~ r2_hidden(X36,k1_ordinal1(X37))
        | r2_hidden(X36,X37)
        | X36 = X37 )
      & ( ~ r2_hidden(X36,X37)
        | r2_hidden(X36,k1_ordinal1(X37)) )
      & ( X36 != X37
        | r2_hidden(X36,k1_ordinal1(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | ~ r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

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
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_ordinal1(X1,esk5_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))
    | ~ r2_hidden(X1,k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X40,X41] :
      ( ~ v3_ordinal1(X40)
      | ~ v3_ordinal1(X41)
      | r1_ordinal1(X40,X41)
      | r2_hidden(X41,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_29,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_30,plain,(
    ! [X34,X35] :
      ( ( ~ r1_ordinal1(X34,X35)
        | r1_tarski(X34,X35)
        | ~ v3_ordinal1(X34)
        | ~ v3_ordinal1(X35) )
      & ( ~ r1_tarski(X34,X35)
        | r1_ordinal1(X34,X35)
        | ~ v3_ordinal1(X34)
        | ~ v3_ordinal1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_34,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | ~ r1_tarski(X43,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,k1_tarski(X1))
    | ~ r2_hidden(esk4_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35]),c_0_36])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,k1_tarski(X1))
    | ~ r2_hidden(esk4_0,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_34]),c_0_35])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_tarski(X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_tarski(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_53,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_54,plain,(
    ! [X38,X39] :
      ( ~ v3_ordinal1(X38)
      | ~ v3_ordinal1(X39)
      | r2_hidden(X38,X39)
      | X38 = X39
      | r2_hidden(X39,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43]),c_0_52])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_tarski(X1))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_tarski(X1))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_ordinal1(esk5_0,esk5_0)
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_36])]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_34]),c_0_35])]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_66,c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.68  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.47/0.68  # and selection function PSelectUnlessUniqMaxPos.
% 0.47/0.68  #
% 0.47/0.68  # Preprocessing time       : 0.028 s
% 0.47/0.68  # Presaturation interreduction done
% 0.47/0.68  
% 0.47/0.68  # Proof found!
% 0.47/0.68  # SZS status Theorem
% 0.47/0.68  # SZS output start CNFRefutation
% 0.47/0.68  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.47/0.68  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.47/0.68  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.47/0.68  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.47/0.68  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.47/0.68  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.47/0.68  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.47/0.68  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.47/0.68  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.47/0.68  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.47/0.68  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.47/0.68  fof(c_0_11, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.47/0.68  fof(c_0_12, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&((~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0))&(r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.47/0.68  fof(c_0_13, plain, ![X33]:k1_ordinal1(X33)=k2_xboole_0(X33,k1_tarski(X33)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.47/0.68  fof(c_0_14, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|X24=X22|X23!=k1_tarski(X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_tarski(X22)))&((~r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)!=X26|X27=k1_tarski(X26))&(r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)=X26|X27=k1_tarski(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.47/0.68  fof(c_0_15, plain, ![X36, X37]:((~r2_hidden(X36,k1_ordinal1(X37))|(r2_hidden(X36,X37)|X36=X37))&((~r2_hidden(X36,X37)|r2_hidden(X36,k1_ordinal1(X37)))&(X36!=X37|r2_hidden(X36,k1_ordinal1(X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.47/0.68  cnf(c_0_16, negated_conjecture, (~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.68  cnf(c_0_17, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.68  cnf(c_0_18, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.68  cnf(c_0_19, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.68  fof(c_0_20, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.47/0.68  cnf(c_0_21, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.47/0.68  cnf(c_0_22, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_18])).
% 0.47/0.68  cnf(c_0_23, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|X1!=X2), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.47/0.68  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.68  cnf(c_0_25, negated_conjecture, (~r1_ordinal1(X1,esk5_0)|~r2_hidden(X1,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))|~r2_hidden(X1,k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.47/0.68  cnf(c_0_26, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_23])).
% 0.47/0.68  cnf(c_0_27, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.47/0.68  fof(c_0_28, plain, ![X40, X41]:(~v3_ordinal1(X40)|(~v3_ordinal1(X41)|(r1_ordinal1(X40,X41)|r2_hidden(X41,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.47/0.68  fof(c_0_29, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.47/0.68  fof(c_0_30, plain, ![X34, X35]:((~r1_ordinal1(X34,X35)|r1_tarski(X34,X35)|(~v3_ordinal1(X34)|~v3_ordinal1(X35)))&(~r1_tarski(X34,X35)|r1_ordinal1(X34,X35)|(~v3_ordinal1(X34)|~v3_ordinal1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.47/0.68  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.68  cnf(c_0_32, negated_conjecture, (~r1_ordinal1(esk5_0,esk5_0)|~r2_hidden(esk5_0,k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.47/0.68  cnf(c_0_33, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.47/0.68  cnf(c_0_34, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.68  cnf(c_0_35, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.68  cnf(c_0_36, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.68  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.68  fof(c_0_38, plain, ![X42, X43]:(~r2_hidden(X42,X43)|~r1_tarski(X43,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.47/0.68  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.68  cnf(c_0_40, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))), inference(rw,[status(thm)],[c_0_31, c_0_17])).
% 0.47/0.68  cnf(c_0_41, negated_conjecture, (~r1_ordinal1(esk5_0,esk5_0)|~r2_hidden(esk5_0,k1_tarski(X1))|~r2_hidden(esk4_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.47/0.68  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.68  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.47/0.68  cnf(c_0_44, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.68  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.68  cnf(c_0_46, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_35]), c_0_36])])).
% 0.47/0.68  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,esk5_0)|~r2_hidden(esk5_0,k1_tarski(X1))|~r2_hidden(esk4_0,k1_tarski(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_34]), c_0_35])])).
% 0.47/0.68  cnf(c_0_48, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 0.47/0.68  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk4_0,k1_tarski(X1))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 0.47/0.68  cnf(c_0_50, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.47/0.68  cnf(c_0_51, negated_conjecture, (r2_hidden(esk4_0,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))|~r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.47/0.68  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk4_0,k1_tarski(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.47/0.68  fof(c_0_53, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.47/0.68  fof(c_0_54, plain, ![X38, X39]:(~v3_ordinal1(X38)|(~v3_ordinal1(X39)|(r2_hidden(X38,X39)|X38=X39|r2_hidden(X39,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.47/0.68  cnf(c_0_55, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_43]), c_0_52])).
% 0.47/0.68  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.68  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.68  cnf(c_0_58, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.47/0.68  cnf(c_0_59, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(esk5_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_35, c_0_22])).
% 0.47/0.68  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk5_0,k1_tarski(X1))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_22])).
% 0.47/0.68  cnf(c_0_61, negated_conjecture, (~r2_hidden(esk5_0,k1_tarski(X1))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 0.47/0.68  cnf(c_0_62, plain, (~r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_56])).
% 0.47/0.68  cnf(c_0_63, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_57])).
% 0.47/0.68  cnf(c_0_64, negated_conjecture, (~r1_ordinal1(esk5_0,esk5_0)|~r2_hidden(esk5_0,k1_tarski(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_58]), c_0_36])]), c_0_59]), c_0_60]), c_0_61])).
% 0.47/0.68  cnf(c_0_65, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.47/0.68  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk5_0,k1_tarski(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_34]), c_0_35])]), c_0_65])).
% 0.47/0.68  cnf(c_0_67, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_66, c_0_48]), ['proof']).
% 0.47/0.68  # SZS output end CNFRefutation
% 0.47/0.68  # Proof object total steps             : 68
% 0.47/0.68  # Proof object clause steps            : 45
% 0.47/0.68  # Proof object formula steps           : 23
% 0.47/0.68  # Proof object conjectures             : 26
% 0.47/0.68  # Proof object clause conjectures      : 23
% 0.47/0.68  # Proof object formula conjectures     : 3
% 0.47/0.68  # Proof object initial clauses used    : 17
% 0.47/0.68  # Proof object initial formulas used   : 11
% 0.47/0.68  # Proof object generating inferences   : 20
% 0.47/0.68  # Proof object simplifying inferences  : 29
% 0.47/0.68  # Training examples: 0 positive, 0 negative
% 0.47/0.68  # Parsed axioms                        : 13
% 0.47/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.68  # Initial clauses                      : 30
% 0.47/0.68  # Removed in clause preprocessing      : 1
% 0.47/0.68  # Initial clauses in saturation        : 29
% 0.47/0.68  # Processed clauses                    : 1317
% 0.47/0.68  # ...of these trivial                  : 1
% 0.47/0.68  # ...subsumed                          : 656
% 0.47/0.68  # ...remaining for further processing  : 660
% 0.47/0.68  # Other redundant clauses eliminated   : 43
% 0.47/0.68  # Clauses deleted for lack of memory   : 0
% 0.47/0.68  # Backward-subsumed                    : 27
% 0.47/0.68  # Backward-rewritten                   : 7
% 0.47/0.68  # Generated clauses                    : 24090
% 0.47/0.68  # ...of the previous two non-trivial   : 24022
% 0.47/0.68  # Contextual simplify-reflections      : 12
% 0.47/0.68  # Paramodulations                      : 24042
% 0.47/0.68  # Factorizations                       : 4
% 0.47/0.68  # Equation resolutions                 : 43
% 0.47/0.68  # Propositional unsat checks           : 0
% 0.47/0.68  #    Propositional check models        : 0
% 0.47/0.68  #    Propositional check unsatisfiable : 0
% 0.47/0.68  #    Propositional clauses             : 0
% 0.47/0.68  #    Propositional clauses after purity: 0
% 0.47/0.68  #    Propositional unsat core size     : 0
% 0.47/0.68  #    Propositional preprocessing time  : 0.000
% 0.47/0.68  #    Propositional encoding time       : 0.000
% 0.47/0.68  #    Propositional solver time         : 0.000
% 0.47/0.68  #    Success case prop preproc time    : 0.000
% 0.47/0.68  #    Success case prop encoding time   : 0.000
% 0.47/0.68  #    Success case prop solver time     : 0.000
% 0.47/0.68  # Current number of processed clauses  : 590
% 0.47/0.68  #    Positive orientable unit clauses  : 6
% 0.47/0.68  #    Positive unorientable unit clauses: 0
% 0.47/0.68  #    Negative unit clauses             : 83
% 0.47/0.68  #    Non-unit-clauses                  : 501
% 0.47/0.68  # Current number of unprocessed clauses: 22592
% 0.47/0.68  # ...number of literals in the above   : 95756
% 0.47/0.68  # Current number of archived formulas  : 0
% 0.47/0.68  # Current number of archived clauses   : 65
% 0.47/0.68  # Clause-clause subsumption calls (NU) : 196834
% 0.47/0.68  # Rec. Clause-clause subsumption calls : 100637
% 0.47/0.68  # Non-unit clause-clause subsumptions  : 430
% 0.47/0.68  # Unit Clause-clause subsumption calls : 17516
% 0.47/0.68  # Rewrite failures with RHS unbound    : 0
% 0.47/0.68  # BW rewrite match attempts            : 4
% 0.47/0.68  # BW rewrite match successes           : 2
% 0.47/0.68  # Condensation attempts                : 0
% 0.47/0.68  # Condensation successes               : 0
% 0.47/0.68  # Termbank termtop insertions          : 347765
% 0.47/0.68  
% 0.47/0.68  # -------------------------------------------------
% 0.47/0.68  # User time                : 0.315 s
% 0.47/0.68  # System time              : 0.016 s
% 0.47/0.68  # Total time               : 0.331 s
% 0.47/0.68  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
