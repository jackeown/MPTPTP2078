%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t42_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   63 (3840 expanded)
%              Number of clauses        :   42 (1514 expanded)
%              Number of leaves         :   10 ( 915 expanded)
%              Depth                    :   19
%              Number of atoms          :  204 (23635 expanded)
%              Number of equality atoms :   29 (5232 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ ( ~ v4_ordinal1(X1)
            & ! [X2] :
                ( v3_ordinal1(X2)
               => X1 != k1_ordinal1(X2) ) )
        & ~ ( ? [X2] :
                ( v3_ordinal1(X2)
                & X1 = k1_ordinal1(X2) )
            & v4_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t42_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t41_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t33_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',fc2_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',redefinition_r1_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',d8_xboole_0)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',cc1_ordinal1)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t21_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',t10_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t42_ordinal1.p',antisymmetry_r2_hidden)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( ~ ( ~ v4_ordinal1(X1)
              & ! [X2] :
                  ( v3_ordinal1(X2)
                 => X1 != k1_ordinal1(X2) ) )
          & ~ ( ? [X2] :
                  ( v3_ordinal1(X2)
                  & X1 = k1_ordinal1(X2) )
              & v4_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_ordinal1])).

fof(c_0_11,plain,(
    ! [X37,X38] :
      ( ( ~ v4_ordinal1(X37)
        | ~ v3_ordinal1(X38)
        | ~ r2_hidden(X38,X37)
        | r2_hidden(k1_ordinal1(X38),X37)
        | ~ v3_ordinal1(X37) )
      & ( v3_ordinal1(esk4_1(X37))
        | v4_ordinal1(X37)
        | ~ v3_ordinal1(X37) )
      & ( r2_hidden(esk4_1(X37),X37)
        | v4_ordinal1(X37)
        | ~ v3_ordinal1(X37) )
      & ( ~ r2_hidden(k1_ordinal1(esk4_1(X37)),X37)
        | v4_ordinal1(X37)
        | ~ v3_ordinal1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

fof(c_0_12,negated_conjecture,(
    ! [X5] :
      ( v3_ordinal1(esk1_0)
      & ( v3_ordinal1(esk2_0)
        | ~ v4_ordinal1(esk1_0) )
      & ( esk1_0 = k1_ordinal1(esk2_0)
        | ~ v4_ordinal1(esk1_0) )
      & ( v4_ordinal1(esk1_0)
        | ~ v4_ordinal1(esk1_0) )
      & ( v3_ordinal1(esk2_0)
        | ~ v3_ordinal1(X5)
        | esk1_0 != k1_ordinal1(X5) )
      & ( esk1_0 = k1_ordinal1(esk2_0)
        | ~ v3_ordinal1(X5)
        | esk1_0 != k1_ordinal1(X5) )
      & ( v4_ordinal1(esk1_0)
        | ~ v3_ordinal1(X5)
        | esk1_0 != k1_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( v3_ordinal1(esk4_1(X1))
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X33,X34] :
      ( ( ~ r2_hidden(X33,X34)
        | r1_ordinal1(k1_ordinal1(X33),X34)
        | ~ v3_ordinal1(X34)
        | ~ v3_ordinal1(X33) )
      & ( ~ r1_ordinal1(k1_ordinal1(X33),X34)
        | r2_hidden(X33,X34)
        | ~ v3_ordinal1(X34)
        | ~ v3_ordinal1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_17,negated_conjecture,
    ( esk1_0 = k1_ordinal1(esk2_0)
    | ~ v4_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_1(esk1_0),esk1_0)
    | v4_ordinal1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v4_ordinal1(esk1_0)
    | v3_ordinal1(esk4_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_20,plain,(
    ! [X52] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X52))
        | ~ v3_ordinal1(X52) )
      & ( v3_ordinal1(k1_ordinal1(X52))
        | ~ v3_ordinal1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ( ~ r1_ordinal1(X21,X22)
        | r1_tarski(X21,X22)
        | ~ v3_ordinal1(X21)
        | ~ v3_ordinal1(X22) )
      & ( ~ r1_tarski(X21,X22)
        | r1_ordinal1(X21,X22)
        | ~ v3_ordinal1(X21)
        | ~ v3_ordinal1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_22,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | r2_hidden(esk4_1(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | v3_ordinal1(esk4_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_25,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | ~ r2_xboole_0(X15,X16) )
      & ( X15 != X16
        | ~ r2_xboole_0(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | X15 = X16
        | r2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | r1_ordinal1(k1_ordinal1(esk4_1(esk1_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14])]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | v3_ordinal1(k1_ordinal1(esk4_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 = k1_ordinal1(esk2_0)
    | ~ v3_ordinal1(X1)
    | esk1_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_31,plain,(
    ! [X51] :
      ( ( v1_ordinal1(X51)
        | ~ v3_ordinal1(X51) )
      & ( v2_ordinal1(X51)
        | ~ v3_ordinal1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_32,plain,(
    ! [X29,X30] :
      ( ~ v1_ordinal1(X29)
      | ~ v3_ordinal1(X30)
      | ~ r2_xboole_0(X29,X30)
      | r2_hidden(X29,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | r1_tarski(k1_ordinal1(esk4_1(esk1_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_14])]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | k1_ordinal1(esk4_1(esk1_0)) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_36,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | r2_xboole_0(k1_ordinal1(esk4_1(esk1_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | v1_ordinal1(k1_ordinal1(esk4_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

fof(c_0_40,plain,(
    ! [X25] : r2_hidden(X25,k1_ordinal1(X25)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_41,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk4_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0
    | r2_hidden(k1_ordinal1(esk4_1(esk1_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_14])]),c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k1_ordinal1(esk2_0) = esk1_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_14])]),c_0_17])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    | ~ v4_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_0,esk1_0)
    | ~ v4_ordinal1(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_44]),c_0_14])]),c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_1(esk1_0),esk1_0)
    | r2_hidden(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_0,esk1_0)
    | v3_ordinal1(esk4_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r1_ordinal1(k1_ordinal1(esk4_1(esk1_0)),esk1_0)
    | r2_hidden(esk1_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_49]),c_0_14])]),c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_0,esk1_0)
    | v3_ordinal1(k1_ordinal1(esk4_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( v4_ordinal1(esk1_0)
    | ~ v3_ordinal1(X1)
    | esk1_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_ordinal1(esk4_1(esk1_0)),esk1_0)
    | r2_hidden(esk1_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_51]),c_0_14])]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_0,esk1_0)
    | k1_ordinal1(esk4_1(esk1_0)) != esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_xboole_0(k1_ordinal1(esk4_1(esk1_0)),esk1_0)
    | r2_hidden(esk1_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_54]),c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( v1_ordinal1(k1_ordinal1(esk4_1(esk1_0)))
    | r2_hidden(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_52])).

fof(c_0_58,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ r2_hidden(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_ordinal1(esk4_1(esk1_0)),esk1_0)
    | r2_hidden(esk1_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_56]),c_0_14])]),c_0_57])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_59]),c_0_14])]),c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
