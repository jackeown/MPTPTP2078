%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0751+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:08 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 406 expanded)
%              Number of clauses        :   30 ( 170 expanded)
%              Number of leaves         :   10 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 (2253 expanded)
%              Number of equality atoms :   20 ( 256 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(X14,X15)
        | r1_ordinal1(k1_ordinal1(X14),X15)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X14) )
      & ( ~ r1_ordinal1(k1_ordinal1(X14),X15)
        | r2_hidden(X14,X15)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ( ~ v4_ordinal1(X16)
        | ~ v3_ordinal1(X17)
        | ~ r2_hidden(X17,X16)
        | r2_hidden(k1_ordinal1(X17),X16)
        | ~ v3_ordinal1(X16) )
      & ( v3_ordinal1(esk1_1(X16))
        | v4_ordinal1(X16)
        | ~ v3_ordinal1(X16) )
      & ( r2_hidden(esk1_1(X16),X16)
        | v4_ordinal1(X16)
        | ~ v3_ordinal1(X16) )
      & ( ~ r2_hidden(k1_ordinal1(esk1_1(X16)),X16)
        | v4_ordinal1(X16)
        | ~ v3_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( ~ r1_ordinal1(X9,X10)
        | r1_tarski(X9,X10)
        | ~ v3_ordinal1(X9)
        | ~ v3_ordinal1(X10) )
      & ( ~ r1_tarski(X9,X10)
        | r1_ordinal1(X9,X10)
        | ~ v3_ordinal1(X9)
        | ~ v3_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_13,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v3_ordinal1(esk1_1(X1))
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v4_ordinal1(X1)
    | r1_ordinal1(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

fof(c_0_18,plain,(
    ! [X8] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X8))
        | ~ v3_ordinal1(X8) )
      & ( v3_ordinal1(k1_ordinal1(X8))
        | ~ v3_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | ~ r2_xboole_0(X6,X7) )
      & ( X6 != X7
        | ~ r2_xboole_0(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | X6 = X7
        | r2_xboole_0(X6,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_20,plain,
    ( v4_ordinal1(X1)
    | r1_tarski(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(k1_ordinal1(esk1_1(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ~ v1_ordinal1(X12)
      | ~ v3_ordinal1(X13)
      | ~ r2_xboole_0(X12,X13)
      | r2_hidden(X12,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v4_ordinal1(X1)
    | r1_tarski(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_ordinal1(esk1_1(X1)) = X1
    | v4_ordinal1(X1)
    | r2_xboole_0(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_28,plain,(
    ! [X5] :
      ( ( v1_ordinal1(X5)
        | ~ v3_ordinal1(X5) )
      & ( v2_ordinal1(X5)
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_29,negated_conjecture,(
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

cnf(c_0_30,plain,
    ( k1_ordinal1(esk1_1(X1)) = X1
    | v4_ordinal1(X1)
    | ~ v1_ordinal1(k1_ordinal1(esk1_1(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,negated_conjecture,(
    ! [X20] :
      ( v3_ordinal1(esk2_0)
      & ( v3_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v4_ordinal1(esk2_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v3_ordinal1(esk3_0)
        | ~ v3_ordinal1(X20)
        | esk2_0 != k1_ordinal1(X20) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v3_ordinal1(X20)
        | esk2_0 != k1_ordinal1(X20) )
      & ( v4_ordinal1(esk2_0)
        | ~ v3_ordinal1(X20)
        | esk2_0 != k1_ordinal1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])])])).

cnf(c_0_33,plain,
    ( k1_ordinal1(esk1_1(X1)) = X1
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(esk1_1(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | ~ v3_ordinal1(X1)
    | esk2_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,plain,
    ( k1_ordinal1(esk1_1(X1)) = X1
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X11] : r2_hidden(X11,k1_ordinal1(X11)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_38,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | ~ v3_ordinal1(esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])]),c_0_36])])).

cnf(c_0_39,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = k1_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v4_ordinal1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_15]),c_0_36])])).

cnf(c_0_43,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X3,X4] :
      ( ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X4,X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_ordinal1(X1),k1_ordinal1(X1))
    | ~ v4_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( k1_ordinal1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_42])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42]),c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_49])]),
    [proof]).

%------------------------------------------------------------------------------
