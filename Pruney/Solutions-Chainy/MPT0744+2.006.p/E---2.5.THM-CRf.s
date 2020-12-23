%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   82 (2110 expanded)
%              Number of clauses        :   49 ( 835 expanded)
%              Number of leaves         :   16 ( 556 expanded)
%              Depth                    :   18
%              Number of atoms          :  252 (6192 expanded)
%              Number of equality atoms :   84 (1254 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_17,plain,(
    ! [X50] : k1_ordinal1(X50) = k2_xboole_0(X50,k1_tarski(X50)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_18,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & ( ~ r2_hidden(esk3_0,k1_ordinal1(esk4_0))
      | ~ r1_ordinal1(esk3_0,esk4_0) )
    & ( r2_hidden(esk3_0,k1_ordinal1(esk4_0))
      | r1_ordinal1(esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_20,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X51,X52] :
      ( ( ~ r1_ordinal1(X51,X52)
        | r1_tarski(X51,X52)
        | ~ v3_ordinal1(X51)
        | ~ v3_ordinal1(X52) )
      & ( ~ r1_tarski(X51,X52)
        | r1_ordinal1(X51,X52)
        | ~ v3_ordinal1(X51)
        | ~ v3_ordinal1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_0,k1_ordinal1(esk4_0))
    | r1_ordinal1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | ~ r2_xboole_0(X19,X20) )
      & ( X19 != X20
        | ~ r2_xboole_0(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | X19 = X20
        | r2_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk4_0)
    | r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_36,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X17)
        | r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_37,plain,(
    ! [X53,X54] :
      ( ~ v1_ordinal1(X53)
      | ~ v3_ordinal1(X54)
      | ~ r2_xboole_0(X53,X54)
      | r2_hidden(X53,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_ordinal1(esk4_0))
    | ~ r1_ordinal1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_42,plain,(
    ! [X55,X56] :
      ( ~ v3_ordinal1(X55)
      | ~ v3_ordinal1(X56)
      | r1_ordinal1(X55,X56)
      | r2_hidden(X56,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_xboole_0(esk3_0,esk4_0)
    | r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X49] :
      ( ( v1_ordinal1(X49)
        | ~ v3_ordinal1(X49) )
      & ( v2_ordinal1(X49)
        | ~ v3_ordinal1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_ordinal1(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_48,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))
    | ~ v1_ordinal1(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])]),c_0_45])).

cnf(c_0_50,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_51,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | ~ r2_hidden(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34]),c_0_35])])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_57,plain,(
    ! [X33] : k3_tarski(k1_tarski(X33)) = X33 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | r1_tarski(X31,k3_tarski(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_60])).

cnf(c_0_64,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_21]),c_0_28]),c_0_29]),c_0_30])).

fof(c_0_65,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X34
        | X40 = X35
        | X40 = X36
        | X40 = X37
        | X40 = X38
        | X39 != k3_enumset1(X34,X35,X36,X37,X38) )
      & ( X41 != X34
        | r2_hidden(X41,X39)
        | X39 != k3_enumset1(X34,X35,X36,X37,X38) )
      & ( X41 != X35
        | r2_hidden(X41,X39)
        | X39 != k3_enumset1(X34,X35,X36,X37,X38) )
      & ( X41 != X36
        | r2_hidden(X41,X39)
        | X39 != k3_enumset1(X34,X35,X36,X37,X38) )
      & ( X41 != X37
        | r2_hidden(X41,X39)
        | X39 != k3_enumset1(X34,X35,X36,X37,X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k3_enumset1(X34,X35,X36,X37,X38) )
      & ( esk2_6(X42,X43,X44,X45,X46,X47) != X42
        | ~ r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)
        | X47 = k3_enumset1(X42,X43,X44,X45,X46) )
      & ( esk2_6(X42,X43,X44,X45,X46,X47) != X43
        | ~ r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)
        | X47 = k3_enumset1(X42,X43,X44,X45,X46) )
      & ( esk2_6(X42,X43,X44,X45,X46,X47) != X44
        | ~ r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)
        | X47 = k3_enumset1(X42,X43,X44,X45,X46) )
      & ( esk2_6(X42,X43,X44,X45,X46,X47) != X45
        | ~ r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)
        | X47 = k3_enumset1(X42,X43,X44,X45,X46) )
      & ( esk2_6(X42,X43,X44,X45,X46,X47) != X46
        | ~ r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)
        | X47 = k3_enumset1(X42,X43,X44,X45,X46) )
      & ( r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)
        | esk2_6(X42,X43,X44,X45,X46,X47) = X42
        | esk2_6(X42,X43,X44,X45,X46,X47) = X43
        | esk2_6(X42,X43,X44,X45,X46,X47) = X44
        | esk2_6(X42,X43,X44,X45,X46,X47) = X45
        | esk2_6(X42,X43,X44,X45,X46,X47) = X46
        | X47 = k3_enumset1(X42,X43,X44,X45,X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = esk3_0
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_66])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ v1_ordinal1(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_68]),c_0_34])]),c_0_60])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X3,X4,X5,X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_50]),c_0_35])])).

cnf(c_0_73,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_64])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_ordinal1(esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72])).

cnf(c_0_77,plain,
    ( r1_ordinal1(X1,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_xboole_0(esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_35])])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k3_enumset1(X3,X4,X5,X6,X1))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.13/0.38  # and selection function SelectCQArNTNpEqFirst.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.13/0.38  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.13/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.13/0.38  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.13/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.13/0.38  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.13/0.38  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.13/0.38  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.13/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.13/0.38  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.13/0.38  fof(c_0_17, plain, ![X50]:k1_ordinal1(X50)=k2_xboole_0(X50,k1_tarski(X50)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.38  fof(c_0_18, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&((~r2_hidden(esk3_0,k1_ordinal1(esk4_0))|~r1_ordinal1(esk3_0,esk4_0))&(r2_hidden(esk3_0,k1_ordinal1(esk4_0))|r1_ordinal1(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.38  cnf(c_0_20, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_22, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_24, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_25, plain, ![X51, X52]:((~r1_ordinal1(X51,X52)|r1_tarski(X51,X52)|(~v3_ordinal1(X51)|~v3_ordinal1(X52)))&(~r1_tarski(X51,X52)|r1_ordinal1(X51,X52)|(~v3_ordinal1(X51)|~v3_ordinal1(X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_0,k1_ordinal1(esk4_0))|r1_ordinal1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_31, plain, ![X19, X20]:(((r1_tarski(X19,X20)|~r2_xboole_0(X19,X20))&(X19!=X20|~r2_xboole_0(X19,X20)))&(~r1_tarski(X19,X20)|X19=X20|r2_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r1_ordinal1(esk3_0,esk4_0)|r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_36, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X13,X12)|(r2_hidden(X13,X10)|r2_hidden(X13,X11))|X12!=k2_xboole_0(X10,X11))&((~r2_hidden(X14,X10)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))&(~r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))))&(((~r2_hidden(esk1_3(X15,X16,X17),X15)|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16))&(~r2_hidden(esk1_3(X15,X16,X17),X16)|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16)))&(r2_hidden(esk1_3(X15,X16,X17),X17)|(r2_hidden(esk1_3(X15,X16,X17),X15)|r2_hidden(esk1_3(X15,X16,X17),X16))|X17=k2_xboole_0(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.13/0.38  fof(c_0_37, plain, ![X53, X54]:(~v1_ordinal1(X53)|(~v3_ordinal1(X54)|(~r2_xboole_0(X53,X54)|r2_hidden(X53,X54)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.13/0.38  cnf(c_0_38, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.13/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk3_0,k1_ordinal1(esk4_0))|~r1_ordinal1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_42, plain, ![X55, X56]:(~v3_ordinal1(X55)|(~v3_ordinal1(X56)|(r1_ordinal1(X55,X56)|r2_hidden(X56,X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.13/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk4_0=esk3_0|r2_xboole_0(esk3_0,esk4_0)|r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  fof(c_0_46, plain, ![X49]:((v1_ordinal1(X49)|~v3_ordinal1(X49))&(v2_ordinal1(X49)|~v3_ordinal1(X49))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~r1_ordinal1(esk3_0,esk4_0)|~r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.13/0.38  cnf(c_0_48, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))|~v1_ordinal1(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34])]), c_0_45])).
% 0.13/0.38  cnf(c_0_50, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  fof(c_0_51, plain, ![X8, X9]:(~r2_hidden(X8,X9)|~r2_hidden(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_34]), c_0_35])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35])])).
% 0.13/0.38  cnf(c_0_54, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  fof(c_0_57, plain, ![X33]:k3_tarski(k1_tarski(X33))=X33, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.13/0.38  fof(c_0_58, plain, ![X31, X32]:(~r2_hidden(X31,X32)|r1_tarski(X31,k3_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_59, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_54])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (esk4_0=esk3_0|~r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_61, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.38  cnf(c_0_62, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_60])).
% 0.13/0.38  cnf(c_0_64, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_21]), c_0_28]), c_0_29]), c_0_30])).
% 0.13/0.38  fof(c_0_65, plain, ![X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47]:(((~r2_hidden(X40,X39)|(X40=X34|X40=X35|X40=X36|X40=X37|X40=X38)|X39!=k3_enumset1(X34,X35,X36,X37,X38))&(((((X41!=X34|r2_hidden(X41,X39)|X39!=k3_enumset1(X34,X35,X36,X37,X38))&(X41!=X35|r2_hidden(X41,X39)|X39!=k3_enumset1(X34,X35,X36,X37,X38)))&(X41!=X36|r2_hidden(X41,X39)|X39!=k3_enumset1(X34,X35,X36,X37,X38)))&(X41!=X37|r2_hidden(X41,X39)|X39!=k3_enumset1(X34,X35,X36,X37,X38)))&(X41!=X38|r2_hidden(X41,X39)|X39!=k3_enumset1(X34,X35,X36,X37,X38))))&((((((esk2_6(X42,X43,X44,X45,X46,X47)!=X42|~r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)|X47=k3_enumset1(X42,X43,X44,X45,X46))&(esk2_6(X42,X43,X44,X45,X46,X47)!=X43|~r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)|X47=k3_enumset1(X42,X43,X44,X45,X46)))&(esk2_6(X42,X43,X44,X45,X46,X47)!=X44|~r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)|X47=k3_enumset1(X42,X43,X44,X45,X46)))&(esk2_6(X42,X43,X44,X45,X46,X47)!=X45|~r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)|X47=k3_enumset1(X42,X43,X44,X45,X46)))&(esk2_6(X42,X43,X44,X45,X46,X47)!=X46|~r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)|X47=k3_enumset1(X42,X43,X44,X45,X46)))&(r2_hidden(esk2_6(X42,X43,X44,X45,X46,X47),X47)|(esk2_6(X42,X43,X44,X45,X46,X47)=X42|esk2_6(X42,X43,X44,X45,X46,X47)=X43|esk2_6(X42,X43,X44,X45,X46,X47)=X44|esk2_6(X42,X43,X44,X45,X46,X47)=X45|esk2_6(X42,X43,X44,X45,X46,X47)=X46)|X47=k3_enumset1(X42,X43,X44,X45,X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (esk4_0=esk3_0|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.13/0.38  cnf(c_0_67, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (esk4_0=esk3_0|r2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_66])).
% 0.13/0.38  cnf(c_0_69, plain, (r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (esk4_0=esk3_0|~v1_ordinal1(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_68]), c_0_34])]), c_0_60])).
% 0.13/0.38  cnf(c_0_71, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X3,X4,X5,X1)))), inference(spm,[status(thm)],[c_0_62, c_0_69])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_50]), c_0_35])])).
% 0.13/0.38  cnf(c_0_73, plain, (r1_ordinal1(X1,X2)|~r1_tarski(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_71, c_0_64])).
% 0.13/0.38  cnf(c_0_75, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (~r1_ordinal1(esk3_0,esk3_0)|~r2_hidden(esk3_0,k2_xboole_0(esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72])).
% 0.13/0.38  cnf(c_0_77, plain, (r1_ordinal1(X1,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.38  cnf(c_0_78, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_75])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk3_0,k2_xboole_0(esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_35])])).
% 0.13/0.38  cnf(c_0_80, plain, (r2_hidden(X1,k2_xboole_0(X2,k3_enumset1(X3,X4,X5,X6,X1)))), inference(spm,[status(thm)],[c_0_78, c_0_69])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 82
% 0.13/0.38  # Proof object clause steps            : 49
% 0.13/0.38  # Proof object formula steps           : 33
% 0.13/0.38  # Proof object conjectures             : 24
% 0.13/0.38  # Proof object clause conjectures      : 21
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 22
% 0.13/0.38  # Proof object initial formulas used   : 16
% 0.13/0.38  # Proof object generating inferences   : 17
% 0.13/0.38  # Proof object simplifying inferences  : 47
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 16
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 39
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 34
% 0.13/0.38  # Processed clauses                    : 127
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 9
% 0.13/0.38  # ...remaining for further processing  : 118
% 0.13/0.38  # Other redundant clauses eliminated   : 15
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 20
% 0.13/0.38  # Generated clauses                    : 122
% 0.13/0.38  # ...of the previous two non-trivial   : 115
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 105
% 0.13/0.38  # Factorizations                       : 6
% 0.13/0.38  # Equation resolutions                 : 15
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 51
% 0.13/0.38  #    Positive orientable unit clauses  : 13
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 7
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 45
% 0.13/0.38  # ...number of literals in the above   : 165
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 62
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 478
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 328
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.13/0.38  # Unit Clause-clause subsumption calls : 51
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 28
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3902
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.009 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
