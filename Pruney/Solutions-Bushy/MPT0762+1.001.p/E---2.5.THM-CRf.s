%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0762+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 145 expanded)
%              Number of clauses        :   40 (  61 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  252 ( 921 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_wellord1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2)
            & r1_wellord1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(t5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

fof(d9_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> r1_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

fof(d12_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> r4_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

fof(d14_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> r6_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

fof(d16_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> r8_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(t8_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,k3_relat_1(X1))
      <=> v2_wellord1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

fof(c_0_8,plain,(
    ! [X7,X8] :
      ( ( r1_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r8_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r4_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r6_relat_2(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r1_wellord1(X7,X8)
        | ~ r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r1_relat_2(X7,X8)
        | ~ r8_relat_2(X7,X8)
        | ~ r4_relat_2(X7,X8)
        | ~ r6_relat_2(X7,X8)
        | ~ r1_wellord1(X7,X8)
        | r2_wellord1(X7,X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_wellord1])])])])).

fof(c_0_9,plain,(
    ! [X10] :
      ( ( ~ v1_wellord1(X10)
        | r1_wellord1(X10,k3_relat_1(X10))
        | ~ v1_relat_1(X10) )
      & ( ~ r1_wellord1(X10,k3_relat_1(X10))
        | v1_wellord1(X10)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_wellord1])])])).

cnf(c_0_10,plain,
    ( r2_wellord1(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r8_relat_2(X1,X2)
    | ~ r4_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X9] :
      ( ( ~ v1_relat_2(X9)
        | r1_relat_2(X9,k3_relat_1(X9))
        | ~ v1_relat_1(X9) )
      & ( ~ r1_relat_2(X9,k3_relat_1(X9))
        | v1_relat_2(X9)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).

fof(c_0_13,plain,(
    ! [X3] :
      ( ( ~ v4_relat_2(X3)
        | r4_relat_2(X3,k3_relat_1(X3))
        | ~ v1_relat_1(X3) )
      & ( ~ r4_relat_2(X3,k3_relat_1(X3))
        | v4_relat_2(X3)
        | ~ v1_relat_1(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_2])])])).

fof(c_0_14,plain,(
    ! [X4] :
      ( ( ~ v6_relat_2(X4)
        | r6_relat_2(X4,k3_relat_1(X4))
        | ~ v1_relat_1(X4) )
      & ( ~ r6_relat_2(X4,k3_relat_1(X4))
        | v6_relat_2(X4)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_2])])])).

fof(c_0_15,plain,(
    ! [X5] :
      ( ( ~ v8_relat_2(X5)
        | r8_relat_2(X5,k3_relat_1(X5))
        | ~ v1_relat_1(X5) )
      & ( ~ r8_relat_2(X5,k3_relat_1(X5))
        | v8_relat_2(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).

cnf(c_0_16,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ r8_relat_2(X1,k3_relat_1(X1))
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X6] :
      ( ( v1_relat_2(X6)
        | ~ v2_wellord1(X6)
        | ~ v1_relat_1(X6) )
      & ( v8_relat_2(X6)
        | ~ v2_wellord1(X6)
        | ~ v1_relat_1(X6) )
      & ( v4_relat_2(X6)
        | ~ v2_wellord1(X6)
        | ~ v1_relat_1(X6) )
      & ( v6_relat_2(X6)
        | ~ v2_wellord1(X6)
        | ~ v1_relat_1(X6) )
      & ( v1_wellord1(X6)
        | ~ v2_wellord1(X6)
        | ~ v1_relat_1(X6) )
      & ( ~ v1_relat_2(X6)
        | ~ v8_relat_2(X6)
        | ~ v4_relat_2(X6)
        | ~ v6_relat_2(X6)
        | ~ v1_wellord1(X6)
        | v2_wellord1(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_19,plain,
    ( v1_wellord1(X1)
    | ~ r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r1_wellord1(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( v4_relat_2(X1)
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r4_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( v6_relat_2(X1)
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( v8_relat_2(X1)
    | ~ r8_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r8_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( v1_relat_2(X1)
    | ~ r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( r2_wellord1(X1,k3_relat_1(X1))
        <=> v2_wellord1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t8_wellord1])).

cnf(c_0_30,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ r8_relat_2(X1,k3_relat_1(X1))
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_31,plain,
    ( r8_relat_2(X1,k3_relat_1(X1))
    | ~ v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( v1_wellord1(X1)
    | ~ r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_34,plain,
    ( v4_relat_2(X1)
    | ~ r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_35,plain,
    ( v6_relat_2(X1)
    | ~ r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( v8_relat_2(X1)
    | ~ r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( v1_relat_2(X1)
    | ~ r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_38,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ( ~ r2_wellord1(esk1_0,k3_relat_1(esk1_0))
      | ~ v2_wellord1(esk1_0) )
    & ( r2_wellord1(esk1_0,k3_relat_1(esk1_0))
      | v2_wellord1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_39,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( r6_relat_2(X1,k3_relat_1(X1))
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( v2_wellord1(X1)
    | ~ r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_wellord1(esk1_0,k3_relat_1(esk1_0))
    | v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r4_relat_2(X1,k3_relat_1(X1))
    | ~ v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_wellord1(esk1_0,k3_relat_1(esk1_0))
    | ~ v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_48,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_wellord1(esk1_0,k3_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_55,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_47]),c_0_43])]),
    [proof]).

%------------------------------------------------------------------------------
