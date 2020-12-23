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
% DateTime   : Thu Dec  3 10:49:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 220 expanded)
%              Number of clauses        :   44 (  99 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 ( 640 expanded)
%              Number of equality atoms :   31 ( 126 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc16_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X2) )
     => ( v1_xboole_0(k7_relat_1(X1,X2))
        & v1_relat_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_12,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ( v1_xboole_0(k7_relat_1(X19,X20))
        | ~ v1_relat_1(X19)
        | ~ v1_xboole_0(X20) )
      & ( v1_relat_1(k7_relat_1(X19,X20))
        | ~ v1_relat_1(X19)
        | ~ v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc16_relat_1])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X23)
        | ~ r2_hidden(X22,k1_relat_1(k7_relat_1(X24,X23)))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(X22,k1_relat_1(X24))
        | ~ r2_hidden(X22,k1_relat_1(k7_relat_1(X24,X23)))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X22,X23)
        | ~ r2_hidden(X22,k1_relat_1(X24))
        | r2_hidden(X22,k1_relat_1(k7_relat_1(X24,X23)))
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_16,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_xboole_0(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) )
    & ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k5_relat_1(k6_relat_1(k1_relat_1(X21)),X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_24,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(X26,X25) = k5_relat_1(k6_relat_1(X25),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_27,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k7_relat_1(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_1(k1_relat_1(k7_relat_1(X1,X2))),k1_relat_1(X1))
    | v1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_34,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_1(k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(esk4_0))
    | v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_1(k1_relat_1(k7_relat_1(X1,X2))),X2)
    | v1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_41,plain,
    ( k5_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_36])).

cnf(c_0_44,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,X1)))
    | ~ r2_hidden(esk1_1(k1_relat_1(k7_relat_1(esk4_0,X1))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_1(k1_relat_1(k7_relat_1(esk4_0,X1))),X1)
    | v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_42]),c_0_25])])).

cnf(c_0_51,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(k7_relat_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_xboole_0(k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25])])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_50]),c_0_33]),c_0_33]),c_0_35])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_55]),c_0_33]),c_0_25])]),c_0_56])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_59,plain,(
    ! [X9,X10] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk2_2(X1,k1_relat_1(esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_55])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:28:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.38  fof(fc16_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_xboole_0(X2))=>(v1_xboole_0(k7_relat_1(X1,X2))&v1_relat_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 0.20/0.38  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.20/0.38  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.20/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.38  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.20/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.38  fof(c_0_12, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.38  fof(c_0_13, plain, ![X19, X20]:((v1_xboole_0(k7_relat_1(X19,X20))|(~v1_relat_1(X19)|~v1_xboole_0(X20)))&(v1_relat_1(k7_relat_1(X19,X20))|(~v1_relat_1(X19)|~v1_xboole_0(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc16_relat_1])])])).
% 0.20/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.20/0.38  fof(c_0_15, plain, ![X22, X23, X24]:(((r2_hidden(X22,X23)|~r2_hidden(X22,k1_relat_1(k7_relat_1(X24,X23)))|~v1_relat_1(X24))&(r2_hidden(X22,k1_relat_1(X24))|~r2_hidden(X22,k1_relat_1(k7_relat_1(X24,X23)))|~v1_relat_1(X24)))&(~r2_hidden(X22,X23)|~r2_hidden(X22,k1_relat_1(X24))|r2_hidden(X22,k1_relat_1(k7_relat_1(X24,X23)))|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.20/0.38  fof(c_0_16, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.38  cnf(c_0_17, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_18, plain, (v1_xboole_0(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, (v1_relat_1(esk4_0)&((k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0))&(k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.38  fof(c_0_20, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_22, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_23, plain, ![X21]:(~v1_relat_1(X21)|k5_relat_1(k6_relat_1(k1_relat_1(X21)),X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.20/0.38  cnf(c_0_24, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_26, plain, ![X25, X26]:(~v1_relat_1(X26)|k7_relat_1(X26,X25)=k5_relat_1(k6_relat_1(X25),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.38  fof(c_0_27, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k7_relat_1(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.38  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(esk1_1(k1_relat_1(k7_relat_1(X1,X2))),k1_relat_1(X1))|v1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_32, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_33, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k7_relat_1(esk4_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  cnf(c_0_35, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.38  cnf(c_0_36, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_37, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|~r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_1(k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(esk4_0))|v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.20/0.38  cnf(c_0_40, plain, (r2_hidden(esk1_1(k1_relat_1(k7_relat_1(X1,X2))),X2)|v1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 0.20/0.38  cnf(c_0_41, plain, (k5_relat_1(k6_relat_1(k1_xboole_0),k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (k7_relat_1(esk4_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.38  cnf(c_0_43, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_36])).
% 0.20/0.38  cnf(c_0_44, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_24, c_0_37])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,X1)))|~r2_hidden(esk1_1(k1_relat_1(k7_relat_1(esk4_0,X1))),esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_1(k1_relat_1(k7_relat_1(esk4_0,X1))),X1)|v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 0.20/0.38  cnf(c_0_47, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_48, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_49, plain, (k7_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_42]), c_0_25])])).
% 0.20/0.38  cnf(c_0_51, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_37])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|v1_xboole_0(k1_relat_1(k7_relat_1(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.38  cnf(c_0_53, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)|~v1_xboole_0(k1_relat_1(k7_relat_1(X1,X3)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.38  cnf(c_0_54, plain, (k7_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_25])])).
% 0.20/0.38  cnf(c_0_56, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_50]), c_0_33]), c_0_33]), c_0_35])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_55]), c_0_33]), c_0_25])]), c_0_56])).
% 0.20/0.38  cnf(c_0_58, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_59, plain, ![X9, X10]:(~r1_xboole_0(X9,X10)|r1_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(esk4_0))|~r2_hidden(esk2_2(X1,k1_relat_1(esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.38  cnf(c_0_61, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_63, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_55])])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 67
% 0.20/0.38  # Proof object clause steps            : 44
% 0.20/0.38  # Proof object formula steps           : 23
% 0.20/0.38  # Proof object conjectures             : 20
% 0.20/0.38  # Proof object clause conjectures      : 17
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 12
% 0.20/0.38  # Proof object generating inferences   : 23
% 0.20/0.38  # Proof object simplifying inferences  : 19
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 12
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 21
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 21
% 0.20/0.38  # Processed clauses                    : 219
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 98
% 0.20/0.38  # ...remaining for further processing  : 119
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 22
% 0.20/0.38  # Generated clauses                    : 392
% 0.20/0.38  # ...of the previous two non-trivial   : 241
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 392
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 76
% 0.20/0.38  #    Positive orientable unit clauses  : 12
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 5
% 0.20/0.38  #    Non-unit-clauses                  : 59
% 0.20/0.38  # Current number of unprocessed clauses: 45
% 0.20/0.38  # ...number of literals in the above   : 152
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 43
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 675
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 543
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 63
% 0.20/0.38  # Unit Clause-clause subsumption calls : 36
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 9
% 0.20/0.38  # BW rewrite match successes           : 7
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6762
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.040 s
% 0.20/0.38  # System time              : 0.001 s
% 0.20/0.38  # Total time               : 0.041 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
