%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:44 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   51 (1243 expanded)
%              Number of clauses        :   38 ( 632 expanded)
%              Number of leaves         :    7 ( 324 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 (3953 expanded)
%              Number of equality atoms :   31 ( 874 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(t3_xboole_0,conjecture,(
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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_7,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    v1_xboole_0(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_12,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k3_xboole_0(X2,esk3_0)
    | r2_hidden(esk2_3(X2,esk3_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,plain,
    ( X1 = k3_xboole_0(X2,esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_14])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_18,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_19,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( X1 = esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_17])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_xboole_0(k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_20])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r1_xboole_0(X1,X2)
            & ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X2) ) )
        & ~ ( ? [X3] :
                ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) )
            & r1_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t3_xboole_0])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_13])])).

fof(c_0_28,negated_conjecture,(
    ! [X23] :
      ( ( r2_hidden(esk6_0,esk4_0)
        | ~ r1_xboole_0(esk4_0,esk5_0) )
      & ( r2_hidden(esk6_0,esk5_0)
        | ~ r1_xboole_0(esk4_0,esk5_0) )
      & ( r1_xboole_0(esk4_0,esk5_0)
        | ~ r1_xboole_0(esk4_0,esk5_0) )
      & ( r2_hidden(esk6_0,esk4_0)
        | ~ r2_hidden(X23,esk4_0)
        | ~ r2_hidden(X23,esk5_0) )
      & ( r2_hidden(esk6_0,esk5_0)
        | ~ r2_hidden(X23,esk4_0)
        | ~ r2_hidden(X23,esk5_0) )
      & ( r1_xboole_0(esk4_0,esk5_0)
        | ~ r2_hidden(X23,esk4_0)
        | ~ r2_hidden(X23,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])])])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k3_xboole_0(X18,X19) = k1_xboole_0 )
      & ( k3_xboole_0(X18,X19) != k1_xboole_0
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_26]),c_0_26])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0)
    | ~ r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0)
    | k3_xboole_0(esk4_0,esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k3_xboole_0(esk4_0,X2)
    | r1_xboole_0(esk4_0,esk5_0)
    | r2_hidden(esk2_3(esk4_0,X2,X1),X1)
    | ~ r2_hidden(esk2_3(esk4_0,X2,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_10])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | ~ r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0)
    | k3_xboole_0(X1,esk3_0) != k1_xboole_0
    | ~ v1_xboole_0(k3_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_37]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | k3_xboole_0(esk4_0,esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0)
    | ~ v1_xboole_0(k3_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_17]),c_0_26])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_44]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_44])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_44]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DN
% 0.18/0.41  # and selection function PSelectComplexExceptRRHorn.
% 0.18/0.41  #
% 0.18/0.41  # Preprocessing time       : 0.027 s
% 0.18/0.41  # Presaturation interreduction done
% 0.18/0.41  
% 0.18/0.41  # Proof found!
% 0.18/0.41  # SZS status Theorem
% 0.18/0.41  # SZS output start CNFRefutation
% 0.18/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.18/0.41  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.18/0.41  fof(dt_o_0_0_xboole_0, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 0.18/0.41  fof(d2_xboole_0, axiom, k1_xboole_0=o_0_0_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 0.18/0.41  fof(t3_xboole_0, conjecture, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.18/0.41  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.18/0.41  fof(c_0_7, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.41  fof(c_0_8, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|~r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.18/0.41  cnf(c_0_9, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.41  cnf(c_0_10, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.41  fof(c_0_11, plain, v1_xboole_0(esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.18/0.41  cnf(c_0_12, plain, (X1=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.18/0.41  cnf(c_0_13, plain, (v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.41  cnf(c_0_14, plain, (X1=k3_xboole_0(X2,esk3_0)|r2_hidden(esk2_3(X2,esk3_0,X1),X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.41  cnf(c_0_15, plain, (X1=k3_xboole_0(X2,esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_9, c_0_14])).
% 0.18/0.41  cnf(c_0_16, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.41  cnf(c_0_17, plain, (k3_xboole_0(X1,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_15, c_0_13])).
% 0.18/0.41  cnf(c_0_18, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).
% 0.18/0.41  cnf(c_0_19, plain, (k1_xboole_0=o_0_0_xboole_0), inference(split_conjunct,[status(thm)],[d2_xboole_0])).
% 0.18/0.41  cnf(c_0_20, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 0.18/0.41  cnf(c_0_21, plain, (X1=esk3_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_15, c_0_17])).
% 0.18/0.41  cnf(c_0_22, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.41  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~v1_xboole_0(k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_9, c_0_20])).
% 0.18/0.41  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t3_xboole_0])).
% 0.18/0.41  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.41  cnf(c_0_26, plain, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.41  cnf(c_0_27, plain, (~r2_hidden(X1,esk3_0)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_13])])).
% 0.18/0.41  fof(c_0_28, negated_conjecture, ![X23]:((((r2_hidden(esk6_0,esk4_0)|~r1_xboole_0(esk4_0,esk5_0))&(r2_hidden(esk6_0,esk5_0)|~r1_xboole_0(esk4_0,esk5_0)))&(r1_xboole_0(esk4_0,esk5_0)|~r1_xboole_0(esk4_0,esk5_0)))&(((r2_hidden(esk6_0,esk4_0)|(~r2_hidden(X23,esk4_0)|~r2_hidden(X23,esk5_0)))&(r2_hidden(esk6_0,esk5_0)|(~r2_hidden(X23,esk4_0)|~r2_hidden(X23,esk5_0))))&(r1_xboole_0(esk4_0,esk5_0)|(~r2_hidden(X23,esk4_0)|~r2_hidden(X23,esk5_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])])])).
% 0.18/0.41  fof(c_0_29, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k3_xboole_0(X18,X19)=k1_xboole_0)&(k3_xboole_0(X18,X19)!=k1_xboole_0|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.18/0.41  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_25])).
% 0.18/0.41  cnf(c_0_31, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_26]), c_0_26])).
% 0.18/0.41  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.18/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(esk6_0,esk4_0)|~r1_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.41  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.41  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.41  cnf(c_0_36, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.41  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.18/0.41  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,esk4_0)|k3_xboole_0(esk4_0,esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.41  cnf(c_0_39, negated_conjecture, (X1=k3_xboole_0(esk4_0,X2)|r1_xboole_0(esk4_0,esk5_0)|r2_hidden(esk2_3(esk4_0,X2,X1),X1)|~r2_hidden(esk2_3(esk4_0,X2,X1),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.41  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_37, c_0_10])).
% 0.18/0.41  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.41  cnf(c_0_42, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|~r1_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.41  cnf(c_0_43, negated_conjecture, (r2_hidden(esk6_0,esk4_0)|k3_xboole_0(X1,esk3_0)!=k1_xboole_0|~v1_xboole_0(k3_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_15])).
% 0.18/0.41  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_37]), c_0_41])).
% 0.18/0.41  cnf(c_0_45, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|k3_xboole_0(esk4_0,esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.18/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,esk4_0)|~v1_xboole_0(k3_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_17]), c_0_26])])).
% 0.18/0.41  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_44]), c_0_22])])).
% 0.18/0.41  cnf(c_0_48, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_44])])).
% 0.18/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_44]), c_0_22])])).
% 0.18/0.41  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])]), ['proof']).
% 0.18/0.41  # SZS output end CNFRefutation
% 0.18/0.41  # Proof object total steps             : 51
% 0.18/0.41  # Proof object clause steps            : 38
% 0.18/0.41  # Proof object formula steps           : 13
% 0.18/0.41  # Proof object conjectures             : 16
% 0.18/0.41  # Proof object clause conjectures      : 13
% 0.18/0.41  # Proof object formula conjectures     : 3
% 0.18/0.41  # Proof object initial clauses used    : 13
% 0.18/0.41  # Proof object initial formulas used   : 7
% 0.18/0.41  # Proof object generating inferences   : 16
% 0.18/0.41  # Proof object simplifying inferences  : 24
% 0.18/0.41  # Training examples: 0 positive, 0 negative
% 0.18/0.41  # Parsed axioms                        : 7
% 0.18/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.41  # Initial clauses                      : 19
% 0.18/0.41  # Removed in clause preprocessing      : 1
% 0.18/0.41  # Initial clauses in saturation        : 18
% 0.18/0.41  # Processed clauses                    : 497
% 0.18/0.41  # ...of these trivial                  : 0
% 0.18/0.41  # ...subsumed                          : 343
% 0.18/0.41  # ...remaining for further processing  : 154
% 0.18/0.41  # Other redundant clauses eliminated   : 3
% 0.18/0.41  # Clauses deleted for lack of memory   : 0
% 0.18/0.41  # Backward-subsumed                    : 13
% 0.18/0.41  # Backward-rewritten                   : 49
% 0.18/0.41  # Generated clauses                    : 2618
% 0.18/0.41  # ...of the previous two non-trivial   : 2262
% 0.18/0.41  # Contextual simplify-reflections      : 4
% 0.18/0.41  # Paramodulations                      : 2595
% 0.18/0.41  # Factorizations                       : 20
% 0.18/0.41  # Equation resolutions                 : 3
% 0.18/0.41  # Propositional unsat checks           : 0
% 0.18/0.41  #    Propositional check models        : 0
% 0.18/0.41  #    Propositional check unsatisfiable : 0
% 0.18/0.41  #    Propositional clauses             : 0
% 0.18/0.41  #    Propositional clauses after purity: 0
% 0.18/0.41  #    Propositional unsat core size     : 0
% 0.18/0.41  #    Propositional preprocessing time  : 0.000
% 0.18/0.41  #    Propositional encoding time       : 0.000
% 0.18/0.41  #    Propositional solver time         : 0.000
% 0.18/0.41  #    Success case prop preproc time    : 0.000
% 0.18/0.41  #    Success case prop encoding time   : 0.000
% 0.18/0.41  #    Success case prop solver time     : 0.000
% 0.18/0.41  # Current number of processed clauses  : 71
% 0.18/0.41  #    Positive orientable unit clauses  : 8
% 0.18/0.41  #    Positive unorientable unit clauses: 0
% 0.18/0.41  #    Negative unit clauses             : 2
% 0.18/0.41  #    Non-unit-clauses                  : 61
% 0.18/0.41  # Current number of unprocessed clauses: 1758
% 0.18/0.41  # ...number of literals in the above   : 7209
% 0.18/0.41  # Current number of archived formulas  : 0
% 0.18/0.41  # Current number of archived clauses   : 80
% 0.18/0.41  # Clause-clause subsumption calls (NU) : 2518
% 0.18/0.41  # Rec. Clause-clause subsumption calls : 1829
% 0.18/0.41  # Non-unit clause-clause subsumptions  : 267
% 0.18/0.41  # Unit Clause-clause subsumption calls : 64
% 0.18/0.41  # Rewrite failures with RHS unbound    : 0
% 0.18/0.41  # BW rewrite match attempts            : 7
% 0.18/0.41  # BW rewrite match successes           : 7
% 0.18/0.41  # Condensation attempts                : 0
% 0.18/0.41  # Condensation successes               : 0
% 0.18/0.41  # Termbank termtop insertions          : 33428
% 0.18/0.41  
% 0.18/0.41  # -------------------------------------------------
% 0.18/0.41  # User time                : 0.072 s
% 0.18/0.41  # System time              : 0.002 s
% 0.18/0.41  # Total time               : 0.074 s
% 0.18/0.41  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
