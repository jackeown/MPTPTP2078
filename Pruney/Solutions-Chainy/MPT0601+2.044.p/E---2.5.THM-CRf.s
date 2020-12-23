%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 115 expanded)
%              Number of clauses        :   29 (  55 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 394 expanded)
%              Number of equality atoms :   47 ( 137 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_8,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X18] : k4_xboole_0(k1_xboole_0,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_12,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_10])).

fof(c_0_16,plain,(
    ! [X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(k4_tarski(X21,esk3_3(X19,X20,X21)),X19)
        | X20 != k1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X19)
        | r2_hidden(X23,X20)
        | X20 != k1_relat_1(X19) )
      & ( ~ r2_hidden(esk4_2(X25,X26),X26)
        | ~ r2_hidden(k4_tarski(esk4_2(X25,X26),X28),X25)
        | X26 = k1_relat_1(X25) )
      & ( r2_hidden(esk4_2(X25,X26),X26)
        | r2_hidden(k4_tarski(esk4_2(X25,X26),esk5_2(X25,X26)),X25)
        | X26 = k1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(k4_tarski(X2,esk3_3(k1_xboole_0,X1,X2)),X3)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_20,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_21,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r2_hidden(k4_tarski(X30,X31),X32)
        | r2_hidden(X31,k11_relat_1(X32,X30))
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(X31,k11_relat_1(X32,X30))
        | r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk2_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_31,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k11_relat_1(X1,X3))
    | X2 != k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

fof(c_0_33,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( ~ r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) = k1_xboole_0 )
    & ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
      | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_34,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,X3)
    | X3 != k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k11_relat_1(X1,X2) != k1_xboole_0
    | X3 != k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k11_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0))
    | k11_relat_1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( X1 != k1_relat_1(esk7_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk7_0))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( X1 != k1_relat_1(esk7_0)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_42,c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.027 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.50  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.50  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.50  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.50  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.50  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.19/0.50  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.19/0.50  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.50  fof(c_0_8, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.50  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.50  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.50  fof(c_0_11, plain, ![X18]:k4_xboole_0(k1_xboole_0,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.50  cnf(c_0_12, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.50  cnf(c_0_13, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  cnf(c_0_14, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_15, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_13, c_0_10])).
% 0.19/0.50  fof(c_0_16, plain, ![X19, X20, X21, X23, X24, X25, X26, X28]:(((~r2_hidden(X21,X20)|r2_hidden(k4_tarski(X21,esk3_3(X19,X20,X21)),X19)|X20!=k1_relat_1(X19))&(~r2_hidden(k4_tarski(X23,X24),X19)|r2_hidden(X23,X20)|X20!=k1_relat_1(X19)))&((~r2_hidden(esk4_2(X25,X26),X26)|~r2_hidden(k4_tarski(esk4_2(X25,X26),X28),X25)|X26=k1_relat_1(X25))&(r2_hidden(esk4_2(X25,X26),X26)|r2_hidden(k4_tarski(esk4_2(X25,X26),esk5_2(X25,X26)),X25)|X26=k1_relat_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.50  cnf(c_0_17, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.50  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_19, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(k4_tarski(X2,esk3_3(k1_xboole_0,X1,X2)),X3)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.50  fof(c_0_20, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.50  cnf(c_0_21, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.50  cnf(c_0_22, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  fof(c_0_23, plain, ![X30, X31, X32]:((~r2_hidden(k4_tarski(X30,X31),X32)|r2_hidden(X31,k11_relat_1(X32,X30))|~v1_relat_1(X32))&(~r2_hidden(X31,k11_relat_1(X32,X30))|r2_hidden(k4_tarski(X30,X31),X32)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.19/0.50  cnf(c_0_24, plain, (X1=k1_xboole_0|X1!=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.50  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  cnf(c_0_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.50  cnf(c_0_27, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.19/0.50  cnf(c_0_29, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_30, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk2_1(k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.19/0.50  cnf(c_0_31, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_21, c_0_26])).
% 0.19/0.50  cnf(c_0_32, plain, (r2_hidden(esk3_3(X1,X2,X3),k11_relat_1(X1,X3))|X2!=k1_relat_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_27, c_0_18])).
% 0.19/0.50  fof(c_0_33, negated_conjecture, (v1_relat_1(esk7_0)&((~r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)=k1_xboole_0)&(r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.19/0.50  cnf(c_0_34, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,X3)|X3!=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.50  cnf(c_0_35, plain, (k11_relat_1(X1,X2)!=k1_xboole_0|X3!=k1_relat_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.50  cnf(c_0_36, negated_conjecture, (k11_relat_1(esk7_0,esk6_0)=k1_xboole_0|~r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))|k11_relat_1(esk7_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.50  cnf(c_0_39, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_40, negated_conjecture, (X1!=k1_relat_1(esk7_0)|~r2_hidden(esk6_0,k1_relat_1(esk7_0))|~r2_hidden(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.50  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_37])])).
% 0.19/0.50  cnf(c_0_42, negated_conjecture, (X1!=k1_relat_1(esk7_0)|~r2_hidden(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.19/0.50  cnf(c_0_43, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_42, c_0_41]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 44
% 0.19/0.50  # Proof object clause steps            : 29
% 0.19/0.50  # Proof object formula steps           : 15
% 0.19/0.50  # Proof object conjectures             : 10
% 0.19/0.50  # Proof object clause conjectures      : 7
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 11
% 0.19/0.50  # Proof object initial formulas used   : 7
% 0.19/0.50  # Proof object generating inferences   : 14
% 0.19/0.50  # Proof object simplifying inferences  : 9
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 7
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 18
% 0.19/0.50  # Removed in clause preprocessing      : 1
% 0.19/0.50  # Initial clauses in saturation        : 17
% 0.19/0.50  # Processed clauses                    : 2250
% 0.19/0.50  # ...of these trivial                  : 71
% 0.19/0.50  # ...subsumed                          : 1920
% 0.19/0.50  # ...remaining for further processing  : 259
% 0.19/0.50  # Other redundant clauses eliminated   : 0
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 25
% 0.19/0.50  # Backward-rewritten                   : 7
% 0.19/0.50  # Generated clauses                    : 9718
% 0.19/0.50  # ...of the previous two non-trivial   : 8497
% 0.19/0.50  # Contextual simplify-reflections      : 6
% 0.19/0.50  # Paramodulations                      : 9631
% 0.19/0.50  # Factorizations                       : 6
% 0.19/0.50  # Equation resolutions                 : 81
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 210
% 0.19/0.50  #    Positive orientable unit clauses  : 5
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 3
% 0.19/0.50  #    Non-unit-clauses                  : 202
% 0.19/0.50  # Current number of unprocessed clauses: 6265
% 0.19/0.50  # ...number of literals in the above   : 32709
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 50
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 16272
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 9453
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 1267
% 0.19/0.50  # Unit Clause-clause subsumption calls : 193
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 11
% 0.19/0.50  # BW rewrite match successes           : 3
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 127534
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.155 s
% 0.19/0.50  # System time              : 0.012 s
% 0.19/0.50  # Total time               : 0.167 s
% 0.19/0.50  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
