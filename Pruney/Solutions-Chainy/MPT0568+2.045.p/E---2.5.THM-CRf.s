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
% DateTime   : Thu Dec  3 10:51:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 101 expanded)
%              Number of clauses        :   21 (  47 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 248 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_10,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tarski(X27,k1_tarski(X28))
        | X27 = k1_xboole_0
        | X27 = k1_tarski(X28) )
      & ( X27 != k1_xboole_0
        | r1_tarski(X27,k1_tarski(X28)) )
      & ( X27 != k1_tarski(X28)
        | r1_tarski(X27,k1_tarski(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_xboole_0(X16,X17)
      | r1_xboole_0(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( r2_hidden(X25,X26)
      | r1_xboole_0(k1_tarski(X25),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

fof(c_0_19,plain,(
    ! [X38,X39,X40,X41,X43,X44,X45,X46,X48] :
      ( ( r2_hidden(k4_tarski(X41,esk4_4(X38,X39,X40,X41)),X38)
        | ~ r2_hidden(X41,X40)
        | X40 != k10_relat_1(X38,X39)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(esk4_4(X38,X39,X40,X41),X39)
        | ~ r2_hidden(X41,X40)
        | X40 != k10_relat_1(X38,X39)
        | ~ v1_relat_1(X38) )
      & ( ~ r2_hidden(k4_tarski(X43,X44),X38)
        | ~ r2_hidden(X44,X39)
        | r2_hidden(X43,X40)
        | X40 != k10_relat_1(X38,X39)
        | ~ v1_relat_1(X38) )
      & ( ~ r2_hidden(esk5_3(X38,X45,X46),X46)
        | ~ r2_hidden(k4_tarski(esk5_3(X38,X45,X46),X48),X38)
        | ~ r2_hidden(X48,X45)
        | X46 = k10_relat_1(X38,X45)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(k4_tarski(esk5_3(X38,X45,X46),esk6_3(X38,X45,X46)),X38)
        | r2_hidden(esk5_3(X38,X45,X46),X46)
        | X46 = k10_relat_1(X38,X45)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(esk6_3(X38,X45,X46),X45)
        | r2_hidden(esk5_3(X38,X45,X46),X46)
        | X46 = k10_relat_1(X38,X45)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_20,plain,(
    ! [X50,X51,X54,X56,X57] :
      ( ( ~ v1_relat_1(X50)
        | ~ r2_hidden(X51,X50)
        | X51 = k4_tarski(esk7_2(X50,X51),esk8_2(X50,X51)) )
      & ( r2_hidden(esk9_1(X54),X54)
        | v1_relat_1(X54) )
      & ( esk9_1(X54) != k4_tarski(X56,X57)
        | v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(k1_tarski(X2),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_26,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk10_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(esk9_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X18
        | X19 != k1_tarski(X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_tarski(X18) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) != X22
        | X23 = k1_tarski(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) = X22
        | X23 = k1_tarski(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk10_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( X1 = k10_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk5_3(X2,X3,X1),esk6_3(X2,X3,X1)),X2)
    | r2_hidden(esk5_3(X2,X3,X1),X1)
    | r2_hidden(esk9_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_36,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(k1_xboole_0,esk10_0,k1_xboole_0),esk6_3(k1_xboole_0,esk10_0,k1_xboole_0)),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34])]),c_0_35]),c_0_35])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_40,plain,
    ( X1 = X2 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_33,c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.38  # and selection function SelectNegativeLiterals.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t39_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.20/0.38  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.38  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.20/0.38  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.20/0.38  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.38  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.20/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.38  fof(c_0_10, plain, ![X27, X28]:((~r1_tarski(X27,k1_tarski(X28))|(X27=k1_xboole_0|X27=k1_tarski(X28)))&((X27!=k1_xboole_0|r1_tarski(X27,k1_tarski(X28)))&(X27!=k1_tarski(X28)|r1_tarski(X27,k1_tarski(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_11, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_xboole_0(X16,X17)|r1_xboole_0(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.38  cnf(c_0_12, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_13, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.38  cnf(c_0_15, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_16, plain, (r1_tarski(k1_xboole_0,k1_tarski(X1))), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_17, plain, ![X25, X26]:(r2_hidden(X25,X26)|r1_xboole_0(k1_tarski(X25),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_18, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.20/0.38  fof(c_0_19, plain, ![X38, X39, X40, X41, X43, X44, X45, X46, X48]:((((r2_hidden(k4_tarski(X41,esk4_4(X38,X39,X40,X41)),X38)|~r2_hidden(X41,X40)|X40!=k10_relat_1(X38,X39)|~v1_relat_1(X38))&(r2_hidden(esk4_4(X38,X39,X40,X41),X39)|~r2_hidden(X41,X40)|X40!=k10_relat_1(X38,X39)|~v1_relat_1(X38)))&(~r2_hidden(k4_tarski(X43,X44),X38)|~r2_hidden(X44,X39)|r2_hidden(X43,X40)|X40!=k10_relat_1(X38,X39)|~v1_relat_1(X38)))&((~r2_hidden(esk5_3(X38,X45,X46),X46)|(~r2_hidden(k4_tarski(esk5_3(X38,X45,X46),X48),X38)|~r2_hidden(X48,X45))|X46=k10_relat_1(X38,X45)|~v1_relat_1(X38))&((r2_hidden(k4_tarski(esk5_3(X38,X45,X46),esk6_3(X38,X45,X46)),X38)|r2_hidden(esk5_3(X38,X45,X46),X46)|X46=k10_relat_1(X38,X45)|~v1_relat_1(X38))&(r2_hidden(esk6_3(X38,X45,X46),X45)|r2_hidden(esk5_3(X38,X45,X46),X46)|X46=k10_relat_1(X38,X45)|~v1_relat_1(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.38  fof(c_0_20, plain, ![X50, X51, X54, X56, X57]:((~v1_relat_1(X50)|(~r2_hidden(X51,X50)|X51=k4_tarski(esk7_2(X50,X51),esk8_2(X50,X51))))&((r2_hidden(esk9_1(X54),X54)|v1_relat_1(X54))&(esk9_1(X54)!=k4_tarski(X56,X57)|v1_relat_1(X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.20/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_23, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(k1_tarski(X2),X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_25, plain, ![X14]:k4_xboole_0(k1_xboole_0,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.38  fof(c_0_26, negated_conjecture, k10_relat_1(k1_xboole_0,esk10_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.38  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(esk9_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_29, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_31, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  fof(c_0_32, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|X20=X18|X19!=k1_tarski(X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_tarski(X18)))&((~r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)!=X22|X23=k1_tarski(X22))&(r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)=X22|X23=k1_tarski(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (k10_relat_1(k1_xboole_0,esk10_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_34, plain, (X1=k10_relat_1(X2,X3)|r2_hidden(k4_tarski(esk5_3(X2,X3,X1),esk6_3(X2,X3,X1)),X2)|r2_hidden(esk5_3(X2,X3,X1),X1)|r2_hidden(esk9_1(X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_31])).
% 0.20/0.38  cnf(c_0_36, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(k1_xboole_0,esk10_0,k1_xboole_0),esk6_3(k1_xboole_0,esk10_0,k1_xboole_0)),k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34])]), c_0_35]), c_0_35])).
% 0.20/0.38  cnf(c_0_38, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 0.20/0.38  cnf(c_0_40, plain, (X1=X2), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_33, c_0_40]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 42
% 0.20/0.38  # Proof object clause steps            : 21
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 7
% 0.20/0.38  # Proof object clause conjectures      : 4
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 10
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 11
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 28
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 27
% 0.20/0.38  # Processed clauses                    : 106
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 6
% 0.20/0.38  # ...remaining for further processing  : 100
% 0.20/0.38  # Other redundant clauses eliminated   : 13
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 52
% 0.20/0.38  # Generated clauses                    : 228
% 0.20/0.38  # ...of the previous two non-trivial   : 207
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 214
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 13
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
% 0.20/0.38  # Current number of processed clauses  : 10
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 3
% 0.20/0.38  # Current number of unprocessed clauses: 154
% 0.20/0.38  # ...number of literals in the above   : 703
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 84
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 624
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 388
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.20/0.38  # Unit Clause-clause subsumption calls : 18
% 0.20/0.38  # Rewrite failures with RHS unbound    : 42
% 0.20/0.38  # BW rewrite match attempts            : 69
% 0.20/0.38  # BW rewrite match successes           : 66
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6224
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.039 s
% 0.20/0.38  # System time              : 0.001 s
% 0.20/0.38  # Total time               : 0.040 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
