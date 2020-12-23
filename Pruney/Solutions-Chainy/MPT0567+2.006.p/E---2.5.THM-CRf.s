%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 118 expanded)
%              Number of clauses        :   22 (  55 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 270 expanded)
%              Number of equality atoms :   46 ( 163 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t171_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

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

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_8,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(k1_tarski(X18),k1_tarski(X19)) != k1_tarski(X18)
        | X18 != X19 )
      & ( X18 = X19
        | k4_xboole_0(k1_tarski(X18),k1_tarski(X19)) = k1_tarski(X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( X16 = X17
      | r1_xboole_0(k1_tarski(X16),k1_tarski(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) = k1_xboole_0
    | X1 = X2 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t171_relat_1])).

cnf(c_0_22,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_tarski(k1_tarski(X1)),k1_tarski(k1_tarski(X1))) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20])])).

fof(c_0_24,plain,(
    ! [X20,X21,X22,X23,X25,X26,X27,X28,X30] :
      ( ( r2_hidden(k4_tarski(X23,esk2_4(X20,X21,X22,X23)),X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k10_relat_1(X20,X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk2_4(X20,X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k10_relat_1(X20,X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X25,X26),X20)
        | ~ r2_hidden(X26,X21)
        | r2_hidden(X25,X22)
        | X22 != k10_relat_1(X20,X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(esk3_3(X20,X27,X28),X28)
        | ~ r2_hidden(k4_tarski(esk3_3(X20,X27,X28),X30),X20)
        | ~ r2_hidden(X30,X27)
        | X28 = k10_relat_1(X20,X27)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk3_3(X20,X27,X28),esk4_3(X20,X27,X28)),X20)
        | r2_hidden(esk3_3(X20,X27,X28),X28)
        | X28 = k10_relat_1(X20,X27)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk4_3(X20,X27,X28),X27)
        | r2_hidden(esk3_3(X20,X27,X28),X28)
        | X28 = k10_relat_1(X20,X27)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k10_relat_1(esk5_0,X2)
    | r2_hidden(esk4_3(esk5_0,X2,X1),X2)
    | r2_hidden(esk3_3(esk5_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k10_relat_1(esk5_0,k1_xboole_0)
    | X2 = X3
    | r2_hidden(esk3_3(esk5_0,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( X1 = X2
    | X3 = X4 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_32]),c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( X1 = X2 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_34])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_33,c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.41  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.20/0.41  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.20/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.41  fof(t171_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 0.20/0.41  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.41  fof(c_0_7, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.41  fof(c_0_8, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.41  fof(c_0_9, plain, ![X18, X19]:((k4_xboole_0(k1_tarski(X18),k1_tarski(X19))!=k1_tarski(X18)|X18!=X19)&(X18=X19|k4_xboole_0(k1_tarski(X18),k1_tarski(X19))=k1_tarski(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_10, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  fof(c_0_12, plain, ![X16, X17]:(X16=X17|r1_xboole_0(k1_tarski(X16),k1_tarski(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.20/0.41  fof(c_0_13, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.41  cnf(c_0_14, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.41  cnf(c_0_16, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_17, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_18, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_19, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X1))!=k1_tarski(X1)), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X1))=k1_xboole_0|X1=X2), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.20/0.41  fof(c_0_21, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t171_relat_1])).
% 0.20/0.41  cnf(c_0_22, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 0.20/0.41  cnf(c_0_23, plain, (k4_xboole_0(k1_tarski(k1_tarski(X1)),k1_tarski(k1_tarski(X1)))=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20])])).
% 0.20/0.41  fof(c_0_24, plain, ![X20, X21, X22, X23, X25, X26, X27, X28, X30]:((((r2_hidden(k4_tarski(X23,esk2_4(X20,X21,X22,X23)),X20)|~r2_hidden(X23,X22)|X22!=k10_relat_1(X20,X21)|~v1_relat_1(X20))&(r2_hidden(esk2_4(X20,X21,X22,X23),X21)|~r2_hidden(X23,X22)|X22!=k10_relat_1(X20,X21)|~v1_relat_1(X20)))&(~r2_hidden(k4_tarski(X25,X26),X20)|~r2_hidden(X26,X21)|r2_hidden(X25,X22)|X22!=k10_relat_1(X20,X21)|~v1_relat_1(X20)))&((~r2_hidden(esk3_3(X20,X27,X28),X28)|(~r2_hidden(k4_tarski(esk3_3(X20,X27,X28),X30),X20)|~r2_hidden(X30,X27))|X28=k10_relat_1(X20,X27)|~v1_relat_1(X20))&((r2_hidden(k4_tarski(esk3_3(X20,X27,X28),esk4_3(X20,X27,X28)),X20)|r2_hidden(esk3_3(X20,X27,X28),X28)|X28=k10_relat_1(X20,X27)|~v1_relat_1(X20))&(r2_hidden(esk4_3(X20,X27,X28),X27)|r2_hidden(esk3_3(X20,X27,X28),X28)|X28=k10_relat_1(X20,X27)|~v1_relat_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.41  fof(c_0_25, negated_conjecture, (v1_relat_1(esk5_0)&k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.41  cnf(c_0_26, plain, (X1=X2|~r2_hidden(X3,k4_xboole_0(k1_tarski(X1),k1_tarski(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17])).
% 0.20/0.41  cnf(c_0_27, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.20/0.41  cnf(c_0_28, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_30, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (X1=k10_relat_1(esk5_0,X2)|r2_hidden(esk4_3(esk5_0,X2,X1),X2)|r2_hidden(esk3_3(esk5_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (X1=k10_relat_1(esk5_0,k1_xboole_0)|X2=X3|r2_hidden(esk3_3(esk5_0,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (X1=X2|X3=X4), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_32]), c_0_33])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (X1=X2), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_34])])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_33, c_0_35]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 37
% 0.20/0.41  # Proof object clause steps            : 22
% 0.20/0.41  # Proof object formula steps           : 15
% 0.20/0.41  # Proof object conjectures             : 10
% 0.20/0.41  # Proof object clause conjectures      : 7
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 9
% 0.20/0.41  # Proof object initial formulas used   : 7
% 0.20/0.41  # Proof object generating inferences   : 8
% 0.20/0.41  # Proof object simplifying inferences  : 10
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 7
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 16
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 15
% 0.20/0.41  # Processed clauses                    : 148
% 0.20/0.41  # ...of these trivial                  : 4
% 0.20/0.41  # ...subsumed                          : 19
% 0.20/0.41  # ...remaining for further processing  : 125
% 0.20/0.41  # Other redundant clauses eliminated   : 132
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 56
% 0.20/0.41  # Backward-rewritten                   : 11
% 0.20/0.41  # Generated clauses                    : 1731
% 0.20/0.41  # ...of the previous two non-trivial   : 1404
% 0.20/0.41  # Contextual simplify-reflections      : 4
% 0.20/0.41  # Paramodulations                      : 1571
% 0.20/0.41  # Factorizations                       : 15
% 0.20/0.41  # Equation resolutions                 : 132
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 26
% 0.20/0.41  #    Positive orientable unit clauses  : 1
% 0.20/0.41  #    Positive unorientable unit clauses: 1
% 0.20/0.41  #    Negative unit clauses             : 0
% 0.20/0.41  #    Non-unit-clauses                  : 24
% 0.20/0.41  # Current number of unprocessed clauses: 1137
% 0.20/0.41  # ...number of literals in the above   : 5214
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 96
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 964
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 404
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 53
% 0.20/0.41  # Unit Clause-clause subsumption calls : 66
% 0.20/0.41  # Rewrite failures with RHS unbound    : 202
% 0.20/0.41  # BW rewrite match attempts            : 167
% 0.20/0.41  # BW rewrite match successes           : 164
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 17958
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.053 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.058 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
