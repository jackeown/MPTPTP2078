%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  59 expanded)
%              Number of clauses        :   25 (  28 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 233 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t21_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_wellord1)).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] :
      ( ( X16 != X14
        | ~ r2_hidden(X16,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(X16,X14),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( X17 = X14
        | ~ r2_hidden(k4_tarski(X17,X14),X13)
        | r2_hidden(X17,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(esk2_3(X13,X18,X19),X19)
        | esk2_3(X13,X18,X19) = X18
        | ~ r2_hidden(k4_tarski(esk2_3(X13,X18,X19),X18),X13)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( esk2_3(X13,X18,X19) != X18
        | r2_hidden(esk2_3(X13,X18,X19),X19)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_3(X13,X18,X19),X18),X13)
        | r2_hidden(esk2_3(X13,X18,X19),X19)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | k2_wellord1(X21,X22) = k3_xboole_0(X21,k2_zfmisc_1(X22,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k2_wellord1(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_18,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_wellord1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk1_2(k1_wellord1(X1,X2),X3),X2),X1)
    | r1_tarski(k1_wellord1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),X4),X3),X1)
    | r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X4)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t21_wellord1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),X4) = X3
    | r2_hidden(esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),X4),k1_wellord1(X1,X3))
    | r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X4)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & ~ r1_tarski(k1_wellord1(k2_wellord1(esk5_0,esk3_0),esk4_0),k1_wellord1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_29,plain,
    ( esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),k1_wellord1(X1,X3)) = X3
    | r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),k1_wellord1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( X1 != k1_wellord1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(esk5_0,esk3_0),esk4_0),k1_wellord1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_wellord1(k2_wellord1(X2,X3),X1))
    | r1_tarski(k1_wellord1(k2_wellord1(X2,X3),X1),k1_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,k1_wellord1(k2_wellord1(esk5_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_relat_1(k2_wellord1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.40  # and selection function SelectNewComplexAHP.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.027 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.13/0.40  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.13/0.40  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 0.13/0.40  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 0.13/0.40  fof(t21_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_wellord1)).
% 0.13/0.40  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  fof(c_0_7, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.13/0.40  fof(c_0_8, plain, ![X13, X14, X15, X16, X17, X18, X19]:((((X16!=X14|~r2_hidden(X16,X15)|X15!=k1_wellord1(X13,X14)|~v1_relat_1(X13))&(r2_hidden(k4_tarski(X16,X14),X13)|~r2_hidden(X16,X15)|X15!=k1_wellord1(X13,X14)|~v1_relat_1(X13)))&(X17=X14|~r2_hidden(k4_tarski(X17,X14),X13)|r2_hidden(X17,X15)|X15!=k1_wellord1(X13,X14)|~v1_relat_1(X13)))&((~r2_hidden(esk2_3(X13,X18,X19),X19)|(esk2_3(X13,X18,X19)=X18|~r2_hidden(k4_tarski(esk2_3(X13,X18,X19),X18),X13))|X19=k1_wellord1(X13,X18)|~v1_relat_1(X13))&((esk2_3(X13,X18,X19)!=X18|r2_hidden(esk2_3(X13,X18,X19),X19)|X19=k1_wellord1(X13,X18)|~v1_relat_1(X13))&(r2_hidden(k4_tarski(esk2_3(X13,X18,X19),X18),X13)|r2_hidden(esk2_3(X13,X18,X19),X19)|X19=k1_wellord1(X13,X18)|~v1_relat_1(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.13/0.40  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_10, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  fof(c_0_11, plain, ![X21, X22]:(~v1_relat_1(X21)|k2_wellord1(X21,X22)=k3_xboole_0(X21,k2_zfmisc_1(X22,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.13/0.40  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.40  cnf(c_0_14, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  fof(c_0_17, plain, ![X23, X24]:(~v1_relat_1(X23)|v1_relat_1(k2_wellord1(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 0.13/0.40  cnf(c_0_18, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~v1_relat_1(X2)|~r2_hidden(X1,k2_wellord1(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.40  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk1_2(k1_wellord1(X1,X2),X3),X2),X1)|r1_tarski(k1_wellord1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.40  cnf(c_0_21, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_22, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),X4),X3),X1)|r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X4)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.13/0.40  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k1_wellord1(k2_wellord1(X3,X1),X2),k1_wellord1(X3,X2)))), inference(assume_negation,[status(cth)],[t21_wellord1])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_26, plain, (esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),X4)=X3|r2_hidden(esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),X4),k1_wellord1(X1,X3))|r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),X4)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.40  cnf(c_0_27, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  fof(c_0_28, negated_conjecture, (v1_relat_1(esk5_0)&~r1_tarski(k1_wellord1(k2_wellord1(esk5_0,esk3_0),esk4_0),k1_wellord1(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.13/0.40  cnf(c_0_29, plain, (esk1_2(k1_wellord1(k2_wellord1(X1,X2),X3),k1_wellord1(X1,X3))=X3|r1_tarski(k1_wellord1(k2_wellord1(X1,X2),X3),k1_wellord1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.40  cnf(c_0_30, plain, (X1!=k1_wellord1(X2,X3)|~v1_relat_1(X2)|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (~r1_tarski(k1_wellord1(k2_wellord1(esk5_0,esk3_0),esk4_0),k1_wellord1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_32, plain, (r2_hidden(X1,k1_wellord1(k2_wellord1(X2,X3),X1))|r1_tarski(k1_wellord1(k2_wellord1(X2,X3),X1),k1_wellord1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_16, c_0_29])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_34, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,k1_wellord1(k2_wellord1(esk5_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (~v1_relat_1(k2_wellord1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_33])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 38
% 0.13/0.40  # Proof object clause steps            : 25
% 0.13/0.40  # Proof object formula steps           : 13
% 0.13/0.40  # Proof object conjectures             : 8
% 0.13/0.40  # Proof object clause conjectures      : 5
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 11
% 0.13/0.40  # Proof object initial formulas used   : 6
% 0.13/0.40  # Proof object generating inferences   : 13
% 0.13/0.40  # Proof object simplifying inferences  : 6
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 6
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 14
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 14
% 0.13/0.40  # Processed clauses                    : 230
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 87
% 0.13/0.40  # ...remaining for further processing  : 143
% 0.13/0.40  # Other redundant clauses eliminated   : 1
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 9
% 0.13/0.40  # Backward-rewritten                   : 0
% 0.13/0.40  # Generated clauses                    : 884
% 0.13/0.40  # ...of the previous two non-trivial   : 876
% 0.13/0.40  # Contextual simplify-reflections      : 25
% 0.13/0.40  # Paramodulations                      : 876
% 0.13/0.40  # Factorizations                       : 4
% 0.13/0.40  # Equation resolutions                 : 4
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 133
% 0.13/0.40  #    Positive orientable unit clauses  : 9
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 122
% 0.13/0.40  # Current number of unprocessed clauses: 660
% 0.13/0.40  # ...number of literals in the above   : 2706
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 9
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 6375
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 4058
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 121
% 0.13/0.40  # Unit Clause-clause subsumption calls : 39
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 29
% 0.13/0.40  # BW rewrite match successes           : 0
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 21766
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.056 s
% 0.13/0.40  # System time              : 0.003 s
% 0.13/0.40  # Total time               : 0.059 s
% 0.13/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
