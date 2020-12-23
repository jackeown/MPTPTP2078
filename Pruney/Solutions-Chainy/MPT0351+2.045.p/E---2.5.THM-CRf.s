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
% DateTime   : Thu Dec  3 10:45:32 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 613 expanded)
%              Number of clauses        :   32 ( 265 expanded)
%              Number of leaves         :    9 ( 164 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 (1045 expanded)
%              Number of equality atoms :   44 ( 558 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_9,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
      | k4_subset_1(X25,X26,X27) = k2_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_10,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k5_xboole_0(X18,k4_xboole_0(X19,X18)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_11,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t28_subset_1])).

fof(c_0_13,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_14,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_18,plain,(
    ! [X21] : m1_subset_1(k2_subset_1(X21),k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_19,plain,(
    ! [X20] : k2_subset_1(X20) = X20 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_subset_1(X2,X1,X3) = k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_15]),c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))) = k4_subset_1(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_15]),c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0))) = k4_subset_1(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X2,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_29])).

cnf(c_0_34,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_15]),c_0_16])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k4_subset_1(X1,esk3_0,X1) = k4_subset_1(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ r2_hidden(X24,X23)
      | r2_hidden(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk2_0) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_25]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk2_0) = k4_subset_1(esk2_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_23])])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k4_subset_1(X1,X2,X1) = X1
    | r2_hidden(esk1_3(X2,X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k4_subset_1(esk2_0,esk2_0,esk3_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk2_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_23]),c_0_41]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk2_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X1,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_47])]),c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_41]),c_0_23])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:02:59 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.37  #
% 0.11/0.37  # Preprocessing time       : 0.028 s
% 0.11/0.37  # Presaturation interreduction done
% 0.11/0.37  
% 0.11/0.37  # Proof found!
% 0.11/0.37  # SZS status Theorem
% 0.11/0.37  # SZS output start CNFRefutation
% 0.11/0.37  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.11/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.11/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.11/0.37  fof(t28_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 0.11/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.11/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.11/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.11/0.37  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.11/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.11/0.37  fof(c_0_9, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|~m1_subset_1(X27,k1_zfmisc_1(X25))|k4_subset_1(X25,X26,X27)=k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.11/0.37  fof(c_0_10, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k5_xboole_0(X18,k4_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.11/0.37  fof(c_0_11, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.11/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t28_subset_1])).
% 0.11/0.37  fof(c_0_13, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.11/0.37  cnf(c_0_14, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.37  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.37  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.37  fof(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.11/0.37  fof(c_0_18, plain, ![X21]:m1_subset_1(k2_subset_1(X21),k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.11/0.37  fof(c_0_19, plain, ![X20]:k2_subset_1(X20)=X20, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.11/0.37  fof(c_0_20, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.11/0.37  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_22, plain, (k4_subset_1(X2,X1,X3)=k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.11/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.37  cnf(c_0_24, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.37  cnf(c_0_25, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.37  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.37  cnf(c_0_27, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_15]), c_0_15]), c_0_16]), c_0_16])).
% 0.11/0.37  cnf(c_0_28, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))=k4_subset_1(esk2_0,X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.11/0.37  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.11/0.37  cnf(c_0_30, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.37  cnf(c_0_31, plain, (X3=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_15]), c_0_16])).
% 0.11/0.37  cnf(c_0_32, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))=k4_subset_1(esk2_0,X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.11/0.37  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k4_subset_1(X2,X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_29])).
% 0.11/0.37  cnf(c_0_34, plain, (X3=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_15]), c_0_16])).
% 0.11/0.37  cnf(c_0_35, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_31])).
% 0.11/0.37  cnf(c_0_36, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k2_subset_1(esk2_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.37  cnf(c_0_37, negated_conjecture, (k4_subset_1(X1,esk3_0,X1)=k4_subset_1(esk2_0,X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.11/0.37  fof(c_0_38, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~r2_hidden(X24,X23)|r2_hidden(X24,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.11/0.37  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35])).
% 0.11/0.37  cnf(c_0_40, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk2_0)!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_25]), c_0_25])).
% 0.11/0.37  cnf(c_0_41, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk2_0)=k4_subset_1(esk2_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_23])])).
% 0.11/0.37  cnf(c_0_42, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.11/0.37  cnf(c_0_43, plain, (k4_subset_1(X1,X2,X1)=X1|r2_hidden(esk1_3(X2,X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_39])).
% 0.11/0.37  cnf(c_0_44, negated_conjecture, (k4_subset_1(esk2_0,esk2_0,esk3_0)!=esk2_0), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.11/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 0.11/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk2_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_23]), c_0_41]), c_0_44])).
% 0.11/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk2_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.11/0.37  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k4_subset_1(X1,X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_33])).
% 0.11/0.37  cnf(c_0_49, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_47])]), c_0_27])).
% 0.11/0.37  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_41]), c_0_23])]), c_0_44]), ['proof']).
% 0.11/0.37  # SZS output end CNFRefutation
% 0.11/0.37  # Proof object total steps             : 51
% 0.11/0.37  # Proof object clause steps            : 32
% 0.11/0.37  # Proof object formula steps           : 19
% 0.11/0.37  # Proof object conjectures             : 16
% 0.11/0.37  # Proof object clause conjectures      : 13
% 0.11/0.37  # Proof object formula conjectures     : 3
% 0.11/0.37  # Proof object initial clauses used    : 11
% 0.11/0.37  # Proof object initial formulas used   : 9
% 0.11/0.37  # Proof object generating inferences   : 14
% 0.11/0.37  # Proof object simplifying inferences  : 26
% 0.11/0.37  # Training examples: 0 positive, 0 negative
% 0.11/0.37  # Parsed axioms                        : 9
% 0.11/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.37  # Initial clauses                      : 15
% 0.11/0.37  # Removed in clause preprocessing      : 3
% 0.11/0.37  # Initial clauses in saturation        : 12
% 0.11/0.37  # Processed clauses                    : 112
% 0.11/0.37  # ...of these trivial                  : 0
% 0.11/0.37  # ...subsumed                          : 34
% 0.11/0.37  # ...remaining for further processing  : 78
% 0.11/0.37  # Other redundant clauses eliminated   : 3
% 0.11/0.37  # Clauses deleted for lack of memory   : 0
% 0.11/0.37  # Backward-subsumed                    : 2
% 0.11/0.37  # Backward-rewritten                   : 1
% 0.11/0.37  # Generated clauses                    : 452
% 0.11/0.37  # ...of the previous two non-trivial   : 397
% 0.11/0.37  # Contextual simplify-reflections      : 6
% 0.11/0.37  # Paramodulations                      : 443
% 0.11/0.37  # Factorizations                       : 6
% 0.11/0.37  # Equation resolutions                 : 3
% 0.11/0.37  # Propositional unsat checks           : 0
% 0.11/0.37  #    Propositional check models        : 0
% 0.11/0.37  #    Propositional check unsatisfiable : 0
% 0.11/0.37  #    Propositional clauses             : 0
% 0.11/0.37  #    Propositional clauses after purity: 0
% 0.11/0.37  #    Propositional unsat core size     : 0
% 0.11/0.37  #    Propositional preprocessing time  : 0.000
% 0.11/0.37  #    Propositional encoding time       : 0.000
% 0.11/0.37  #    Propositional solver time         : 0.000
% 0.11/0.37  #    Success case prop preproc time    : 0.000
% 0.11/0.37  #    Success case prop encoding time   : 0.000
% 0.11/0.37  #    Success case prop solver time     : 0.000
% 0.11/0.37  # Current number of processed clauses  : 60
% 0.11/0.37  #    Positive orientable unit clauses  : 7
% 0.11/0.37  #    Positive unorientable unit clauses: 1
% 0.11/0.37  #    Negative unit clauses             : 1
% 0.11/0.37  #    Non-unit-clauses                  : 51
% 0.11/0.37  # Current number of unprocessed clauses: 308
% 0.11/0.37  # ...number of literals in the above   : 1361
% 0.11/0.37  # Current number of archived formulas  : 0
% 0.11/0.37  # Current number of archived clauses   : 18
% 0.11/0.37  # Clause-clause subsumption calls (NU) : 413
% 0.11/0.37  # Rec. Clause-clause subsumption calls : 307
% 0.11/0.37  # Non-unit clause-clause subsumptions  : 42
% 0.11/0.37  # Unit Clause-clause subsumption calls : 17
% 0.11/0.37  # Rewrite failures with RHS unbound    : 0
% 0.11/0.37  # BW rewrite match attempts            : 8
% 0.11/0.37  # BW rewrite match successes           : 5
% 0.11/0.37  # Condensation attempts                : 0
% 0.11/0.37  # Condensation successes               : 0
% 0.11/0.37  # Termbank termtop insertions          : 9858
% 0.11/0.37  
% 0.11/0.37  # -------------------------------------------------
% 0.11/0.37  # User time                : 0.042 s
% 0.11/0.37  # System time              : 0.003 s
% 0.11/0.37  # Total time               : 0.044 s
% 0.11/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
