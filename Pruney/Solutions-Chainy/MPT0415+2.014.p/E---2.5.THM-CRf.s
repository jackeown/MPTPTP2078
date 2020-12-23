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
% DateTime   : Thu Dec  3 10:47:40 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  82 expanded)
%              Number of clauses        :   26 (  36 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 277 expanded)
%              Number of equality atoms :   36 (  90 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_10,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k1_xboole_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k3_subset_1(X17,X20),X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X17))
        | X19 != k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( ~ r2_hidden(k3_subset_1(X17,X20),X18)
        | r2_hidden(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X17))
        | X19 != k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(X17))
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(k3_subset_1(X17,esk2_3(X17,X18,X19)),X18)
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X19)
        | r2_hidden(k3_subset_1(X17,esk2_3(X17,X18,X19)),X18)
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_22,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))
      | k7_setfam_1(X22,k7_setfam_1(X22,X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & esk4_0 != k1_xboole_0
    & k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( k7_setfam_1(esk3_0,k1_xboole_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31]),c_0_20])]),c_0_35])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_39]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_31,c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:45:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.028 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.18/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.18/0.37  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.18/0.37  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.18/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.18/0.37  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.18/0.37  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.18/0.37  fof(c_0_9, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.37  fof(c_0_10, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.37  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_14, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.37  fof(c_0_16, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.18/0.37  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.18/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_19, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k1_xboole_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.37  cnf(c_0_20, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  fof(c_0_21, plain, ![X17, X18, X19, X20]:(((~r2_hidden(X20,X19)|r2_hidden(k3_subset_1(X17,X20),X18)|~m1_subset_1(X20,k1_zfmisc_1(X17))|X19!=k7_setfam_1(X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))&(~r2_hidden(k3_subset_1(X17,X20),X18)|r2_hidden(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(X17))|X19!=k7_setfam_1(X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))))&((m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(X17))|X19=k7_setfam_1(X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))&((~r2_hidden(esk2_3(X17,X18,X19),X19)|~r2_hidden(k3_subset_1(X17,esk2_3(X17,X18,X19)),X18)|X19=k7_setfam_1(X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))&(r2_hidden(esk2_3(X17,X18,X19),X19)|r2_hidden(k3_subset_1(X17,esk2_3(X17,X18,X19)),X18)|X19=k7_setfam_1(X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))|~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.18/0.37  fof(c_0_22, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|m1_subset_1(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.18/0.37  fof(c_0_23, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))|k7_setfam_1(X22,k7_setfam_1(X22,X23))=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.18/0.37  fof(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(esk4_0!=k1_xboole_0&k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.18/0.37  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_18])).
% 0.18/0.37  cnf(c_0_26, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.37  cnf(c_0_27, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_28, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.37  cnf(c_0_29, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.37  cnf(c_0_32, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_26])).
% 0.18/0.37  cnf(c_0_33, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X2,k7_setfam_1(X1,X3))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_27, c_0_28])])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (k7_setfam_1(esk3_0,k1_xboole_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.18/0.37  cnf(c_0_35, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.18/0.37  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_37, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_31]), c_0_20])]), c_0_35])).
% 0.18/0.37  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_36])).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk4_0,X1)=esk4_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_39]), c_0_40])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_31, c_0_41]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 43
% 0.18/0.37  # Proof object clause steps            : 26
% 0.18/0.37  # Proof object formula steps           : 17
% 0.18/0.37  # Proof object conjectures             : 12
% 0.18/0.37  # Proof object clause conjectures      : 9
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 12
% 0.18/0.37  # Proof object initial formulas used   : 8
% 0.18/0.37  # Proof object generating inferences   : 10
% 0.18/0.37  # Proof object simplifying inferences  : 13
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 8
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 21
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 21
% 0.18/0.37  # Processed clauses                    : 79
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 8
% 0.18/0.37  # ...remaining for further processing  : 71
% 0.18/0.37  # Other redundant clauses eliminated   : 5
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 2
% 0.18/0.37  # Backward-rewritten                   : 0
% 0.18/0.37  # Generated clauses                    : 99
% 0.18/0.37  # ...of the previous two non-trivial   : 86
% 0.18/0.37  # Contextual simplify-reflections      : 2
% 0.18/0.37  # Paramodulations                      : 91
% 0.18/0.37  # Factorizations                       : 2
% 0.18/0.37  # Equation resolutions                 : 5
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 42
% 0.18/0.37  #    Positive orientable unit clauses  : 6
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 4
% 0.18/0.37  #    Non-unit-clauses                  : 32
% 0.18/0.37  # Current number of unprocessed clauses: 48
% 0.18/0.37  # ...number of literals in the above   : 149
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 24
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 199
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 97
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.18/0.37  # Unit Clause-clause subsumption calls : 64
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 0
% 0.18/0.37  # BW rewrite match successes           : 0
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 3128
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.031 s
% 0.18/0.37  # System time              : 0.004 s
% 0.18/0.37  # Total time               : 0.035 s
% 0.18/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
