%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 283 expanded)
%              Number of clauses        :   31 ( 125 expanded)
%              Number of leaves         :    7 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 (1572 expanded)
%              Number of equality atoms :   66 ( 537 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15,X16,X18,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X14,X15)
        | X13 != k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X12,X13,X16),X12)
        | r2_hidden(X16,X13)
        | X13 != k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( ~ r2_hidden(X16,esk1_3(X12,X13,X16))
        | r2_hidden(X16,X13)
        | X13 != k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X12,X18),X12)
        | ~ r2_hidden(esk2_2(X12,X18),X18)
        | X18 = k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X12,X18),esk3_2(X12,X18))
        | ~ r2_hidden(esk2_2(X12,X18),X18)
        | X18 = k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X12,X18),X18)
        | ~ r2_hidden(X21,X12)
        | r2_hidden(esk2_2(X12,X18),X21)
        | X18 = k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( X23 != k1_setfam_1(X22)
        | X23 = k1_xboole_0
        | X22 != k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | X24 = k1_setfam_1(X22)
        | X22 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X34] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))
      & r2_hidden(esk5_0,esk4_0)
      & ( r2_hidden(esk7_0,esk6_0)
        | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) )
      & ( ~ r2_hidden(esk5_0,esk7_0)
        | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) )
      & ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
        | ~ r2_hidden(X34,esk6_0)
        | r2_hidden(esk5_0,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | k6_setfam_1(X25,X26) = k1_setfam_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ( X11 = k1_xboole_0
        | k8_setfam_1(X10,X11) = k6_setfam_1(X10,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( X11 != k1_xboole_0
        | k8_setfam_1(X10,X11) = X10
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_16,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k6_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0))
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

fof(c_0_31,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_32,plain,(
    ! [X7,X8] : k2_xboole_0(k1_tarski(X7),X8) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | k2_xboole_0(k1_tarski(X5),X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

cnf(c_0_34,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_30])).

cnf(c_0_37,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_41]),c_0_41]),c_0_42]),c_0_43])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:42:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 0.13/0.37  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.13/0.37  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.13/0.37  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.13/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.13/0.37  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 0.13/0.37  fof(c_0_8, plain, ![X12, X13, X14, X15, X16, X18, X21, X22, X23, X24]:((((~r2_hidden(X14,X13)|(~r2_hidden(X15,X12)|r2_hidden(X14,X15))|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&((r2_hidden(esk1_3(X12,X13,X16),X12)|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(X16,esk1_3(X12,X13,X16))|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)))&(((r2_hidden(esk3_2(X12,X18),X12)|~r2_hidden(esk2_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(esk2_2(X12,X18),esk3_2(X12,X18))|~r2_hidden(esk2_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0))&(r2_hidden(esk2_2(X12,X18),X18)|(~r2_hidden(X21,X12)|r2_hidden(esk2_2(X12,X18),X21))|X18=k1_setfam_1(X12)|X12=k1_xboole_0)))&((X23!=k1_setfam_1(X22)|X23=k1_xboole_0|X22!=k1_xboole_0)&(X24!=k1_xboole_0|X24=k1_setfam_1(X22)|X22!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, ![X34]:(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))&(r2_hidden(esk5_0,esk4_0)&(((r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)))&(~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))))&(r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|(~r2_hidden(X34,esk6_0)|r2_hidden(esk5_0,X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).
% 0.13/0.37  cnf(c_0_10, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_11, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))|k6_setfam_1(X25,X26)=k1_setfam_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.13/0.37  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk1_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_14, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(er,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_15, plain, ![X10, X11]:((X11=k1_xboole_0|k8_setfam_1(X10,X11)=k6_setfam_1(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))&(X11!=k1_xboole_0|k8_setfam_1(X10,X11)=X10|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.13/0.37  cnf(c_0_16, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2))), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(X1,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.37  cnf(c_0_20, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (k6_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k8_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_21])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_27, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (esk6_0=k1_xboole_0|~r2_hidden(esk5_0,k1_setfam_1(esk6_0))|~r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.13/0.37  fof(c_0_31, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.37  fof(c_0_32, plain, ![X7, X8]:k2_xboole_0(k1_tarski(X7),X8)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.13/0.37  fof(c_0_33, plain, ![X5, X6]:(~r2_hidden(X5,X6)|k2_xboole_0(k1_tarski(X5),X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (esk6_0=k1_xboole_0|~r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_30])).
% 0.13/0.37  cnf(c_0_37, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_38, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_39, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_40, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.13/0.37  cnf(c_0_42, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_38])])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40])])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_41]), c_0_41]), c_0_42]), c_0_43])]), c_0_44]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 46
% 0.13/0.37  # Proof object clause steps            : 31
% 0.13/0.37  # Proof object formula steps           : 15
% 0.13/0.37  # Proof object conjectures             : 20
% 0.13/0.37  # Proof object clause conjectures      : 17
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 14
% 0.13/0.37  # Proof object initial formulas used   : 7
% 0.13/0.37  # Proof object generating inferences   : 12
% 0.13/0.37  # Proof object simplifying inferences  : 16
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 20
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 20
% 0.13/0.37  # Processed clauses                    : 63
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 62
% 0.13/0.37  # Other redundant clauses eliminated   : 9
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 3
% 0.13/0.37  # Backward-rewritten                   : 14
% 0.13/0.37  # Generated clauses                    : 52
% 0.13/0.37  # ...of the previous two non-trivial   : 52
% 0.13/0.37  # Contextual simplify-reflections      : 2
% 0.13/0.37  # Paramodulations                      : 43
% 0.13/0.37  # Factorizations                       : 2
% 0.13/0.37  # Equation resolutions                 : 9
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 20
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 12
% 0.13/0.37  # Current number of unprocessed clauses: 26
% 0.13/0.37  # ...number of literals in the above   : 129
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 36
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 201
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 88
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.37  # Unit Clause-clause subsumption calls : 10
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2500
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
