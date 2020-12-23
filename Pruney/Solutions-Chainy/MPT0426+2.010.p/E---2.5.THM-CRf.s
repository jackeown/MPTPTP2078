%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 764 expanded)
%              Number of clauses        :   39 ( 332 expanded)
%              Number of leaves         :    7 ( 184 expanded)
%              Depth                    :   18
%              Number of atoms          :  170 (3183 expanded)
%              Number of equality atoms :   69 (1000 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t58_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ( r2_hidden(X6,X7)
        | ~ r2_hidden(X6,k4_xboole_0(X7,k1_tarski(X8))) )
      & ( X6 != X8
        | ~ r2_hidden(X6,k4_xboole_0(X7,k1_tarski(X8))) )
      & ( ~ r2_hidden(X6,X7)
        | X6 = X8
        | r2_hidden(X6,k4_xboole_0(X7,k1_tarski(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ( X11 = k1_xboole_0
        | k8_setfam_1(X10,X11) = k6_setfam_1(X10,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( X11 != k1_xboole_0
        | k8_setfam_1(X10,X11) = X10
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_11,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_12,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_14,negated_conjecture,(
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k1_setfam_1(esk6_0),X1),esk6_0)
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | k6_setfam_1(X25,X26) = k1_setfam_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k6_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_33]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_38]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_42]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_47]),c_0_48]),c_0_48]),c_0_24]),c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_52,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_22]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.20/0.50  # and selection function SelectCQIArEqFirst.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.027 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.50  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 0.20/0.50  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.20/0.50  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.20/0.50  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.50  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.50  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.20/0.50  fof(c_0_7, plain, ![X6, X7, X8]:(((r2_hidden(X6,X7)|~r2_hidden(X6,k4_xboole_0(X7,k1_tarski(X8))))&(X6!=X8|~r2_hidden(X6,k4_xboole_0(X7,k1_tarski(X8)))))&(~r2_hidden(X6,X7)|X6=X8|r2_hidden(X6,k4_xboole_0(X7,k1_tarski(X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.50  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 0.20/0.50  fof(c_0_9, plain, ![X12, X13, X14, X15, X16, X18, X21, X22, X23, X24]:((((~r2_hidden(X14,X13)|(~r2_hidden(X15,X12)|r2_hidden(X14,X15))|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&((r2_hidden(esk1_3(X12,X13,X16),X12)|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(X16,esk1_3(X12,X13,X16))|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)))&(((r2_hidden(esk3_2(X12,X18),X12)|~r2_hidden(esk2_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(esk2_2(X12,X18),esk3_2(X12,X18))|~r2_hidden(esk2_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0))&(r2_hidden(esk2_2(X12,X18),X18)|(~r2_hidden(X21,X12)|r2_hidden(esk2_2(X12,X18),X21))|X18=k1_setfam_1(X12)|X12=k1_xboole_0)))&((X23!=k1_setfam_1(X22)|X23=k1_xboole_0|X22!=k1_xboole_0)&(X24!=k1_xboole_0|X24=k1_setfam_1(X22)|X22!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.20/0.50  fof(c_0_10, plain, ![X10, X11]:((X11=k1_xboole_0|k8_setfam_1(X10,X11)=k6_setfam_1(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))&(X11!=k1_xboole_0|k8_setfam_1(X10,X11)=X10|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.20/0.50  fof(c_0_11, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.50  cnf(c_0_12, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.50  fof(c_0_13, plain, ![X5]:k4_xboole_0(k1_xboole_0,X5)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.50  fof(c_0_14, negated_conjecture, ![X34]:(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))&(r2_hidden(esk5_0,esk4_0)&(((r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)))&(~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))))&(r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|(~r2_hidden(X34,esk6_0)|r2_hidden(esk5_0,X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).
% 0.20/0.50  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_16, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  cnf(c_0_17, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_18, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_19, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.50  cnf(c_0_20, negated_conjecture, (r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.50  cnf(c_0_22, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_17])])).
% 0.20/0.50  cnf(c_0_23, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_24, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.50  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk1_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_26, negated_conjecture, (r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_3(esk6_0,k1_setfam_1(esk6_0),X1),esk6_0)|r2_hidden(X1,k1_setfam_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.50  fof(c_0_28, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))|k6_setfam_1(X25,X26)=k1_setfam_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.20/0.50  cnf(c_0_29, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2))), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.50  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(X1,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.50  cnf(c_0_31, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_33, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.50  cnf(c_0_34, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  cnf(c_0_35, negated_conjecture, (k6_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.50  cnf(c_0_36, negated_conjecture, (r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_33]), c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.50  cnf(c_0_37, negated_conjecture, (k8_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_35])).
% 0.20/0.50  cnf(c_0_38, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.50  cnf(c_0_39, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_20, c_0_37])).
% 0.20/0.50  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_38]), c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.50  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_42, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.20/0.50  cnf(c_0_43, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.50  cnf(c_0_44, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_42]), c_0_22]), c_0_23])]), c_0_24])).
% 0.20/0.50  cnf(c_0_45, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(X1,esk7_0)|~r2_hidden(X1,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.50  cnf(c_0_46, plain, (X1=k1_setfam_1(X2)|X1!=k1_xboole_0|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_47, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.20/0.50  cnf(c_0_48, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.20/0.50  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_47]), c_0_48]), c_0_48]), c_0_24]), c_0_24])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.20/0.50  cnf(c_0_52, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_37]), c_0_40])])).
% 0.20/0.50  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_22]), c_0_23])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 54
% 0.20/0.50  # Proof object clause steps            : 39
% 0.20/0.50  # Proof object formula steps           : 15
% 0.20/0.50  # Proof object conjectures             : 25
% 0.20/0.50  # Proof object clause conjectures      : 22
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 15
% 0.20/0.50  # Proof object initial formulas used   : 7
% 0.20/0.50  # Proof object generating inferences   : 15
% 0.20/0.50  # Proof object simplifying inferences  : 40
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 8
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 22
% 0.20/0.50  # Removed in clause preprocessing      : 0
% 0.20/0.50  # Initial clauses in saturation        : 22
% 0.20/0.50  # Processed clauses                    : 848
% 0.20/0.50  # ...of these trivial                  : 0
% 0.20/0.50  # ...subsumed                          : 598
% 0.20/0.50  # ...remaining for further processing  : 250
% 0.20/0.50  # Other redundant clauses eliminated   : 9
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 10
% 0.20/0.50  # Backward-rewritten                   : 111
% 0.20/0.50  # Generated clauses                    : 7916
% 0.20/0.50  # ...of the previous two non-trivial   : 7537
% 0.20/0.50  # Contextual simplify-reflections      : 4
% 0.20/0.50  # Paramodulations                      : 7908
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 9
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 100
% 0.20/0.50  #    Positive orientable unit clauses  : 9
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 2
% 0.20/0.50  #    Non-unit-clauses                  : 89
% 0.20/0.50  # Current number of unprocessed clauses: 6698
% 0.20/0.50  # ...number of literals in the above   : 33296
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 143
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 12485
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 4133
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 584
% 0.20/0.50  # Unit Clause-clause subsumption calls : 469
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 4
% 0.20/0.50  # BW rewrite match successes           : 4
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 155009
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.154 s
% 0.20/0.50  # System time              : 0.005 s
% 0.20/0.50  # Total time               : 0.159 s
% 0.20/0.50  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
