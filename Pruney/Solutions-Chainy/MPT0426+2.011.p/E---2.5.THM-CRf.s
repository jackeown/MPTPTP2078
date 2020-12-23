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
% DateTime   : Thu Dec  3 10:47:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 758 expanded)
%              Number of clauses        :   40 ( 326 expanded)
%              Number of leaves         :    7 ( 187 expanded)
%              Depth                    :   16
%              Number of atoms          :  169 (3335 expanded)
%              Number of equality atoms :   71 (1224 expanded)
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

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

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
    ! [X11,X12,X13,X14,X15,X17,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X13,X12)
        | ~ r2_hidden(X14,X11)
        | r2_hidden(X13,X14)
        | X12 != k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X11,X12,X15),X11)
        | r2_hidden(X15,X12)
        | X12 != k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(X15,esk1_3(X11,X12,X15))
        | r2_hidden(X15,X12)
        | X12 != k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X11,X17),X11)
        | ~ r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X11,X17),esk3_2(X11,X17))
        | ~ r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X11,X17),X17)
        | ~ r2_hidden(X20,X11)
        | r2_hidden(esk2_2(X11,X17),X20)
        | X17 = k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( X22 != k1_setfam_1(X21)
        | X22 = k1_xboole_0
        | X21 != k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | X23 = k1_setfam_1(X21)
        | X21 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( X10 = k1_xboole_0
        | k8_setfam_1(X9,X10) = k6_setfam_1(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) )
      & ( X10 != k1_xboole_0
        | k8_setfam_1(X9,X10) = X9
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_10,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,k1_tarski(X7)) != X6
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(X7,X6)
        | k4_xboole_0(X6,k1_tarski(X7)) = X6 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_13,negated_conjecture,(
    ! [X33] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))
      & r2_hidden(esk5_0,esk4_0)
      & ( r2_hidden(esk7_0,esk6_0)
        | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) )
      & ( ~ r2_hidden(esk5_0,esk7_0)
        | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) )
      & ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
        | ~ r2_hidden(X33,esk6_0)
        | r2_hidden(esk5_0,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | k6_setfam_1(X24,X25) = k1_setfam_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k1_setfam_1(esk6_0),X1),esk6_0)
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k6_setfam_1(esk4_0,esk6_0) = k8_setfam_1(esk4_0,esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k6_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_35]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_0,k1_setfam_1(esk6_0))
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_37])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_41]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_45]),c_0_46]),c_0_46]),c_0_23]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_49]),c_0_46]),c_0_46]),c_0_23]),c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_36]),c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.13/0.38  # and selection function SelectCQIArEqFirst.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 0.13/0.38  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.13/0.38  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.38  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 0.13/0.38  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X17, X20, X21, X22, X23]:((((~r2_hidden(X13,X12)|(~r2_hidden(X14,X11)|r2_hidden(X13,X14))|X12!=k1_setfam_1(X11)|X11=k1_xboole_0)&((r2_hidden(esk1_3(X11,X12,X15),X11)|r2_hidden(X15,X12)|X12!=k1_setfam_1(X11)|X11=k1_xboole_0)&(~r2_hidden(X15,esk1_3(X11,X12,X15))|r2_hidden(X15,X12)|X12!=k1_setfam_1(X11)|X11=k1_xboole_0)))&(((r2_hidden(esk3_2(X11,X17),X11)|~r2_hidden(esk2_2(X11,X17),X17)|X17=k1_setfam_1(X11)|X11=k1_xboole_0)&(~r2_hidden(esk2_2(X11,X17),esk3_2(X11,X17))|~r2_hidden(esk2_2(X11,X17),X17)|X17=k1_setfam_1(X11)|X11=k1_xboole_0))&(r2_hidden(esk2_2(X11,X17),X17)|(~r2_hidden(X20,X11)|r2_hidden(esk2_2(X11,X17),X20))|X17=k1_setfam_1(X11)|X11=k1_xboole_0)))&((X22!=k1_setfam_1(X21)|X22=k1_xboole_0|X21!=k1_xboole_0)&(X23!=k1_xboole_0|X23=k1_setfam_1(X21)|X21!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.13/0.38  fof(c_0_9, plain, ![X9, X10]:((X10=k1_xboole_0|k8_setfam_1(X9,X10)=k6_setfam_1(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))&(X10!=k1_xboole_0|k8_setfam_1(X9,X10)=X9|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X6, X7]:((k4_xboole_0(X6,k1_tarski(X7))!=X6|~r2_hidden(X7,X6))&(r2_hidden(X7,X6)|k4_xboole_0(X6,k1_tarski(X7))=X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X5]:k4_xboole_0(k1_xboole_0,X5)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ![X33]:(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))&(r2_hidden(esk5_0,esk4_0)&(((r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)))&(~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))))&(r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|(~r2_hidden(X33,esk6_0)|r2_hidden(esk5_0,X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_15, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(er,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_16])])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_23, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  fof(c_0_24, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))|k6_setfam_1(X24,X25)=k1_setfam_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk1_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_3(esk6_0,k1_setfam_1(esk6_0),X1),esk6_0)|r2_hidden(X1,k1_setfam_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.13/0.38  cnf(c_0_28, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_30, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2))), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(X1,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k6_setfam_1(esk4_0,esk6_0)=k8_setfam_1(esk4_0,esk6_0)|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k6_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k8_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_35]), c_0_21]), c_0_22])]), c_0_23])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_19, c_0_36])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_0,k1_setfam_1(esk6_0))|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_19, c_0_37])).
% 0.13/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_42, plain, (X1=k1_setfam_1(X2)|X1!=k1_xboole_0|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_41]), c_0_21]), c_0_22])]), c_0_23])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.13/0.38  cnf(c_0_46, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(X1,esk7_0)|~r2_hidden(X1,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_45]), c_0_46]), c_0_46]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_49]), c_0_46]), c_0_46]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_36]), c_0_48])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_21]), c_0_22])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 55
% 0.13/0.38  # Proof object clause steps            : 40
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 27
% 0.13/0.38  # Proof object clause conjectures      : 24
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 36
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 95
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 13
% 0.13/0.38  # ...remaining for further processing  : 82
% 0.13/0.38  # Other redundant clauses eliminated   : 9
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 24
% 0.13/0.38  # Generated clauses                    : 239
% 0.13/0.38  # ...of the previous two non-trivial   : 204
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 230
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 9
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 28
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 18
% 0.13/0.38  # Current number of unprocessed clauses: 145
% 0.13/0.38  # ...number of literals in the above   : 550
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 48
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 389
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 204
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.13/0.38  # Unit Clause-clause subsumption calls : 42
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 5
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5339
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
