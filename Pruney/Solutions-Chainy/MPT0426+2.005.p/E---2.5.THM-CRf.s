%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 936 expanded)
%              Number of clauses        :   36 ( 436 expanded)
%              Number of leaves         :    6 ( 202 expanded)
%              Depth                    :   13
%              Number of atoms          :  183 (5026 expanded)
%              Number of equality atoms :   74 (1757 expanded)
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

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20,X21,X23,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X19,X20)
        | X18 != k1_setfam_1(X17)
        | X17 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X17,X18,X21),X17)
        | r2_hidden(X21,X18)
        | X18 != k1_setfam_1(X17)
        | X17 = k1_xboole_0 )
      & ( ~ r2_hidden(X21,esk2_3(X17,X18,X21))
        | r2_hidden(X21,X18)
        | X18 != k1_setfam_1(X17)
        | X17 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X17,X23),X17)
        | ~ r2_hidden(esk3_2(X17,X23),X23)
        | X23 = k1_setfam_1(X17)
        | X17 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X17,X23),esk4_2(X17,X23))
        | ~ r2_hidden(esk3_2(X17,X23),X23)
        | X23 = k1_setfam_1(X17)
        | X17 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X17,X23),X23)
        | ~ r2_hidden(X26,X17)
        | r2_hidden(esk3_2(X17,X23),X26)
        | X23 = k1_setfam_1(X17)
        | X17 = k1_xboole_0 )
      & ( X28 != k1_setfam_1(X27)
        | X28 = k1_xboole_0
        | X27 != k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | X29 = k1_setfam_1(X27)
        | X27 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X36] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))
      & r2_hidden(esk6_0,esk5_0)
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) )
      & ( ~ r2_hidden(esk6_0,esk8_0)
        | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) )
      & ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
        | ~ r2_hidden(X36,esk7_0)
        | r2_hidden(esk6_0,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ( X16 = k1_xboole_0
        | k8_setfam_1(X15,X16) = k6_setfam_1(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( X16 != k1_xboole_0
        | k8_setfam_1(X15,X16) = X15
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_11,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30)))
      | k6_setfam_1(X30,X31) = k1_setfam_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk2_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(esk6_0,X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk2_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,esk2_3(esk7_0,k1_setfam_1(esk7_0),X1))
    | r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(X1,k1_setfam_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k6_setfam_1(esk5_0,esk7_0) = k8_setfam_1(esk5_0,esk7_0)
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k6_setfam_1(esk5_0,esk7_0) = k1_setfam_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(esk6_0,k1_setfam_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k8_setfam_1(esk5_0,esk7_0) = k1_setfam_1(esk7_0)
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk8_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,k1_setfam_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(esk6_0,k1_setfam_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r2_hidden(esk6_0,k1_setfam_1(esk7_0))
    | ~ r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk6_0,X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

fof(c_0_34,plain,(
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

cnf(c_0_35,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_39,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_36])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k8_setfam_1(esk5_0,k1_xboole_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_36]),c_0_36]),c_0_43]),c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_46,c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 0.13/0.38  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.13/0.38  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.13/0.38  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.13/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 0.13/0.38  fof(c_0_7, plain, ![X17, X18, X19, X20, X21, X23, X26, X27, X28, X29]:((((~r2_hidden(X19,X18)|(~r2_hidden(X20,X17)|r2_hidden(X19,X20))|X18!=k1_setfam_1(X17)|X17=k1_xboole_0)&((r2_hidden(esk2_3(X17,X18,X21),X17)|r2_hidden(X21,X18)|X18!=k1_setfam_1(X17)|X17=k1_xboole_0)&(~r2_hidden(X21,esk2_3(X17,X18,X21))|r2_hidden(X21,X18)|X18!=k1_setfam_1(X17)|X17=k1_xboole_0)))&(((r2_hidden(esk4_2(X17,X23),X17)|~r2_hidden(esk3_2(X17,X23),X23)|X23=k1_setfam_1(X17)|X17=k1_xboole_0)&(~r2_hidden(esk3_2(X17,X23),esk4_2(X17,X23))|~r2_hidden(esk3_2(X17,X23),X23)|X23=k1_setfam_1(X17)|X17=k1_xboole_0))&(r2_hidden(esk3_2(X17,X23),X23)|(~r2_hidden(X26,X17)|r2_hidden(esk3_2(X17,X23),X26))|X23=k1_setfam_1(X17)|X17=k1_xboole_0)))&((X28!=k1_setfam_1(X27)|X28=k1_xboole_0|X27!=k1_xboole_0)&(X29!=k1_xboole_0|X29=k1_setfam_1(X27)|X27!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ![X36]:(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))&(r2_hidden(esk6_0,esk5_0)&(((r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)))&(~r2_hidden(esk6_0,esk8_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))))&(r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|(~r2_hidden(X36,esk7_0)|r2_hidden(esk6_0,X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.13/0.38  cnf(c_0_9, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_10, plain, ![X15, X16]:((X16=k1_xboole_0|k8_setfam_1(X15,X16)=k6_setfam_1(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&(X16!=k1_xboole_0|k8_setfam_1(X15,X16)=X15|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30)))|k6_setfam_1(X30,X31)=k1_setfam_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk2_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(esk6_0,X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X1,k1_setfam_1(X1),X2),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(er,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_17, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X2,esk2_3(X1,k1_setfam_1(X1),X2))), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,esk2_3(esk7_0,k1_setfam_1(esk7_0),X1))|r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(X1,k1_setfam_1(esk7_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (k6_setfam_1(esk5_0,esk7_0)=k8_setfam_1(esk5_0,esk7_0)|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k6_setfam_1(esk5_0,esk7_0)=k1_setfam_1(esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(esk6_0,k1_setfam_1(esk7_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k8_setfam_1(esk5_0,esk7_0)=k1_setfam_1(esk7_0)|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~r2_hidden(esk6_0,esk8_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_27, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,k1_setfam_1(esk7_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk6_0,k1_setfam_1(esk7_0))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (esk7_0=k1_xboole_0|~r2_hidden(esk6_0,k1_setfam_1(esk7_0))|~r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk6_0,X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk7_0=k1_xboole_0|~r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.13/0.38  fof(c_0_34, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.38  cnf(c_0_35, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.13/0.38  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  fof(c_0_38, plain, ![X14]:k4_xboole_0(k1_xboole_0,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.38  cnf(c_0_39, plain, (k8_setfam_1(X1,k1_xboole_0)=X1|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(er,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))), inference(rw,[status(thm)],[c_0_16, c_0_36])).
% 0.13/0.38  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_42, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k8_setfam_1(esk5_0,k1_xboole_0)=esk5_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_45, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_36]), c_0_36]), c_0_43]), c_0_44])])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_46, c_0_47]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 49
% 0.13/0.38  # Proof object clause steps            : 36
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 13
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 13
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 23
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 23
% 0.13/0.38  # Processed clauses                    : 76
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 74
% 0.13/0.38  # Other redundant clauses eliminated   : 11
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 13
% 0.13/0.38  # Generated clauses                    : 72
% 0.13/0.38  # ...of the previous two non-trivial   : 71
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 60
% 0.13/0.38  # Factorizations                       : 2
% 0.13/0.38  # Equation resolutions                 : 11
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
% 0.13/0.38  # Current number of processed clauses  : 26
% 0.13/0.38  #    Positive orientable unit clauses  : 7
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 17
% 0.13/0.38  # Current number of unprocessed clauses: 39
% 0.13/0.38  # ...number of literals in the above   : 151
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 39
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 275
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 131
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 35
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2846
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
