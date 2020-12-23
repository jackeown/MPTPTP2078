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
% DateTime   : Thu Dec  3 10:47:48 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 292 expanded)
%              Number of clauses        :   35 ( 134 expanded)
%              Number of leaves         :    7 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 (1599 expanded)
%              Number of equality atoms :   77 ( 556 expanded)
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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
    ! [X10,X11] :
      ( ( X11 = k1_xboole_0
        | k8_setfam_1(X10,X11) = k6_setfam_1(X10,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( X11 != k1_xboole_0
        | k8_setfam_1(X10,X11) = X10
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_12,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | k6_setfam_1(X25,X26) = k1_setfam_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k6_setfam_1(esk4_0,esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k6_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k6_setfam_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(esk5_0,k6_setfam_1(esk4_0,esk6_0))
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

fof(c_0_30,plain,(
    ! [X5,X6] :
      ( ( k2_zfmisc_1(X5,X6) != k1_xboole_0
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0))
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_22])).

fof(c_0_35,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_36,plain,(
    ! [X7,X8] : ~ r2_hidden(X7,k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_34])).

cnf(c_0_41,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_46,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_45]),c_0_45]),c_0_46]),c_0_47])]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:25:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.027 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 0.21/0.39  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.21/0.39  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.21/0.39  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.21/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.39  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.21/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 0.21/0.39  fof(c_0_8, plain, ![X12, X13, X14, X15, X16, X18, X21, X22, X23, X24]:((((~r2_hidden(X14,X13)|(~r2_hidden(X15,X12)|r2_hidden(X14,X15))|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&((r2_hidden(esk1_3(X12,X13,X16),X12)|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(X16,esk1_3(X12,X13,X16))|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)))&(((r2_hidden(esk3_2(X12,X18),X12)|~r2_hidden(esk2_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(esk2_2(X12,X18),esk3_2(X12,X18))|~r2_hidden(esk2_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0))&(r2_hidden(esk2_2(X12,X18),X18)|(~r2_hidden(X21,X12)|r2_hidden(esk2_2(X12,X18),X21))|X18=k1_setfam_1(X12)|X12=k1_xboole_0)))&((X23!=k1_setfam_1(X22)|X23=k1_xboole_0|X22!=k1_xboole_0)&(X24!=k1_xboole_0|X24=k1_setfam_1(X22)|X22!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.21/0.39  fof(c_0_9, negated_conjecture, ![X34]:(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))&(r2_hidden(esk5_0,esk4_0)&(((r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)))&(~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))))&(r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|(~r2_hidden(X34,esk6_0)|r2_hidden(esk5_0,X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).
% 0.21/0.39  cnf(c_0_10, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  fof(c_0_11, plain, ![X10, X11]:((X11=k1_xboole_0|k8_setfam_1(X10,X11)=k6_setfam_1(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))&(X11!=k1_xboole_0|k8_setfam_1(X10,X11)=X10|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.21/0.39  fof(c_0_12, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))|k6_setfam_1(X25,X26)=k1_setfam_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.21/0.39  cnf(c_0_13, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk1_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_14, negated_conjecture, (r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_15, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(er,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_16, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_18, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_19, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2))), inference(er,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(X1,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (k8_setfam_1(esk4_0,esk6_0)=k6_setfam_1(esk4_0,esk6_0)|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (k6_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (~r2_hidden(esk5_0,esk7_0)|~r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (k8_setfam_1(esk4_0,esk6_0)=k1_setfam_1(esk6_0)|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k6_setfam_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (esk6_0=k1_xboole_0|~r2_hidden(esk5_0,k6_setfam_1(esk4_0,esk6_0))|~r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.21/0.39  fof(c_0_30, plain, ![X5, X6]:((k2_zfmisc_1(X5,X6)!=k1_xboole_0|(X5=k1_xboole_0|X6=k1_xboole_0))&((X5!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0)&(X6!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.39  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)|~r2_hidden(esk5_0,k1_setfam_1(esk6_0))), inference(rw,[status(thm)],[c_0_28, c_0_22])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (esk6_0=k1_xboole_0|~r2_hidden(esk5_0,k1_setfam_1(esk6_0))|~r2_hidden(esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_29, c_0_22])).
% 0.21/0.39  fof(c_0_35, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.39  fof(c_0_36, plain, ![X7, X8]:~r2_hidden(X7,k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.21/0.39  cnf(c_0_37, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,X1)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (esk6_0=k1_xboole_0|~r2_hidden(esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_34])).
% 0.21/0.39  cnf(c_0_41, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_42, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.39  cnf(c_0_43, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.39  cnf(c_0_44, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_37])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.21/0.39  cnf(c_0_46, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_42])])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_48, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_45]), c_0_45]), c_0_46]), c_0_47])]), c_0_48]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 50
% 0.21/0.39  # Proof object clause steps            : 35
% 0.21/0.39  # Proof object formula steps           : 15
% 0.21/0.39  # Proof object conjectures             : 23
% 0.21/0.39  # Proof object clause conjectures      : 20
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 14
% 0.21/0.39  # Proof object initial formulas used   : 7
% 0.21/0.39  # Proof object generating inferences   : 12
% 0.21/0.39  # Proof object simplifying inferences  : 18
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 8
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 22
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 22
% 0.21/0.39  # Processed clauses                    : 74
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 4
% 0.21/0.39  # ...remaining for further processing  : 70
% 0.21/0.39  # Other redundant clauses eliminated   : 10
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 3
% 0.21/0.39  # Backward-rewritten                   : 17
% 0.21/0.39  # Generated clauses                    : 46
% 0.21/0.39  # ...of the previous two non-trivial   : 50
% 0.21/0.39  # Contextual simplify-reflections      : 2
% 0.21/0.39  # Paramodulations                      : 38
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 10
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 21
% 0.21/0.39  #    Positive orientable unit clauses  : 8
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 11
% 0.21/0.39  # Current number of unprocessed clauses: 17
% 0.21/0.39  # ...number of literals in the above   : 77
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 41
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 166
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 89
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 7
% 0.21/0.39  # Unit Clause-clause subsumption calls : 25
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 2
% 0.21/0.39  # BW rewrite match successes           : 2
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 2443
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.028 s
% 0.21/0.39  # System time              : 0.006 s
% 0.21/0.39  # Total time               : 0.034 s
% 0.21/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
