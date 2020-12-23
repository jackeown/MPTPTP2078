%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:47 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 303 expanded)
%              Number of clauses        :   42 ( 134 expanded)
%              Number of leaves         :    7 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  164 (1310 expanded)
%              Number of equality atoms :   39 ( 299 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> ~ r2_hidden(X4,X3) ) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,X2)
                  <=> ~ r2_hidden(X4,X3) ) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_subset_1])).

fof(c_0_8,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k3_subset_1(X20,X21) = k4_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X29] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & ( ~ r2_hidden(X29,esk4_0)
        | ~ r2_hidden(X29,esk5_0)
        | ~ m1_subset_1(X29,esk3_0) )
      & ( r2_hidden(X29,esk5_0)
        | r2_hidden(X29,esk4_0)
        | ~ m1_subset_1(X29,esk3_0) )
      & esk4_0 != k3_subset_1(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

fof(c_0_10,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | m1_subset_1(k3_subset_1(X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_11,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k3_subset_1(X24,k3_subset_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_14,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k3_subset_1(esk3_0,esk5_0) = k4_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X19,X18)
        | r2_hidden(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ r2_hidden(X19,X18)
        | m1_subset_1(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ m1_subset_1(X19,X18)
        | v1_xboole_0(X19)
        | ~ v1_xboole_0(X18) )
      & ( ~ v1_xboole_0(X19)
        | m1_subset_1(X19,X18)
        | ~ v1_xboole_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])])).

cnf(c_0_22,negated_conjecture,
    ( k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_12])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_21]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(X1,X2) = esk5_0
    | r2_hidden(esk2_3(X1,X2,esk5_0),esk3_0)
    | r2_hidden(esk2_3(X1,X2,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk4_0
    | ~ r2_hidden(esk2_3(esk4_0,X1,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k4_xboole_0(X2,esk4_0)
    | r2_hidden(esk2_3(X2,esk4_0,X1),esk5_0)
    | r2_hidden(esk2_3(X2,esk4_0,X1),X1)
    | ~ r2_hidden(esk2_3(X2,esk4_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = esk5_0
    | r2_hidden(esk2_3(esk3_0,X1,esk5_0),esk3_0) ),
    inference(ef,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_38])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk5_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_44]),c_0_38])])).

cnf(c_0_49,negated_conjecture,
    ( k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_44]),c_0_38])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk5_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 != k3_subset_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_48]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:06:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.94  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.77/0.94  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.77/0.94  #
% 0.77/0.94  # Preprocessing time       : 0.028 s
% 0.77/0.94  
% 0.77/0.94  # Proof found!
% 0.77/0.94  # SZS status Theorem
% 0.77/0.94  # SZS output start CNFRefutation
% 0.77/0.94  fof(t51_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>~(r2_hidden(X4,X3))))=>X2=k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_subset_1)).
% 0.77/0.94  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.77/0.94  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.77/0.94  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.77/0.94  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.77/0.94  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.77/0.94  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.77/0.94  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>~(r2_hidden(X4,X3))))=>X2=k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t51_subset_1])).
% 0.77/0.94  fof(c_0_8, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|k3_subset_1(X20,X21)=k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.77/0.94  fof(c_0_9, negated_conjecture, ![X29]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&(((~r2_hidden(X29,esk4_0)|~r2_hidden(X29,esk5_0)|~m1_subset_1(X29,esk3_0))&(r2_hidden(X29,esk5_0)|r2_hidden(X29,esk4_0)|~m1_subset_1(X29,esk3_0)))&esk4_0!=k3_subset_1(esk3_0,esk5_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).
% 0.77/0.94  fof(c_0_10, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|m1_subset_1(k3_subset_1(X22,X23),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.77/0.94  cnf(c_0_11, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.77/0.94  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.94  fof(c_0_13, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k3_subset_1(X24,k3_subset_1(X24,X25))=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.77/0.94  fof(c_0_14, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.77/0.94  cnf(c_0_15, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.77/0.94  cnf(c_0_16, negated_conjecture, (k3_subset_1(esk3_0,esk5_0)=k4_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.77/0.94  cnf(c_0_17, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.77/0.94  fof(c_0_18, plain, ![X18, X19]:(((~m1_subset_1(X19,X18)|r2_hidden(X19,X18)|v1_xboole_0(X18))&(~r2_hidden(X19,X18)|m1_subset_1(X19,X18)|v1_xboole_0(X18)))&((~m1_subset_1(X19,X18)|v1_xboole_0(X19)|~v1_xboole_0(X18))&(~v1_xboole_0(X19)|m1_subset_1(X19,X18)|~v1_xboole_0(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.77/0.94  fof(c_0_19, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.77/0.94  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.77/0.94  cnf(c_0_21, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])])).
% 0.77/0.94  cnf(c_0_22, negated_conjecture, (k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_16]), c_0_12])])).
% 0.77/0.94  cnf(c_0_23, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.94  cnf(c_0_24, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.94  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_20])).
% 0.77/0.94  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_21]), c_0_22])).
% 0.77/0.94  cnf(c_0_27, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.94  cnf(c_0_28, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.77/0.94  cnf(c_0_29, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.77/0.94  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk5_0)|r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.94  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.77/0.94  cnf(c_0_32, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.77/0.94  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_29])).
% 0.77/0.94  cnf(c_0_34, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.77/0.94  cnf(c_0_35, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.77/0.94  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk4_0)|r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.77/0.94  cnf(c_0_37, negated_conjecture, (k4_xboole_0(X1,X2)=esk5_0|r2_hidden(esk2_3(X1,X2,esk5_0),esk3_0)|r2_hidden(esk2_3(X1,X2,esk5_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.77/0.94  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.94  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.77/0.94  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk4_0,X1)=esk4_0|~r2_hidden(esk2_3(esk4_0,X1,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_31])).
% 0.77/0.94  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_33])).
% 0.77/0.94  cnf(c_0_42, negated_conjecture, (X1=k4_xboole_0(X2,esk4_0)|r2_hidden(esk2_3(X2,esk4_0,X1),esk5_0)|r2_hidden(esk2_3(X2,esk4_0,X1),X1)|~r2_hidden(esk2_3(X2,esk4_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.77/0.94  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk3_0,X1)=esk5_0|r2_hidden(esk2_3(esk3_0,X1,esk5_0),esk3_0)), inference(ef,[status(thm)],[c_0_37])).
% 0.77/0.94  cnf(c_0_44, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_38])).
% 0.77/0.94  cnf(c_0_45, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_39])).
% 0.77/0.94  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.77/0.94  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk5_0|r2_hidden(esk2_3(esk3_0,esk4_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.77/0.94  cnf(c_0_48, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_44]), c_0_38])])).
% 0.77/0.94  cnf(c_0_49, negated_conjecture, (k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_44]), c_0_38])])).
% 0.77/0.94  cnf(c_0_50, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.77/0.94  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk5_0|r2_hidden(esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_43])).
% 0.77/0.94  cnf(c_0_52, negated_conjecture, (esk4_0!=k3_subset_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.94  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_48]), c_0_49])).
% 0.77/0.94  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_47])).
% 0.77/0.94  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)!=esk4_0), inference(rw,[status(thm)],[c_0_52, c_0_16])).
% 0.77/0.94  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_55]), ['proof']).
% 0.77/0.94  # SZS output end CNFRefutation
% 0.77/0.94  # Proof object total steps             : 57
% 0.77/0.94  # Proof object clause steps            : 42
% 0.77/0.94  # Proof object formula steps           : 15
% 0.77/0.94  # Proof object conjectures             : 30
% 0.77/0.94  # Proof object clause conjectures      : 27
% 0.77/0.94  # Proof object formula conjectures     : 3
% 0.77/0.94  # Proof object initial clauses used    : 15
% 0.77/0.94  # Proof object initial formulas used   : 7
% 0.77/0.94  # Proof object generating inferences   : 22
% 0.77/0.94  # Proof object simplifying inferences  : 20
% 0.77/0.94  # Training examples: 0 positive, 0 negative
% 0.77/0.94  # Parsed axioms                        : 7
% 0.77/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.94  # Initial clauses                      : 20
% 0.77/0.94  # Removed in clause preprocessing      : 0
% 0.77/0.94  # Initial clauses in saturation        : 20
% 0.77/0.94  # Processed clauses                    : 10589
% 0.77/0.94  # ...of these trivial                  : 111
% 0.77/0.94  # ...subsumed                          : 9427
% 0.77/0.94  # ...remaining for further processing  : 1051
% 0.77/0.94  # Other redundant clauses eliminated   : 3
% 0.77/0.94  # Clauses deleted for lack of memory   : 0
% 0.77/0.94  # Backward-subsumed                    : 84
% 0.77/0.94  # Backward-rewritten                   : 182
% 0.77/0.94  # Generated clauses                    : 72593
% 0.77/0.94  # ...of the previous two non-trivial   : 53294
% 0.77/0.94  # Contextual simplify-reflections      : 50
% 0.77/0.94  # Paramodulations                      : 72526
% 0.77/0.94  # Factorizations                       : 58
% 0.77/0.94  # Equation resolutions                 : 3
% 0.77/0.94  # Propositional unsat checks           : 0
% 0.77/0.94  #    Propositional check models        : 0
% 0.77/0.94  #    Propositional check unsatisfiable : 0
% 0.77/0.94  #    Propositional clauses             : 0
% 0.77/0.94  #    Propositional clauses after purity: 0
% 0.77/0.94  #    Propositional unsat core size     : 0
% 0.77/0.94  #    Propositional preprocessing time  : 0.000
% 0.77/0.94  #    Propositional encoding time       : 0.000
% 0.77/0.94  #    Propositional solver time         : 0.000
% 0.77/0.94  #    Success case prop preproc time    : 0.000
% 0.77/0.94  #    Success case prop encoding time   : 0.000
% 0.77/0.94  #    Success case prop solver time     : 0.000
% 0.77/0.94  # Current number of processed clauses  : 776
% 0.77/0.94  #    Positive orientable unit clauses  : 79
% 0.77/0.94  #    Positive unorientable unit clauses: 2
% 0.77/0.94  #    Negative unit clauses             : 15
% 0.77/0.94  #    Non-unit-clauses                  : 680
% 0.77/0.94  # Current number of unprocessed clauses: 41082
% 0.77/0.94  # ...number of literals in the above   : 126145
% 0.77/0.94  # Current number of archived formulas  : 0
% 0.77/0.94  # Current number of archived clauses   : 272
% 0.77/0.94  # Clause-clause subsumption calls (NU) : 68231
% 0.77/0.94  # Rec. Clause-clause subsumption calls : 54365
% 0.77/0.94  # Non-unit clause-clause subsumptions  : 4094
% 0.77/0.94  # Unit Clause-clause subsumption calls : 2816
% 0.77/0.94  # Rewrite failures with RHS unbound    : 639
% 0.77/0.94  # BW rewrite match attempts            : 5449
% 0.77/0.94  # BW rewrite match successes           : 274
% 0.77/0.94  # Condensation attempts                : 0
% 0.77/0.94  # Condensation successes               : 0
% 0.77/0.94  # Termbank termtop insertions          : 931297
% 0.77/0.94  
% 0.77/0.94  # -------------------------------------------------
% 0.77/0.94  # User time                : 0.587 s
% 0.77/0.94  # System time              : 0.018 s
% 0.77/0.94  # Total time               : 0.605 s
% 0.77/0.94  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
