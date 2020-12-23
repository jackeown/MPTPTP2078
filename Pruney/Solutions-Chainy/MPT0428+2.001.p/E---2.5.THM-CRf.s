%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:57 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 145 expanded)
%              Number of clauses        :   31 (  69 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 413 expanded)
%              Number of equality atoms :   30 ( 126 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( m1_setfam_1(X2,X1)
        <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t60_setfam_1])).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ( ~ m1_setfam_1(X20,X19)
        | r1_tarski(X19,k3_tarski(X20)) )
      & ( ~ r1_tarski(X19,k3_tarski(X20))
        | m1_setfam_1(X20,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & ( ~ m1_setfam_1(esk4_0,esk3_0)
      | k5_setfam_1(esk3_0,esk4_0) != esk3_0 )
    & ( m1_setfam_1(esk4_0,esk3_0)
      | k5_setfam_1(esk3_0,esk4_0) = esk3_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | m1_subset_1(k5_setfam_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_setfam_1(esk4_0,esk3_0)
    | k5_setfam_1(esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | k5_setfam_1(X23,X24) = k3_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_16,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k5_setfam_1(esk3_0,esk4_0) = esk3_0
    | r1_tarski(esk3_0,k3_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k5_setfam_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k5_setfam_1(esk3_0,esk4_0) = esk3_0
    | k3_tarski(esk4_0) = esk3_0
    | ~ r1_tarski(k3_tarski(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k3_tarski(esk4_0) = k5_setfam_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k5_setfam_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))
    | v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( k5_setfam_1(esk3_0,esk4_0) = esk3_0
    | ~ r1_tarski(k5_setfam_1(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k5_setfam_1(esk3_0,esk4_0),esk3_0)
    | v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k5_setfam_1(esk3_0,esk4_0) = esk3_0
    | v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( k5_setfam_1(esk3_0,esk4_0) = esk3_0
    | ~ r2_hidden(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( m1_setfam_1(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_setfam_1(esk4_0,esk3_0)
    | k5_setfam_1(esk3_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( k5_setfam_1(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( m1_setfam_1(esk4_0,k5_setfam_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_setfam_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_44]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.14/0.38  # and selection function HSelectMinInfpos.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t60_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.14/0.38  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.14/0.38  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.14/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.38  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.14/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1))), inference(assume_negation,[status(cth)],[t60_setfam_1])).
% 0.14/0.38  fof(c_0_9, plain, ![X19, X20]:((~m1_setfam_1(X20,X19)|r1_tarski(X19,k3_tarski(X20)))&(~r1_tarski(X19,k3_tarski(X20))|m1_setfam_1(X20,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&((~m1_setfam_1(esk4_0,esk3_0)|k5_setfam_1(esk3_0,esk4_0)!=esk3_0)&(m1_setfam_1(esk4_0,esk3_0)|k5_setfam_1(esk3_0,esk4_0)=esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))|m1_subset_1(k5_setfam_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.14/0.38  fof(c_0_12, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.38  cnf(c_0_13, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (m1_setfam_1(esk4_0,esk3_0)|k5_setfam_1(esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_15, plain, ![X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))|k5_setfam_1(X23,X24)=k3_tarski(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.14/0.38  fof(c_0_16, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.38  fof(c_0_17, plain, ![X25, X26]:(~m1_subset_1(X25,X26)|(v1_xboole_0(X26)|r2_hidden(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.38  cnf(c_0_18, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_20, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (k5_setfam_1(esk3_0,esk4_0)=esk3_0|r1_tarski(esk3_0,k3_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_22, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_24, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(k5_setfam_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k5_setfam_1(esk3_0,esk4_0)=esk3_0|k3_tarski(esk4_0)=esk3_0|~r1_tarski(k3_tarski(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (k3_tarski(esk4_0)=k5_setfam_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.14/0.38  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(k5_setfam_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))|v1_xboole_0(k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  fof(c_0_30, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (k5_setfam_1(esk3_0,esk4_0)=esk3_0|~r1_tarski(k5_setfam_1(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27])])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k5_setfam_1(esk3_0,esk4_0),esk3_0)|v1_xboole_0(k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (k5_setfam_1(esk3_0,esk4_0)=esk3_0|v1_xboole_0(k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_39, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k5_setfam_1(esk3_0,esk4_0)=esk3_0|~r2_hidden(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_41, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.38  cnf(c_0_42, plain, (m1_setfam_1(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (~m1_setfam_1(esk4_0,esk3_0)|k5_setfam_1(esk3_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (k5_setfam_1(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (m1_setfam_1(esk4_0,k5_setfam_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~m1_setfam_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_44]), c_0_46]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 48
% 0.14/0.38  # Proof object clause steps            : 31
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 19
% 0.14/0.38  # Proof object clause conjectures      : 16
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 13
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 10
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 18
% 0.14/0.38  # Processed clauses                    : 66
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 5
% 0.14/0.38  # ...remaining for further processing  : 59
% 0.14/0.38  # Other redundant clauses eliminated   : 4
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 15
% 0.14/0.38  # Generated clauses                    : 55
% 0.14/0.38  # ...of the previous two non-trivial   : 55
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 51
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 4
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 22
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 14
% 0.14/0.38  # Current number of unprocessed clauses: 23
% 0.14/0.38  # ...number of literals in the above   : 51
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 34
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 78
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 68
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.38  # Unit Clause-clause subsumption calls : 8
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 6
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1745
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.028 s
% 0.21/0.38  # System time              : 0.005 s
% 0.21/0.38  # Total time               : 0.033 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
