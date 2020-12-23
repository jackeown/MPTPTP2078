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
% DateTime   : Thu Dec  3 10:47:58 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 105 expanded)
%              Number of clauses        :   25 (  47 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 297 expanded)
%              Number of equality atoms :   19 (  68 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(t60_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(c_0_7,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ r2_hidden(X14,X13)
      | r2_hidden(X14,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))
      | m1_subset_1(k5_setfam_1(X17,X18),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( m1_setfam_1(X2,X1)
        <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t60_setfam_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ( ~ m1_setfam_1(X16,X15)
        | r1_tarski(X15,k3_tarski(X16)) )
      & ( ~ r1_tarski(X15,k3_tarski(X16))
        | m1_setfam_1(X16,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))
      | k5_setfam_1(X19,X20) = k3_tarski(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & ( ~ m1_setfam_1(esk3_0,esk2_0)
      | k5_setfam_1(esk2_0,esk3_0) != esk2_0 )
    & ( m1_setfam_1(esk3_0,esk2_0)
      | k5_setfam_1(esk2_0,esk3_0) = esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X1,k5_setfam_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(k5_setfam_1(X1,X2),X3),X1)
    | r1_tarski(k5_setfam_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( k3_tarski(X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k3_tarski(esk3_0) = k5_setfam_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(k5_setfam_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k5_setfam_1(esk2_0,esk3_0) = X1
    | ~ m1_setfam_1(esk3_0,X1)
    | ~ r1_tarski(k5_setfam_1(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k5_setfam_1(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_setfam_1(esk3_0,esk2_0)
    | k5_setfam_1(esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( m1_setfam_1(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_setfam_1(esk3_0,esk2_0)
    | k5_setfam_1(esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k5_setfam_1(esk2_0,esk3_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( m1_setfam_1(esk3_0,k5_setfam_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_setfam_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_36]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:36:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.37  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.12/0.37  fof(t60_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.12/0.37  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.12/0.37  fof(c_0_7, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|(~r2_hidden(X14,X13)|r2_hidden(X14,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))|m1_subset_1(k5_setfam_1(X17,X18),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1))), inference(assume_negation,[status(cth)],[t60_setfam_1])).
% 0.12/0.37  cnf(c_0_10, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_12, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  fof(c_0_14, plain, ![X15, X16]:((~m1_setfam_1(X16,X15)|r1_tarski(X15,k3_tarski(X16)))&(~r1_tarski(X15,k3_tarski(X16))|m1_setfam_1(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.12/0.37  fof(c_0_15, plain, ![X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))|k5_setfam_1(X19,X20)=k3_tarski(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.12/0.37  fof(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&((~m1_setfam_1(esk3_0,esk2_0)|k5_setfam_1(esk2_0,esk3_0)!=esk2_0)&(m1_setfam_1(esk3_0,esk2_0)|k5_setfam_1(esk2_0,esk3_0)=esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r2_hidden(X1,k5_setfam_1(X2,X3))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_20, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_24, plain, (r2_hidden(esk1_2(k5_setfam_1(X1,X2),X3),X1)|r1_tarski(k5_setfam_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.37  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_26, plain, (k3_tarski(X1)=X2|~m1_setfam_1(X1,X2)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (k3_tarski(esk3_0)=k5_setfam_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_28, plain, (r1_tarski(k5_setfam_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_29, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (k5_setfam_1(esk2_0,esk3_0)=X1|~m1_setfam_1(esk3_0,X1)|~r1_tarski(k5_setfam_1(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (r1_tarski(k5_setfam_1(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (m1_setfam_1(esk3_0,esk2_0)|k5_setfam_1(esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_34, plain, (m1_setfam_1(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (~m1_setfam_1(esk3_0,esk2_0)|k5_setfam_1(esk2_0,esk3_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k5_setfam_1(esk2_0,esk3_0)=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (m1_setfam_1(esk3_0,k5_setfam_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (~m1_setfam_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_36]), c_0_38]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 40
% 0.12/0.37  # Proof object clause steps            : 25
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 13
% 0.12/0.37  # Proof object clause conjectures      : 10
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 12
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 10
% 0.12/0.37  # Proof object simplifying inferences  : 6
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 14
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 14
% 0.12/0.37  # Processed clauses                    : 44
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 4
% 0.12/0.37  # ...remaining for further processing  : 39
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 11
% 0.12/0.37  # Generated clauses                    : 52
% 0.12/0.37  # ...of the previous two non-trivial   : 44
% 0.12/0.37  # Contextual simplify-reflections      : 1
% 0.12/0.37  # Paramodulations                      : 50
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 26
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 20
% 0.12/0.37  # Current number of unprocessed clauses: 14
% 0.12/0.37  # ...number of literals in the above   : 32
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 11
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 23
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 22
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.37  # Unit Clause-clause subsumption calls : 3
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1607
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
