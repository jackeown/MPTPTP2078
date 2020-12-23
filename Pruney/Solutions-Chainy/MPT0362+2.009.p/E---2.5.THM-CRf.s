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
% DateTime   : Thu Dec  3 10:46:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  64 expanded)
%              Number of clauses        :   22 (  29 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 130 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t42_subset_1])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | k9_subset_1(X19,X20,X21) = k3_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_12,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | m1_subset_1(k9_subset_1(X16,X17,X18),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_14,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( k3_subset_1(X1,k9_subset_1(X1,X2,X3)) = k4_xboole_0(X1,k9_subset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

fof(c_0_24,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),k3_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk3_0) = k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k3_subset_1(esk1_0,k9_subset_1(esk1_0,X1,esk3_0)) = k4_xboole_0(esk1_0,k9_subset_1(esk1_0,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_28,plain,(
    ! [X6,X7,X8] :
      ( ( r1_tarski(X6,X7)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),k3_subset_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))) = k4_xboole_0(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_32,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(k4_xboole_0(X11,X10),k4_xboole_0(X11,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.20/0.46  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.028 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t42_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 0.20/0.46  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.46  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.20/0.46  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.46  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.20/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.46  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.46  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.20/0.46  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t42_subset_1])).
% 0.20/0.46  fof(c_0_9, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k3_subset_1(X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.46  fof(c_0_10, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&~r1_tarski(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.46  fof(c_0_11, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X19))|k9_subset_1(X19,X20,X21)=k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.20/0.46  fof(c_0_12, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.46  fof(c_0_13, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X16))|m1_subset_1(k9_subset_1(X16,X17,X18),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.20/0.46  cnf(c_0_14, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.46  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.46  cnf(c_0_16, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.46  cnf(c_0_18, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.46  cnf(c_0_19, negated_conjecture, (~r1_tarski(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.46  cnf(c_0_20, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.46  cnf(c_0_21, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.46  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.46  cnf(c_0_23, plain, (k3_subset_1(X1,k9_subset_1(X1,X2,X3))=k4_xboole_0(X1,k9_subset_1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.20/0.46  fof(c_0_24, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.46  cnf(c_0_25, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,esk2_0),k3_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.46  cnf(c_0_26, negated_conjecture, (k9_subset_1(esk1_0,X1,esk3_0)=k4_xboole_0(X1,k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.46  cnf(c_0_27, negated_conjecture, (k3_subset_1(esk1_0,k9_subset_1(esk1_0,X1,esk3_0))=k4_xboole_0(esk1_0,k9_subset_1(esk1_0,X1,esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.20/0.46  fof(c_0_28, plain, ![X6, X7, X8]:((r1_tarski(X6,X7)|~r1_tarski(X6,k4_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_tarski(X6,k4_xboole_0(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.20/0.46  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_30, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,esk2_0),k3_subset_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.46  cnf(c_0_31, negated_conjecture, (k3_subset_1(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))=k4_xboole_0(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.46  fof(c_0_32, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(k4_xboole_0(X11,X10),k4_xboole_0(X11,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.20/0.46  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.46  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.46  cnf(c_0_35, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.46  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.46  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 39
% 0.20/0.46  # Proof object clause steps            : 22
% 0.20/0.46  # Proof object formula steps           : 17
% 0.20/0.46  # Proof object conjectures             : 14
% 0.20/0.46  # Proof object clause conjectures      : 11
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 10
% 0.20/0.46  # Proof object initial formulas used   : 8
% 0.20/0.46  # Proof object generating inferences   : 7
% 0.20/0.46  # Proof object simplifying inferences  : 7
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 8
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 13
% 0.20/0.46  # Removed in clause preprocessing      : 1
% 0.20/0.46  # Initial clauses in saturation        : 12
% 0.20/0.46  # Processed clauses                    : 461
% 0.20/0.46  # ...of these trivial                  : 64
% 0.20/0.46  # ...subsumed                          : 50
% 0.20/0.46  # ...remaining for further processing  : 347
% 0.20/0.46  # Other redundant clauses eliminated   : 2
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 0
% 0.20/0.46  # Backward-rewritten                   : 3
% 0.20/0.46  # Generated clauses                    : 4174
% 0.20/0.46  # ...of the previous two non-trivial   : 4049
% 0.20/0.46  # Contextual simplify-reflections      : 0
% 0.20/0.46  # Paramodulations                      : 4172
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 2
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 331
% 0.20/0.46  #    Positive orientable unit clauses  : 226
% 0.20/0.46  #    Positive unorientable unit clauses: 2
% 0.20/0.46  #    Negative unit clauses             : 1
% 0.20/0.46  #    Non-unit-clauses                  : 102
% 0.20/0.46  # Current number of unprocessed clauses: 3611
% 0.20/0.46  # ...number of literals in the above   : 4837
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 15
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 1317
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 1317
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 50
% 0.20/0.46  # Unit Clause-clause subsumption calls : 110
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 8889
% 0.20/0.46  # BW rewrite match successes           : 4
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 117075
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.110 s
% 0.20/0.47  # System time              : 0.009 s
% 0.20/0.47  # Total time               : 0.119 s
% 0.20/0.47  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
