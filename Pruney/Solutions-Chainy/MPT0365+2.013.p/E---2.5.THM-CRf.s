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
% DateTime   : Thu Dec  3 10:46:35 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 156 expanded)
%              Number of clauses        :   29 (  63 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 533 expanded)
%              Number of equality atoms :    9 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ( r1_xboole_0(X2,X3)
              & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(t44_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ( r1_xboole_0(X2,X3)
                & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_subset_1])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_xboole_0(X16,k3_subset_1(X15,X17))
        | r1_tarski(X16,X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( ~ r1_tarski(X16,X17)
        | r1_xboole_0(X16,k3_subset_1(X15,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & r1_xboole_0(esk2_0,esk3_0)
    & r1_xboole_0(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0))
    & esk2_0 != k3_subset_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_11,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | r1_tarski(X13,k3_subset_1(X12,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( ~ r1_tarski(X13,k3_subset_1(X12,X14))
        | r1_xboole_0(X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | ~ r2_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r1_xboole_0(X1,k3_subset_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_24,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | ~ r2_xboole_0(X4,X5) )
      & ( X4 != X5
        | ~ r2_xboole_0(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | X4 = X5
        | r2_xboole_0(X4,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_14])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_xboole_0(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r1_xboole_0(X1,k3_subset_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_19]),c_0_16])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk1_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 != k3_subset_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_xboole_0(k3_subset_1(esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:50:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t46_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_xboole_0(X2,X3)&r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)))=>X2=k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 0.12/0.37  fof(t44_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 0.12/0.37  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.12/0.37  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 0.12/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.12/0.37  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.12/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.12/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_xboole_0(X2,X3)&r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)))=>X2=k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t46_subset_1])).
% 0.12/0.37  fof(c_0_8, plain, ![X15, X16, X17]:((~r1_xboole_0(X16,k3_subset_1(X15,X17))|r1_tarski(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))&(~r1_tarski(X16,X17)|r1_xboole_0(X16,k3_subset_1(X15,X17))|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&((r1_xboole_0(esk2_0,esk3_0)&r1_xboole_0(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0)))&esk2_0!=k3_subset_1(esk1_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.37  fof(c_0_10, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.12/0.37  fof(c_0_11, plain, ![X12, X13, X14]:((~r1_xboole_0(X13,X14)|r1_tarski(X13,k3_subset_1(X12,X14))|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))&(~r1_tarski(X13,k3_subset_1(X12,X14))|r1_xboole_0(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.12/0.37  cnf(c_0_13, plain, (r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_15, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_17, plain, (r1_tarski(X1,k3_subset_1(X3,X2))|~r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  fof(c_0_20, plain, ![X8, X9]:(~r1_tarski(X8,X9)|~r2_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))|~r1_xboole_0(X1,k3_subset_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (r1_xboole_0(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  fof(c_0_24, plain, ![X4, X5]:(((r1_tarski(X4,X5)|~r2_xboole_0(X4,X5))&(X4!=X5|~r2_xboole_0(X4,X5)))&(~r1_tarski(X4,X5)|X4=X5|r2_xboole_0(X4,X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_27, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.12/0.37  cnf(c_0_29, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_14])])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~r2_xboole_0(esk3_0,k3_subset_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))|~r1_xboole_0(X1,k3_subset_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_13, c_0_16])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (r1_xboole_0(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_23])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk1_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))|~r1_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (r1_xboole_0(k3_subset_1(esk1_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_34, c_0_33])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_19]), c_0_16])])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_subset_1(esk1_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (esk2_0!=k3_subset_1(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (~r2_xboole_0(k3_subset_1(esk1_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_39])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_41]), c_0_42]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 44
% 0.12/0.37  # Proof object clause steps            : 29
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 26
% 0.12/0.37  # Proof object clause conjectures      : 23
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 11
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 16
% 0.12/0.37  # Proof object simplifying inferences  : 13
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 15
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 15
% 0.12/0.37  # Processed clauses                    : 73
% 0.12/0.37  # ...of these trivial                  : 5
% 0.12/0.37  # ...subsumed                          : 3
% 0.12/0.37  # ...remaining for further processing  : 65
% 0.12/0.37  # Other redundant clauses eliminated   : 1
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 18
% 0.12/0.37  # Generated clauses                    : 158
% 0.12/0.37  # ...of the previous two non-trivial   : 154
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 157
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
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
% 0.12/0.37  # Current number of processed clauses  : 46
% 0.12/0.37  #    Positive orientable unit clauses  : 17
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 26
% 0.12/0.37  # Current number of unprocessed clauses: 88
% 0.12/0.37  # ...number of literals in the above   : 204
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 18
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 24
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 24
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 2
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 23
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4371
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.031 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
