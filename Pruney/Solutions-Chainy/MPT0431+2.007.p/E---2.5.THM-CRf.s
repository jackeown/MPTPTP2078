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
% DateTime   : Thu Dec  3 10:48:06 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   55 (  95 expanded)
%              Number of clauses        :   32 (  40 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 299 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t63_setfam_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v3_setfam_1(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
         => ! [X3] :
              ( ( v3_setfam_1(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d13_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v3_setfam_1(X2,X1)
      <=> ~ r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_11,plain,(
    ! [X11,X12] : k3_tarski(k2_tarski(X11,X12)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | k4_subset_1(X21,X22,X23) = k2_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_17,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v3_setfam_1(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
           => ! [X3] :
                ( ( v3_setfam_1(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_setfam_1])).

cnf(c_0_21,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k1_enumset1(X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v3_setfam_1(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & v3_setfam_1(esk3_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_24,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | m1_subset_1(k4_subset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_25,plain,
    ( k4_subset_1(X1,X2,X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X16,X17] : m1_subset_1(k6_subset_1(X16,X17),k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_29,plain,(
    ! [X24,X25] : k6_subset_1(X24,X25) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_30,plain,(
    ! [X4,X5,X6] :
      ( ( ~ r2_hidden(X4,X5)
        | ~ r2_hidden(X4,X6)
        | ~ r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( r2_hidden(X4,X5)
        | r2_hidden(X4,X6)
        | ~ r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X4,X5)
        | r2_hidden(X4,X6)
        | r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X4,X6)
        | r2_hidden(X4,X5)
        | r2_hidden(X4,k5_xboole_0(X5,X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_31,negated_conjecture,
    ( k5_xboole_0(X1,k4_xboole_0(esk3_0,X1)) = k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X26,X27] :
      ( ( ~ v3_setfam_1(X27,X26)
        | ~ r2_hidden(X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) )
      & ( r2_hidden(X26,X27)
        | v3_setfam_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_35,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ r2_hidden(X20,X19)
      | r2_hidden(X20,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)) = k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | v3_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( ~ v3_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( v3_setfam_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k4_xboole_0(esk3_0,esk2_0))
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_0,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_32]),c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( v3_setfam_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_26]),c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.41/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.41/0.58  # and selection function SelectLComplex.
% 0.41/0.58  #
% 0.41/0.58  # Preprocessing time       : 0.027 s
% 0.41/0.58  # Presaturation interreduction done
% 0.41/0.58  
% 0.41/0.58  # Proof found!
% 0.41/0.58  # SZS status Theorem
% 0.41/0.58  # SZS output start CNFRefutation
% 0.41/0.58  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.41/0.58  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.41/0.58  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.41/0.58  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.41/0.58  fof(t63_setfam_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 0.41/0.58  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.41/0.58  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.41/0.58  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.41/0.58  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.41/0.58  fof(d13_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v3_setfam_1(X2,X1)<=>~(r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 0.41/0.58  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.41/0.58  fof(c_0_11, plain, ![X11, X12]:k3_tarski(k2_tarski(X11,X12))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.41/0.58  fof(c_0_12, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.41/0.58  fof(c_0_13, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|~m1_subset_1(X23,k1_zfmisc_1(X21))|k4_subset_1(X21,X22,X23)=k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.41/0.58  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.41/0.58  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.41/0.58  fof(c_0_16, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k5_xboole_0(X7,k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.41/0.58  cnf(c_0_17, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.41/0.58  cnf(c_0_18, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.41/0.58  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.58  fof(c_0_20, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1))))), inference(assume_negation,[status(cth)],[t63_setfam_1])).
% 0.41/0.58  cnf(c_0_21, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k1_enumset1(X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.41/0.58  cnf(c_0_22, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.41/0.58  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk1_0)&((v3_setfam_1(esk2_0,esk1_0)&m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))))&((v3_setfam_1(esk3_0,esk1_0)&m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))))&~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.41/0.58  fof(c_0_24, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|~m1_subset_1(X15,k1_zfmisc_1(X13))|m1_subset_1(k4_subset_1(X13,X14,X15),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.41/0.58  cnf(c_0_25, plain, (k4_subset_1(X1,X2,X3)=k5_xboole_0(X2,k4_xboole_0(X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.41/0.58  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.41/0.58  cnf(c_0_27, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.41/0.58  fof(c_0_28, plain, ![X16, X17]:m1_subset_1(k6_subset_1(X16,X17),k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.41/0.58  fof(c_0_29, plain, ![X24, X25]:k6_subset_1(X24,X25)=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.41/0.58  fof(c_0_30, plain, ![X4, X5, X6]:(((~r2_hidden(X4,X5)|~r2_hidden(X4,X6)|~r2_hidden(X4,k5_xboole_0(X5,X6)))&(r2_hidden(X4,X5)|r2_hidden(X4,X6)|~r2_hidden(X4,k5_xboole_0(X5,X6))))&((~r2_hidden(X4,X5)|r2_hidden(X4,X6)|r2_hidden(X4,k5_xboole_0(X5,X6)))&(~r2_hidden(X4,X6)|r2_hidden(X4,X5)|r2_hidden(X4,k5_xboole_0(X5,X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.41/0.58  cnf(c_0_31, negated_conjecture, (k5_xboole_0(X1,k4_xboole_0(esk3_0,X1))=k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.41/0.58  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.41/0.58  fof(c_0_33, plain, ![X26, X27]:((~v3_setfam_1(X27,X26)|~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))&(r2_hidden(X26,X27)|v3_setfam_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).
% 0.41/0.58  cnf(c_0_34, negated_conjecture, (m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.41/0.58  fof(c_0_35, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~r2_hidden(X20,X19)|r2_hidden(X20,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.41/0.58  cnf(c_0_36, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.41/0.58  cnf(c_0_37, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.41/0.58  cnf(c_0_38, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.41/0.58  cnf(c_0_39, negated_conjecture, (k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0))=k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.41/0.58  cnf(c_0_40, plain, (r2_hidden(X1,X2)|v3_setfam_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.41/0.58  cnf(c_0_41, negated_conjecture, (m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.41/0.58  cnf(c_0_42, negated_conjecture, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.41/0.58  cnf(c_0_43, plain, (~v3_setfam_1(X1,X2)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.41/0.58  cnf(c_0_44, negated_conjecture, (v3_setfam_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.41/0.58  cnf(c_0_45, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.41/0.58  cnf(c_0_46, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.41/0.58  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,k4_xboole_0(esk3_0,esk2_0))|r2_hidden(X1,esk2_0)|~r2_hidden(X1,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.41/0.58  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_0,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.41/0.58  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_32]), c_0_44])])).
% 0.41/0.58  cnf(c_0_50, negated_conjecture, (v3_setfam_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.41/0.58  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.41/0.58  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_0,k4_xboole_0(esk3_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.41/0.58  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_26]), c_0_50])])).
% 0.41/0.58  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), ['proof']).
% 0.41/0.58  # SZS output end CNFRefutation
% 0.41/0.58  # Proof object total steps             : 55
% 0.41/0.58  # Proof object clause steps            : 32
% 0.41/0.58  # Proof object formula steps           : 23
% 0.41/0.58  # Proof object conjectures             : 18
% 0.41/0.58  # Proof object clause conjectures      : 15
% 0.41/0.58  # Proof object formula conjectures     : 3
% 0.41/0.58  # Proof object initial clauses used    : 16
% 0.41/0.58  # Proof object initial formulas used   : 11
% 0.41/0.58  # Proof object generating inferences   : 11
% 0.41/0.58  # Proof object simplifying inferences  : 12
% 0.41/0.58  # Training examples: 0 positive, 0 negative
% 0.41/0.58  # Parsed axioms                        : 11
% 0.41/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.58  # Initial clauses                      : 20
% 0.41/0.58  # Removed in clause preprocessing      : 3
% 0.41/0.58  # Initial clauses in saturation        : 17
% 0.41/0.58  # Processed clauses                    : 899
% 0.41/0.58  # ...of these trivial                  : 0
% 0.41/0.58  # ...subsumed                          : 41
% 0.41/0.58  # ...remaining for further processing  : 858
% 0.41/0.58  # Other redundant clauses eliminated   : 0
% 0.41/0.58  # Clauses deleted for lack of memory   : 0
% 0.41/0.58  # Backward-subsumed                    : 0
% 0.41/0.58  # Backward-rewritten                   : 0
% 0.41/0.58  # Generated clauses                    : 13784
% 0.41/0.58  # ...of the previous two non-trivial   : 13719
% 0.41/0.58  # Contextual simplify-reflections      : 3
% 0.41/0.58  # Paramodulations                      : 13784
% 0.41/0.58  # Factorizations                       : 0
% 0.41/0.58  # Equation resolutions                 : 0
% 0.41/0.58  # Propositional unsat checks           : 0
% 0.41/0.58  #    Propositional check models        : 0
% 0.41/0.58  #    Propositional check unsatisfiable : 0
% 0.41/0.58  #    Propositional clauses             : 0
% 0.41/0.58  #    Propositional clauses after purity: 0
% 0.41/0.58  #    Propositional unsat core size     : 0
% 0.41/0.58  #    Propositional preprocessing time  : 0.000
% 0.41/0.58  #    Propositional encoding time       : 0.000
% 0.41/0.58  #    Propositional solver time         : 0.000
% 0.41/0.58  #    Success case prop preproc time    : 0.000
% 0.41/0.58  #    Success case prop encoding time   : 0.000
% 0.41/0.58  #    Success case prop solver time     : 0.000
% 0.41/0.58  # Current number of processed clauses  : 841
% 0.41/0.58  #    Positive orientable unit clauses  : 360
% 0.41/0.58  #    Positive unorientable unit clauses: 0
% 0.41/0.58  #    Negative unit clauses             : 4
% 0.41/0.58  #    Non-unit-clauses                  : 477
% 0.41/0.58  # Current number of unprocessed clauses: 12852
% 0.41/0.58  # ...number of literals in the above   : 14363
% 0.41/0.58  # Current number of archived formulas  : 0
% 0.41/0.58  # Current number of archived clauses   : 20
% 0.41/0.58  # Clause-clause subsumption calls (NU) : 74350
% 0.41/0.58  # Rec. Clause-clause subsumption calls : 68172
% 0.41/0.58  # Non-unit clause-clause subsumptions  : 42
% 0.41/0.58  # Unit Clause-clause subsumption calls : 167
% 0.41/0.58  # Rewrite failures with RHS unbound    : 0
% 0.41/0.58  # BW rewrite match attempts            : 31716
% 0.41/0.58  # BW rewrite match successes           : 0
% 0.41/0.58  # Condensation attempts                : 0
% 0.41/0.58  # Condensation successes               : 0
% 0.41/0.58  # Termbank termtop insertions          : 594099
% 0.41/0.58  
% 0.41/0.58  # -------------------------------------------------
% 0.41/0.58  # User time                : 0.213 s
% 0.41/0.58  # System time              : 0.018 s
% 0.41/0.58  # Total time               : 0.231 s
% 0.41/0.58  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
