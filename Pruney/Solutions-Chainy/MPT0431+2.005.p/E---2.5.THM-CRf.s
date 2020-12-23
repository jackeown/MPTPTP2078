%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 116 expanded)
%              Number of clauses        :   32 (  50 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 437 expanded)
%              Number of equality atoms :   27 (  49 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d13_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v3_setfam_1(X2,X1)
      <=> ~ r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X19,X20] : k3_tarski(k2_tarski(X19,X20)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | m1_subset_1(k4_subset_1(X21,X22,X23),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v3_setfam_1(esk3_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & v3_setfam_1(esk4_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_13,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | k4_subset_1(X24,X25,X26) = k2_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X27,X28] :
      ( ( ~ v3_setfam_1(X28,X27)
        | ~ r2_hidden(X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) )
      & ( r2_hidden(X27,X28)
        | v3_setfam_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(esk2_0),X1,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_25,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k1_enumset1(X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v3_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k3_tarski(k1_enumset1(X1,X1,esk4_0)) = k4_subset_1(k1_zfmisc_1(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_0,k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0)) = k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k4_xboole_0(X1,k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(X1,k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0)) = k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),X1))
    | r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_41,plain,
    ( ~ v3_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( v3_setfam_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( v3_setfam_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),X1),X2))
    | r2_hidden(esk2_0,X1)
    | r2_hidden(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_17]),c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074I
% 0.21/0.39  # and selection function SelectCQIArEqFirst.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t63_setfam_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 0.21/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.39  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.21/0.39  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.21/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.21/0.39  fof(d13_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v3_setfam_1(X2,X1)<=>~(r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 0.21/0.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1))))), inference(assume_negation,[status(cth)],[t63_setfam_1])).
% 0.21/0.39  fof(c_0_9, plain, ![X19, X20]:k3_tarski(k2_tarski(X19,X20))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.39  fof(c_0_10, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_11, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|~m1_subset_1(X23,k1_zfmisc_1(X21))|m1_subset_1(k4_subset_1(X21,X22,X23),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, (~v1_xboole_0(esk2_0)&((v3_setfam_1(esk3_0,esk2_0)&m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))))&((v3_setfam_1(esk4_0,esk2_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))))&~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.21/0.39  fof(c_0_13, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|~m1_subset_1(X26,k1_zfmisc_1(X24))|k4_subset_1(X24,X25,X26)=k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.21/0.39  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_16, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_18, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_19, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.39  fof(c_0_20, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.21/0.39  fof(c_0_21, plain, ![X27, X28]:((~v3_setfam_1(X28,X27)|~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))))&(r2_hidden(X27,X28)|v3_setfam_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (m1_subset_1(k4_subset_1(k1_zfmisc_1(esk2_0),X1,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  fof(c_0_24, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.39  cnf(c_0_25, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k1_enumset1(X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.39  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_27, plain, (r2_hidden(X1,X2)|v3_setfam_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (k3_tarski(k1_enumset1(X1,X1,esk4_0))=k4_subset_1(k1_zfmisc_1(esk2_0),X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_25, c_0_17])).
% 0.21/0.39  cnf(c_0_32, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_33, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_26])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(esk2_0,k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.21/0.39  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_30, c_0_19])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0))=k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.21/0.39  cnf(c_0_37, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk2_0,k4_xboole_0(X1,k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (k4_xboole_0(X1,k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0))=k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),X1))|r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.21/0.39  cnf(c_0_41, plain, (~v3_setfam_1(X1,X2)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (v3_setfam_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (v3_setfam_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(esk2_0),esk3_0,esk4_0),X1),X2))|r2_hidden(esk2_0,X1)|r2_hidden(esk2_0,X2)), inference(spm,[status(thm)],[c_0_37, c_0_40])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_42])])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_17]), c_0_43])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 49
% 0.21/0.39  # Proof object clause steps            : 32
% 0.21/0.39  # Proof object formula steps           : 17
% 0.21/0.39  # Proof object conjectures             : 21
% 0.21/0.39  # Proof object clause conjectures      : 18
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 14
% 0.21/0.39  # Proof object initial formulas used   : 8
% 0.21/0.39  # Proof object generating inferences   : 12
% 0.21/0.39  # Proof object simplifying inferences  : 13
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 8
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 19
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 17
% 0.21/0.39  # Processed clauses                    : 162
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 9
% 0.21/0.39  # ...remaining for further processing  : 153
% 0.21/0.39  # Other redundant clauses eliminated   : 3
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 785
% 0.21/0.39  # ...of the previous two non-trivial   : 769
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 780
% 0.21/0.39  # Factorizations                       : 2
% 0.21/0.39  # Equation resolutions                 : 3
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
% 0.21/0.39  # Current number of processed clauses  : 132
% 0.21/0.39  #    Positive orientable unit clauses  : 58
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 5
% 0.21/0.39  #    Non-unit-clauses                  : 69
% 0.21/0.39  # Current number of unprocessed clauses: 641
% 0.21/0.39  # ...number of literals in the above   : 886
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 20
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 822
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 793
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 8
% 0.21/0.39  # Unit Clause-clause subsumption calls : 35
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 718
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 27194
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.043 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.048 s
% 0.21/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
