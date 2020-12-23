%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:38 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 101 expanded)
%              Number of clauses        :   23 (  45 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 204 expanded)
%              Number of equality atoms :    6 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(c_0_8,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_9,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_10,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(k5_relat_1(X19,X17),k5_relat_1(X19,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_26])).

cnf(c_0_30,plain,
    ( v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k1_setfam_1(k2_tarski(X4,k5_relat_1(X1,X3))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),X4) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0))),k1_setfam_1(k2_tarski(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_11]),c_0_11])).

cnf(c_0_35,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k1_setfam_1(k2_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.38/0.55  # and selection function SelectCQPrecWNTNp.
% 0.38/0.55  #
% 0.38/0.55  # Preprocessing time       : 0.047 s
% 0.38/0.55  # Presaturation interreduction done
% 0.38/0.55  
% 0.38/0.55  # Proof found!
% 0.38/0.55  # SZS status Theorem
% 0.38/0.55  # SZS output start CNFRefutation
% 0.38/0.55  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.38/0.55  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.38/0.55  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.38/0.55  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.38/0.55  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.38/0.55  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.38/0.55  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.38/0.55  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.38/0.55  fof(c_0_8, plain, ![X4, X5]:r1_tarski(k3_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.38/0.55  fof(c_0_9, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.38/0.55  cnf(c_0_10, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.38/0.55  cnf(c_0_11, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.38/0.55  fof(c_0_12, plain, ![X9, X10]:k2_tarski(X9,X10)=k2_tarski(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.38/0.55  fof(c_0_13, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.38/0.55  cnf(c_0_14, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.38/0.55  cnf(c_0_15, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.55  fof(c_0_16, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.38/0.55  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.55  cnf(c_0_18, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.38/0.55  fof(c_0_19, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.38/0.55  fof(c_0_20, plain, ![X17, X18, X19]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(X17,X18)|r1_tarski(k5_relat_1(X19,X17),k5_relat_1(X19,X18)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.38/0.55  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.38/0.55  cnf(c_0_22, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.38/0.55  fof(c_0_23, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.38/0.55  cnf(c_0_24, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.55  cnf(c_0_25, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.55  cnf(c_0_26, plain, (v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.38/0.55  fof(c_0_27, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.38/0.55  cnf(c_0_28, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_11])).
% 0.38/0.55  cnf(c_0_29, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k5_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_26])).
% 0.38/0.55  cnf(c_0_30, plain, (v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_15])).
% 0.38/0.55  cnf(c_0_31, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.55  cnf(c_0_32, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k1_setfam_1(k2_tarski(X4,k5_relat_1(X1,X3))))|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),X4)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.38/0.55  cnf(c_0_33, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_30])).
% 0.38/0.55  cnf(c_0_34, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k2_tarski(esk2_0,esk3_0))),k1_setfam_1(k2_tarski(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_11]), c_0_11])).
% 0.38/0.55  cnf(c_0_35, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))),k1_setfam_1(k2_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.38/0.55  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.55  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.55  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.55  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38])]), ['proof']).
% 0.38/0.55  # SZS output end CNFRefutation
% 0.38/0.55  # Proof object total steps             : 40
% 0.38/0.55  # Proof object clause steps            : 23
% 0.38/0.55  # Proof object formula steps           : 17
% 0.38/0.55  # Proof object conjectures             : 9
% 0.38/0.55  # Proof object clause conjectures      : 6
% 0.38/0.55  # Proof object formula conjectures     : 3
% 0.38/0.55  # Proof object initial clauses used    : 11
% 0.38/0.55  # Proof object initial formulas used   : 8
% 0.38/0.55  # Proof object generating inferences   : 9
% 0.38/0.55  # Proof object simplifying inferences  : 10
% 0.38/0.55  # Training examples: 0 positive, 0 negative
% 0.38/0.55  # Parsed axioms                        : 8
% 0.38/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.55  # Initial clauses                      : 12
% 0.38/0.55  # Removed in clause preprocessing      : 1
% 0.38/0.55  # Initial clauses in saturation        : 11
% 0.38/0.55  # Processed clauses                    : 1209
% 0.38/0.55  # ...of these trivial                  : 197
% 0.38/0.55  # ...subsumed                          : 554
% 0.38/0.55  # ...remaining for further processing  : 458
% 0.38/0.55  # Other redundant clauses eliminated   : 0
% 0.38/0.55  # Clauses deleted for lack of memory   : 0
% 0.38/0.55  # Backward-subsumed                    : 0
% 0.38/0.55  # Backward-rewritten                   : 0
% 0.38/0.55  # Generated clauses                    : 14731
% 0.38/0.55  # ...of the previous two non-trivial   : 13431
% 0.38/0.55  # Contextual simplify-reflections      : 19
% 0.38/0.55  # Paramodulations                      : 14731
% 0.38/0.55  # Factorizations                       : 0
% 0.38/0.55  # Equation resolutions                 : 0
% 0.38/0.55  # Propositional unsat checks           : 0
% 0.38/0.55  #    Propositional check models        : 0
% 0.38/0.55  #    Propositional check unsatisfiable : 0
% 0.38/0.55  #    Propositional clauses             : 0
% 0.38/0.55  #    Propositional clauses after purity: 0
% 0.38/0.55  #    Propositional unsat core size     : 0
% 0.38/0.55  #    Propositional preprocessing time  : 0.000
% 0.38/0.55  #    Propositional encoding time       : 0.000
% 0.38/0.55  #    Propositional solver time         : 0.000
% 0.38/0.55  #    Success case prop preproc time    : 0.000
% 0.38/0.55  #    Success case prop encoding time   : 0.000
% 0.38/0.55  #    Success case prop solver time     : 0.000
% 0.38/0.55  # Current number of processed clauses  : 447
% 0.38/0.55  #    Positive orientable unit clauses  : 269
% 0.38/0.55  #    Positive unorientable unit clauses: 1
% 0.38/0.55  #    Negative unit clauses             : 1
% 0.38/0.55  #    Non-unit-clauses                  : 176
% 0.38/0.55  # Current number of unprocessed clauses: 12233
% 0.38/0.55  # ...number of literals in the above   : 13322
% 0.38/0.55  # Current number of archived formulas  : 0
% 0.38/0.55  # Current number of archived clauses   : 12
% 0.38/0.55  # Clause-clause subsumption calls (NU) : 18316
% 0.38/0.55  # Rec. Clause-clause subsumption calls : 16330
% 0.38/0.55  # Non-unit clause-clause subsumptions  : 573
% 0.38/0.55  # Unit Clause-clause subsumption calls : 6100
% 0.38/0.55  # Rewrite failures with RHS unbound    : 0
% 0.38/0.55  # BW rewrite match attempts            : 31678
% 0.38/0.55  # BW rewrite match successes           : 12
% 0.38/0.55  # Condensation attempts                : 0
% 0.38/0.55  # Condensation successes               : 0
% 0.38/0.55  # Termbank termtop insertions          : 293758
% 0.38/0.55  
% 0.38/0.55  # -------------------------------------------------
% 0.38/0.55  # User time                : 0.184 s
% 0.38/0.55  # System time              : 0.016 s
% 0.38/0.55  # Total time               : 0.200 s
% 0.38/0.55  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
