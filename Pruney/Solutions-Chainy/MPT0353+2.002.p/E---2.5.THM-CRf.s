%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:42 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 164 expanded)
%              Number of clauses        :   41 (  75 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 440 expanded)
%              Number of equality atoms :   61 ( 189 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_subset_1])).

fof(c_0_12,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k3_subset_1(X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_13,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | k9_subset_1(X33,X34,X35) = k3_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & k7_subset_1(esk2_0,esk3_0,esk4_0) != k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | ~ r2_hidden(X29,X28)
      | r2_hidden(X29,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k9_subset_1(X22,X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k7_subset_1(X30,X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_23,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk3_0) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_30,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X19,X20,X21] : k5_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X21,X20)) = k3_xboole_0(k5_xboole_0(X19,X21),X20) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k7_subset_1(esk2_0,esk3_0,esk4_0) != k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k3_subset_1(esk2_0,esk4_0) = k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k9_subset_1(esk2_0,esk3_0,X1) = k3_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_28])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X16] : k3_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_42,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 = k3_xboole_0(X1,X2)
    | r2_hidden(esk1_3(X1,X2,esk4_0),esk2_0)
    | r2_hidden(esk1_3(X1,X2,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( k7_subset_1(esk2_0,esk3_0,esk4_0) != k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k7_subset_1(esk2_0,esk3_0,X1) = k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = k3_xboole_0(esk2_0,X1)
    | r2_hidden(esk1_3(esk2_0,X1,esk4_0),esk2_0) ),
    inference(ef,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( esk3_0 = k3_xboole_0(X1,X2)
    | r2_hidden(esk1_3(X1,X2,esk3_0),esk2_0)
    | r2_hidden(esk1_3(X1,X2,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 = k3_xboole_0(esk2_0,X1)
    | r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk2_0) ),
    inference(ef,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0)) = k5_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_56])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_49]),c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1)) = k3_xboole_0(k5_xboole_0(esk2_0,X1),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_59]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.18/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.41  #
% 0.18/0.41  # Preprocessing time       : 0.027 s
% 0.18/0.41  # Presaturation interreduction done
% 0.18/0.41  
% 0.18/0.41  # Proof found!
% 0.18/0.41  # SZS status Theorem
% 0.18/0.41  # SZS output start CNFRefutation
% 0.18/0.41  fof(t32_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.18/0.41  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.18/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.41  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.18/0.41  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.18/0.41  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.18/0.41  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.18/0.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.18/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.41  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.18/0.41  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.18/0.41  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t32_subset_1])).
% 0.18/0.41  fof(c_0_12, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k3_subset_1(X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.18/0.41  fof(c_0_13, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.41  fof(c_0_14, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X33))|k9_subset_1(X33,X34,X35)=k3_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.18/0.41  fof(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&k7_subset_1(esk2_0,esk3_0,esk4_0)!=k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.18/0.41  fof(c_0_16, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|(~r2_hidden(X29,X28)|r2_hidden(X29,X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.18/0.41  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.41  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.41  fof(c_0_19, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X22))|k9_subset_1(X22,X23,X24)=k9_subset_1(X22,X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.18/0.41  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.41  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.41  fof(c_0_22, plain, ![X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k7_subset_1(X30,X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.18/0.41  fof(c_0_23, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.18/0.41  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.41  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.41  cnf(c_0_26, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.41  cnf(c_0_27, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.41  cnf(c_0_28, negated_conjecture, (k9_subset_1(esk2_0,X1,esk3_0)=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.41  fof(c_0_29, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.41  cnf(c_0_30, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.41  fof(c_0_31, plain, ![X19, X20, X21]:k5_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X21,X20))=k3_xboole_0(k5_xboole_0(X19,X21),X20), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.18/0.41  cnf(c_0_32, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.41  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.41  cnf(c_0_35, negated_conjecture, (k7_subset_1(esk2_0,esk3_0,esk4_0)!=k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.41  cnf(c_0_36, negated_conjecture, (k3_subset_1(esk2_0,esk4_0)=k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.18/0.41  cnf(c_0_37, negated_conjecture, (k9_subset_1(esk2_0,esk3_0,X1)=k3_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_28])).
% 0.18/0.41  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.41  cnf(c_0_39, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_30, c_0_18])).
% 0.18/0.41  cnf(c_0_40, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.41  fof(c_0_41, plain, ![X16]:k3_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.18/0.41  cnf(c_0_42, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.41  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_32])).
% 0.18/0.41  cnf(c_0_44, negated_conjecture, (esk4_0=k3_xboole_0(X1,X2)|r2_hidden(esk1_3(X1,X2,esk4_0),esk2_0)|r2_hidden(esk1_3(X1,X2,esk4_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.41  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.18/0.41  cnf(c_0_46, negated_conjecture, (k7_subset_1(esk2_0,esk3_0,esk4_0)!=k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])).
% 0.18/0.41  cnf(c_0_47, negated_conjecture, (k7_subset_1(esk2_0,esk3_0,X1)=k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_39, c_0_21])).
% 0.18/0.41  cnf(c_0_48, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.18/0.41  cnf(c_0_49, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.41  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_43])).
% 0.18/0.41  cnf(c_0_51, negated_conjecture, (esk4_0=k3_xboole_0(esk2_0,X1)|r2_hidden(esk1_3(esk2_0,X1,esk4_0),esk2_0)), inference(ef,[status(thm)],[c_0_44])).
% 0.18/0.41  cnf(c_0_52, negated_conjecture, (esk3_0=k3_xboole_0(X1,X2)|r2_hidden(esk1_3(X1,X2,esk3_0),esk2_0)|r2_hidden(esk1_3(X1,X2,esk3_0),X1)), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 0.18/0.41  cnf(c_0_53, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.41  cnf(c_0_54, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38])).
% 0.18/0.41  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.41  cnf(c_0_56, negated_conjecture, (esk3_0=k3_xboole_0(esk2_0,X1)|r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk2_0)), inference(ef,[status(thm)],[c_0_52])).
% 0.18/0.41  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_54])).
% 0.18/0.41  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0))=k5_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.41  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_50, c_0_56])).
% 0.18/0.41  cnf(c_0_60, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_49]), c_0_38])).
% 0.18/0.41  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.18/0.41  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1))=k3_xboole_0(k5_xboole_0(esk2_0,X1),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_59]), c_0_60])).
% 0.18/0.41  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_38])]), ['proof']).
% 0.18/0.41  # SZS output end CNFRefutation
% 0.18/0.41  # Proof object total steps             : 64
% 0.18/0.41  # Proof object clause steps            : 41
% 0.18/0.41  # Proof object formula steps           : 23
% 0.18/0.41  # Proof object conjectures             : 25
% 0.18/0.41  # Proof object clause conjectures      : 22
% 0.18/0.41  # Proof object formula conjectures     : 3
% 0.18/0.41  # Proof object initial clauses used    : 15
% 0.18/0.41  # Proof object initial formulas used   : 11
% 0.18/0.41  # Proof object generating inferences   : 19
% 0.18/0.41  # Proof object simplifying inferences  : 17
% 0.18/0.41  # Training examples: 0 positive, 0 negative
% 0.18/0.41  # Parsed axioms                        : 11
% 0.18/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.41  # Initial clauses                      : 18
% 0.18/0.41  # Removed in clause preprocessing      : 1
% 0.18/0.41  # Initial clauses in saturation        : 17
% 0.18/0.41  # Processed clauses                    : 438
% 0.18/0.41  # ...of these trivial                  : 51
% 0.18/0.41  # ...subsumed                          : 203
% 0.18/0.41  # ...remaining for further processing  : 184
% 0.18/0.41  # Other redundant clauses eliminated   : 3
% 0.18/0.41  # Clauses deleted for lack of memory   : 0
% 0.18/0.41  # Backward-subsumed                    : 0
% 0.18/0.41  # Backward-rewritten                   : 23
% 0.18/0.41  # Generated clauses                    : 3431
% 0.18/0.41  # ...of the previous two non-trivial   : 3119
% 0.18/0.41  # Contextual simplify-reflections      : 1
% 0.18/0.41  # Paramodulations                      : 3384
% 0.18/0.41  # Factorizations                       : 44
% 0.18/0.41  # Equation resolutions                 : 3
% 0.18/0.41  # Propositional unsat checks           : 0
% 0.18/0.41  #    Propositional check models        : 0
% 0.18/0.41  #    Propositional check unsatisfiable : 0
% 0.18/0.41  #    Propositional clauses             : 0
% 0.18/0.41  #    Propositional clauses after purity: 0
% 0.18/0.41  #    Propositional unsat core size     : 0
% 0.18/0.41  #    Propositional preprocessing time  : 0.000
% 0.18/0.41  #    Propositional encoding time       : 0.000
% 0.18/0.41  #    Propositional solver time         : 0.000
% 0.18/0.41  #    Success case prop preproc time    : 0.000
% 0.18/0.41  #    Success case prop encoding time   : 0.000
% 0.18/0.41  #    Success case prop solver time     : 0.000
% 0.18/0.41  # Current number of processed clauses  : 141
% 0.18/0.41  #    Positive orientable unit clauses  : 52
% 0.18/0.41  #    Positive unorientable unit clauses: 4
% 0.18/0.41  #    Negative unit clauses             : 0
% 0.18/0.41  #    Non-unit-clauses                  : 85
% 0.18/0.41  # Current number of unprocessed clauses: 2709
% 0.18/0.41  # ...number of literals in the above   : 6124
% 0.18/0.41  # Current number of archived formulas  : 0
% 0.18/0.41  # Current number of archived clauses   : 41
% 0.18/0.41  # Clause-clause subsumption calls (NU) : 3426
% 0.18/0.41  # Rec. Clause-clause subsumption calls : 2516
% 0.18/0.41  # Non-unit clause-clause subsumptions  : 163
% 0.18/0.41  # Unit Clause-clause subsumption calls : 273
% 0.18/0.41  # Rewrite failures with RHS unbound    : 0
% 0.18/0.41  # BW rewrite match attempts            : 135
% 0.18/0.41  # BW rewrite match successes           : 43
% 0.18/0.41  # Condensation attempts                : 0
% 0.18/0.41  # Condensation successes               : 0
% 0.18/0.41  # Termbank termtop insertions          : 47234
% 0.18/0.41  
% 0.18/0.41  # -------------------------------------------------
% 0.18/0.41  # User time                : 0.071 s
% 0.18/0.41  # System time              : 0.004 s
% 0.18/0.41  # Total time               : 0.076 s
% 0.18/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
