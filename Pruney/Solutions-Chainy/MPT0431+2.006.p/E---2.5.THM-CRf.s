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
% DateTime   : Thu Dec  3 10:48:06 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 113 expanded)
%              Number of clauses        :   35 (  46 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  144 ( 331 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_setfam_1)).

fof(t5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(X1,X2)
        & r2_hidden(X3,k2_xboole_0(X1,X2))
        & ~ ( r2_hidden(X3,X1)
            & ~ r2_hidden(X3,X2) )
        & ~ ( r2_hidden(X3,X2)
            & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d13_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v3_setfam_1(X2,X1)
      <=> ~ r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_13,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
      | k4_subset_1(X25,X26,X27) = k2_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_14,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X13,X14] : k2_enumset1(X13,X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X6,X7,X8] :
      ( ( r2_hidden(X8,X7)
        | r2_hidden(X8,X6)
        | ~ r1_xboole_0(X6,X7)
        | ~ r2_hidden(X8,k2_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X6)
        | ~ r1_xboole_0(X6,X7)
        | ~ r2_hidden(X8,k2_xboole_0(X6,X7)) )
      & ( r2_hidden(X8,X7)
        | ~ r2_hidden(X8,X7)
        | ~ r1_xboole_0(X6,X7)
        | ~ r2_hidden(X8,k2_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | ~ r1_xboole_0(X6,X7)
        | ~ r2_hidden(X8,k2_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).

fof(c_0_18,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_19,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_20,plain,(
    ! [X11,X12] : r1_xboole_0(k4_xboole_0(X11,X12),X12) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_21,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v3_setfam_1(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & v3_setfam_1(esk3_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_25,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | m1_subset_1(k4_subset_1(X17,X18,X19),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_enumset1(X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X20,X21] : m1_subset_1(k6_subset_1(X20,X21),k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_34,plain,(
    ! [X28,X29] : k6_subset_1(X28,X29) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X2)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_23])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k3_tarski(k2_enumset1(X1,X1,X1,esk3_0)) = k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_40,plain,(
    ! [X30,X31] :
      ( ( ~ v3_setfam_1(X31,X30)
        | ~ r2_hidden(X30,X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30))) )
      & ( r2_hidden(X30,X31)
        | v3_setfam_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_42,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ r2_hidden(X24,X23)
      | r2_hidden(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_46,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)) = k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | v3_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,plain,
    ( ~ v3_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v3_setfam_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k4_xboole_0(esk3_0,esk2_0))
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_0,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( v3_setfam_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.43/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.43/0.59  # and selection function SelectLComplex.
% 0.43/0.59  #
% 0.43/0.59  # Preprocessing time       : 0.027 s
% 0.43/0.59  # Presaturation interreduction done
% 0.43/0.59  
% 0.43/0.59  # Proof found!
% 0.43/0.59  # SZS status Theorem
% 0.43/0.59  # SZS output start CNFRefutation
% 0.43/0.59  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.43/0.59  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.43/0.59  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.43/0.59  fof(t63_setfam_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_setfam_1)).
% 0.43/0.59  fof(t5_xboole_0, axiom, ![X1, X2, X3]:~((((r1_xboole_0(X1,X2)&r2_hidden(X3,k2_xboole_0(X1,X2)))&~((r2_hidden(X3,X1)&~(r2_hidden(X3,X2)))))&~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 0.43/0.59  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.43/0.59  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.43/0.59  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.43/0.59  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.43/0.59  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.43/0.59  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.43/0.59  fof(d13_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v3_setfam_1(X2,X1)<=>~(r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 0.43/0.59  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.43/0.59  fof(c_0_13, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|~m1_subset_1(X27,k1_zfmisc_1(X25))|k4_subset_1(X25,X26,X27)=k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.43/0.59  fof(c_0_14, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.43/0.59  fof(c_0_15, plain, ![X13, X14]:k2_enumset1(X13,X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.43/0.59  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1))))), inference(assume_negation,[status(cth)],[t63_setfam_1])).
% 0.43/0.59  fof(c_0_17, plain, ![X6, X7, X8]:(((r2_hidden(X8,X7)|(r2_hidden(X8,X6)|(~r1_xboole_0(X6,X7)|~r2_hidden(X8,k2_xboole_0(X6,X7)))))&(~r2_hidden(X8,X6)|(r2_hidden(X8,X6)|(~r1_xboole_0(X6,X7)|~r2_hidden(X8,k2_xboole_0(X6,X7))))))&((r2_hidden(X8,X7)|(~r2_hidden(X8,X7)|(~r1_xboole_0(X6,X7)|~r2_hidden(X8,k2_xboole_0(X6,X7)))))&(~r2_hidden(X8,X6)|(~r2_hidden(X8,X7)|(~r1_xboole_0(X6,X7)|~r2_hidden(X8,k2_xboole_0(X6,X7))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).
% 0.43/0.59  fof(c_0_18, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.43/0.59  fof(c_0_19, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.43/0.59  fof(c_0_20, plain, ![X11, X12]:r1_xboole_0(k4_xboole_0(X11,X12),X12), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.43/0.59  cnf(c_0_21, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.43/0.59  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.59  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.43/0.59  fof(c_0_24, negated_conjecture, (~v1_xboole_0(esk1_0)&((v3_setfam_1(esk2_0,esk1_0)&m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))))&((v3_setfam_1(esk3_0,esk1_0)&m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))))&~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.43/0.59  fof(c_0_25, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|~m1_subset_1(X19,k1_zfmisc_1(X17))|m1_subset_1(k4_subset_1(X17,X18,X19),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.43/0.59  cnf(c_0_26, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.43/0.59  cnf(c_0_27, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.43/0.59  cnf(c_0_28, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.43/0.59  cnf(c_0_29, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.43/0.59  cnf(c_0_30, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_enumset1(X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.43/0.59  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.43/0.59  cnf(c_0_32, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.43/0.59  fof(c_0_33, plain, ![X20, X21]:m1_subset_1(k6_subset_1(X20,X21),k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.43/0.59  fof(c_0_34, plain, ![X28, X29]:k6_subset_1(X28,X29)=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.43/0.59  cnf(c_0_35, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X2)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_23])).
% 0.43/0.59  cnf(c_0_36, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.43/0.59  cnf(c_0_37, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.43/0.59  cnf(c_0_38, negated_conjecture, (k3_tarski(k2_enumset1(X1,X1,X1,esk3_0))=k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.43/0.59  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.43/0.59  fof(c_0_40, plain, ![X30, X31]:((~v3_setfam_1(X31,X30)|~r2_hidden(X30,X31)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30))))&(r2_hidden(X30,X31)|v3_setfam_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).
% 0.43/0.59  cnf(c_0_41, negated_conjecture, (m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),X1,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.43/0.59  fof(c_0_42, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~r2_hidden(X24,X23)|r2_hidden(X24,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.43/0.59  cnf(c_0_43, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.43/0.59  cnf(c_0_44, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.43/0.59  cnf(c_0_45, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.43/0.59  cnf(c_0_46, negated_conjecture, (k3_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))=k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.43/0.59  cnf(c_0_47, plain, (r2_hidden(X1,X2)|v3_setfam_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.43/0.59  cnf(c_0_48, negated_conjecture, (m1_subset_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 0.43/0.59  cnf(c_0_49, negated_conjecture, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.43/0.59  cnf(c_0_50, plain, (~v3_setfam_1(X1,X2)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.43/0.59  cnf(c_0_51, negated_conjecture, (v3_setfam_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.43/0.59  cnf(c_0_52, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.43/0.59  cnf(c_0_53, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.43/0.59  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k4_xboole_0(esk3_0,esk2_0))|r2_hidden(X1,esk2_0)|~r2_hidden(X1,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.43/0.59  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_0,k4_subset_1(k1_zfmisc_1(esk1_0),esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.43/0.59  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_39]), c_0_51])])).
% 0.43/0.59  cnf(c_0_57, negated_conjecture, (v3_setfam_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.43/0.59  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.43/0.59  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_0,k4_xboole_0(esk3_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.43/0.59  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_57])])).
% 0.43/0.59  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), ['proof']).
% 0.43/0.59  # SZS output end CNFRefutation
% 0.43/0.59  # Proof object total steps             : 62
% 0.43/0.59  # Proof object clause steps            : 35
% 0.43/0.59  # Proof object formula steps           : 27
% 0.43/0.59  # Proof object conjectures             : 18
% 0.43/0.59  # Proof object clause conjectures      : 15
% 0.43/0.59  # Proof object formula conjectures     : 3
% 0.43/0.59  # Proof object initial clauses used    : 18
% 0.43/0.59  # Proof object initial formulas used   : 13
% 0.43/0.59  # Proof object generating inferences   : 13
% 0.43/0.59  # Proof object simplifying inferences  : 18
% 0.43/0.59  # Training examples: 0 positive, 0 negative
% 0.43/0.59  # Parsed axioms                        : 13
% 0.43/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.59  # Initial clauses                      : 22
% 0.43/0.59  # Removed in clause preprocessing      : 5
% 0.43/0.59  # Initial clauses in saturation        : 17
% 0.43/0.59  # Processed clauses                    : 716
% 0.43/0.59  # ...of these trivial                  : 0
% 0.43/0.59  # ...subsumed                          : 4
% 0.43/0.59  # ...remaining for further processing  : 712
% 0.43/0.59  # Other redundant clauses eliminated   : 0
% 0.43/0.59  # Clauses deleted for lack of memory   : 0
% 0.43/0.59  # Backward-subsumed                    : 2
% 0.43/0.59  # Backward-rewritten                   : 2
% 0.43/0.59  # Generated clauses                    : 10887
% 0.43/0.59  # ...of the previous two non-trivial   : 10872
% 0.43/0.59  # Contextual simplify-reflections      : 5
% 0.43/0.59  # Paramodulations                      : 10887
% 0.43/0.59  # Factorizations                       : 0
% 0.43/0.59  # Equation resolutions                 : 0
% 0.43/0.59  # Propositional unsat checks           : 0
% 0.43/0.59  #    Propositional check models        : 0
% 0.43/0.59  #    Propositional check unsatisfiable : 0
% 0.43/0.59  #    Propositional clauses             : 0
% 0.43/0.59  #    Propositional clauses after purity: 0
% 0.43/0.59  #    Propositional unsat core size     : 0
% 0.43/0.59  #    Propositional preprocessing time  : 0.000
% 0.43/0.59  #    Propositional encoding time       : 0.000
% 0.43/0.59  #    Propositional solver time         : 0.000
% 0.43/0.59  #    Success case prop preproc time    : 0.000
% 0.43/0.59  #    Success case prop encoding time   : 0.000
% 0.43/0.59  #    Success case prop solver time     : 0.000
% 0.43/0.59  # Current number of processed clauses  : 691
% 0.43/0.59  #    Positive orientable unit clauses  : 290
% 0.43/0.59  #    Positive unorientable unit clauses: 0
% 0.43/0.59  #    Negative unit clauses             : 4
% 0.43/0.59  #    Non-unit-clauses                  : 397
% 0.43/0.59  # Current number of unprocessed clauses: 10189
% 0.43/0.59  # ...number of literals in the above   : 11234
% 0.43/0.59  # Current number of archived formulas  : 0
% 0.43/0.59  # Current number of archived clauses   : 24
% 0.43/0.59  # Clause-clause subsumption calls (NU) : 54719
% 0.43/0.59  # Rec. Clause-clause subsumption calls : 50669
% 0.43/0.59  # Non-unit clause-clause subsumptions  : 8
% 0.43/0.59  # Unit Clause-clause subsumption calls : 505
% 0.43/0.59  # Rewrite failures with RHS unbound    : 0
% 0.43/0.59  # BW rewrite match attempts            : 25959
% 0.43/0.59  # BW rewrite match successes           : 2
% 0.43/0.59  # Condensation attempts                : 0
% 0.43/0.59  # Condensation successes               : 0
% 0.43/0.59  # Termbank termtop insertions          : 560428
% 0.43/0.59  
% 0.43/0.59  # -------------------------------------------------
% 0.43/0.59  # User time                : 0.232 s
% 0.43/0.59  # System time              : 0.017 s
% 0.43/0.59  # Total time               : 0.248 s
% 0.43/0.59  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
