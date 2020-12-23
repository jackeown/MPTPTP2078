%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:51 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 283 expanded)
%              Number of clauses        :   42 ( 119 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 847 expanded)
%              Number of equality atoms :   47 ( 205 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_12,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26)))
      | k6_setfam_1(X26,X27) = k1_setfam_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | X30 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X31),k1_setfam_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ( X23 = k1_xboole_0
        | k8_setfam_1(X22,X23) = k6_setfam_1(X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) )
      & ( X23 != k1_xboole_0
        | k8_setfam_1(X22,X23) = X22
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_16,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k6_setfam_1(esk3_0,esk4_0) = k1_setfam_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k1_setfam_1(esk4_0) = k8_setfam_1(esk3_0,esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k6_setfam_1(esk3_0,esk5_0) = k1_setfam_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k1_setfam_1(esk5_0) = k8_setfam_1(esk3_0,esk5_0)
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_22]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | m1_subset_1(k8_setfam_1(X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

fof(c_0_30,plain,(
    ! [X19] :
      ( ( r1_xboole_0(X19,X19)
        | X19 != k1_xboole_0 )
      & ( X19 = k1_xboole_0
        | ~ r1_xboole_0(X19,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_31,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_33,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk2_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_38,plain,(
    ! [X20,X21] :
      ( v1_xboole_0(X21)
      | ~ r1_tarski(X21,X20)
      | ~ r1_xboole_0(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_39,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k8_setfam_1(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( k8_setfam_1(esk3_0,k1_xboole_0) = esk3_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k8_setfam_1(esk3_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_46])).

fof(c_0_57,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk3_0,k1_xboole_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n019.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 17:25:37 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.31  # No SInE strategy applied
% 0.10/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.16/0.34  # and selection function SelectNewComplexAHP.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.028 s
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t59_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 0.16/0.34  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.16/0.34  fof(t7_setfam_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.16/0.34  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.16/0.34  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 0.16/0.34  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.16/0.34  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.16/0.34  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.16/0.34  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.16/0.34  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.16/0.34  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.34  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t59_setfam_1])).
% 0.16/0.34  fof(c_0_12, plain, ![X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26)))|k6_setfam_1(X26,X27)=k1_setfam_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.16/0.34  fof(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(r1_tarski(esk4_0,esk5_0)&~r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.16/0.34  fof(c_0_14, plain, ![X30, X31]:(~r1_tarski(X30,X31)|(X30=k1_xboole_0|r1_tarski(k1_setfam_1(X31),k1_setfam_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).
% 0.16/0.34  fof(c_0_15, plain, ![X22, X23]:((X23=k1_xboole_0|k8_setfam_1(X22,X23)=k6_setfam_1(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))))&(X23!=k1_xboole_0|k8_setfam_1(X22,X23)=X22|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.16/0.34  cnf(c_0_16, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.34  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.34  cnf(c_0_18, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.34  cnf(c_0_20, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.34  cnf(c_0_21, negated_conjecture, (k6_setfam_1(esk3_0,esk4_0)=k1_setfam_1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.16/0.34  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.34  cnf(c_0_23, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.16/0.34  cnf(c_0_24, negated_conjecture, (k1_setfam_1(esk4_0)=k8_setfam_1(esk3_0,esk4_0)|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_21])).
% 0.16/0.34  cnf(c_0_25, negated_conjecture, (k6_setfam_1(esk3_0,esk5_0)=k1_setfam_1(esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_22])).
% 0.16/0.34  cnf(c_0_26, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk5_0),k8_setfam_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.16/0.34  cnf(c_0_27, negated_conjecture, (k1_setfam_1(esk5_0)=k8_setfam_1(esk3_0,esk5_0)|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_22]), c_0_25])).
% 0.16/0.34  cnf(c_0_28, negated_conjecture, (~r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.34  fof(c_0_29, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))|m1_subset_1(k8_setfam_1(X24,X25),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 0.16/0.34  fof(c_0_30, plain, ![X19]:((r1_xboole_0(X19,X19)|X19!=k1_xboole_0)&(X19=k1_xboole_0|~r1_xboole_0(X19,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.16/0.34  cnf(c_0_31, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.34  cnf(c_0_32, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.16/0.34  fof(c_0_33, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.16/0.34  cnf(c_0_34, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.16/0.34  fof(c_0_35, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk2_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk2_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.16/0.34  cnf(c_0_36, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.34  fof(c_0_37, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.16/0.34  fof(c_0_38, plain, ![X20, X21]:(v1_xboole_0(X21)|(~r1_tarski(X21,X20)|~r1_xboole_0(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.16/0.34  cnf(c_0_39, plain, (k8_setfam_1(X1,k1_xboole_0)=X1|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(er,[status(thm)],[c_0_31])).
% 0.16/0.34  cnf(c_0_40, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(spm,[status(thm)],[c_0_17, c_0_32])).
% 0.16/0.34  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.16/0.34  cnf(c_0_42, negated_conjecture, (m1_subset_1(k8_setfam_1(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 0.16/0.34  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.34  cnf(c_0_44, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_36])).
% 0.16/0.34  cnf(c_0_45, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.34  cnf(c_0_46, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.34  cnf(c_0_47, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.16/0.34  cnf(c_0_48, negated_conjecture, (esk5_0=k1_xboole_0|~r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_28, c_0_32])).
% 0.16/0.34  cnf(c_0_49, negated_conjecture, (k8_setfam_1(esk3_0,k1_xboole_0)=esk3_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.16/0.34  cnf(c_0_50, negated_conjecture, (r1_tarski(k8_setfam_1(esk3_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.16/0.34  cnf(c_0_51, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.16/0.34  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.34  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.16/0.34  cnf(c_0_54, negated_conjecture, (v1_xboole_0(esk4_0)|~r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_19])).
% 0.16/0.34  cnf(c_0_55, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.16/0.34  cnf(c_0_56, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_46])).
% 0.16/0.34  fof(c_0_57, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.34  cnf(c_0_58, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.16/0.34  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.16/0.34  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.16/0.34  cnf(c_0_61, negated_conjecture, (~r1_tarski(k8_setfam_1(esk3_0,k1_xboole_0),k8_setfam_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_28, c_0_55])).
% 0.16/0.34  cnf(c_0_62, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.16/0.34  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.16/0.34  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63])]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 65
% 0.16/0.34  # Proof object clause steps            : 42
% 0.16/0.34  # Proof object formula steps           : 23
% 0.16/0.34  # Proof object conjectures             : 25
% 0.16/0.34  # Proof object clause conjectures      : 22
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 17
% 0.16/0.34  # Proof object initial formulas used   : 11
% 0.16/0.34  # Proof object generating inferences   : 21
% 0.16/0.34  # Proof object simplifying inferences  : 13
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 12
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 23
% 0.16/0.34  # Removed in clause preprocessing      : 0
% 0.16/0.34  # Initial clauses in saturation        : 23
% 0.16/0.34  # Processed clauses                    : 111
% 0.16/0.34  # ...of these trivial                  : 2
% 0.16/0.34  # ...subsumed                          : 10
% 0.16/0.34  # ...remaining for further processing  : 99
% 0.16/0.34  # Other redundant clauses eliminated   : 2
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 0
% 0.16/0.34  # Backward-rewritten                   : 57
% 0.16/0.34  # Generated clauses                    : 179
% 0.16/0.34  # ...of the previous two non-trivial   : 167
% 0.16/0.34  # Contextual simplify-reflections      : 0
% 0.16/0.34  # Paramodulations                      : 175
% 0.16/0.34  # Factorizations                       : 0
% 0.16/0.34  # Equation resolutions                 : 4
% 0.16/0.34  # Propositional unsat checks           : 0
% 0.16/0.34  #    Propositional check models        : 0
% 0.16/0.34  #    Propositional check unsatisfiable : 0
% 0.16/0.34  #    Propositional clauses             : 0
% 0.16/0.34  #    Propositional clauses after purity: 0
% 0.16/0.34  #    Propositional unsat core size     : 0
% 0.16/0.34  #    Propositional preprocessing time  : 0.000
% 0.16/0.34  #    Propositional encoding time       : 0.000
% 0.16/0.34  #    Propositional solver time         : 0.000
% 0.16/0.34  #    Success case prop preproc time    : 0.000
% 0.16/0.34  #    Success case prop encoding time   : 0.000
% 0.16/0.34  #    Success case prop solver time     : 0.000
% 0.16/0.34  # Current number of processed clauses  : 40
% 0.16/0.34  #    Positive orientable unit clauses  : 11
% 0.16/0.34  #    Positive unorientable unit clauses: 0
% 0.16/0.34  #    Negative unit clauses             : 1
% 0.16/0.34  #    Non-unit-clauses                  : 28
% 0.16/0.34  # Current number of unprocessed clauses: 79
% 0.16/0.34  # ...number of literals in the above   : 176
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 57
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 251
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 240
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 8
% 0.16/0.34  # Unit Clause-clause subsumption calls : 58
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 17
% 0.16/0.34  # BW rewrite match successes           : 5
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 3379
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.035 s
% 0.16/0.34  # System time              : 0.002 s
% 0.16/0.34  # Total time               : 0.037 s
% 0.16/0.34  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
