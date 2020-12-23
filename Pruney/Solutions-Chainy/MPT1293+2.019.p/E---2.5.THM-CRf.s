%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:54 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 123 expanded)
%              Number of clauses        :   38 (  52 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 237 expanded)
%              Number of equality atoms :   27 (  57 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t3_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( r1_tarski(X3,X2)
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tops_2])).

fof(c_0_15,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | k5_setfam_1(X25,X26) = k3_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_16,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_17,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1_0),esk3_0) = k3_tarski(esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1_0),esk2_0) = k3_tarski(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k7_subset_1(X22,X23,X24) = k4_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_struct_0(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))
      | ~ r1_tarski(X31,X30)
      | m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_tops_2])])])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,k2_xboole_0(X11,X12))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_26,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X19,X20] : k3_tarski(k2_xboole_0(X19,X20)) = k2_xboole_0(k3_tarski(X19),k3_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_29,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_31])])).

fof(c_0_37,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k3_tarski(k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k3_tarski(X1),k3_tarski(X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_33]),c_0_33])).

fof(c_0_40,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(k3_tarski(X17),k3_tarski(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_41,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_42,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_43,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1_0),X1) = k3_tarski(X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(X3))
    | ~ r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k3_tarski(k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(X1),k3_tarski(X2)),k3_tarski(X3))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_33]),c_0_33])).

cnf(c_0_55,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_33]),c_0_33])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_33])).

fof(c_0_57,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_58,plain,(
    ! [X21] : k3_tarski(k1_zfmisc_1(X21)) = X21 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_19])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:35:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.76/0.92  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.76/0.92  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.76/0.92  #
% 0.76/0.92  # Preprocessing time       : 0.028 s
% 0.76/0.92  # Presaturation interreduction done
% 0.76/0.92  
% 0.76/0.92  # Proof found!
% 0.76/0.92  # SZS status Theorem
% 0.76/0.92  # SZS output start CNFRefutation
% 0.76/0.92  fof(t6_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 0.76/0.92  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.76/0.92  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.76/0.92  fof(t3_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(r1_tarski(X3,X2)=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 0.76/0.92  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.76/0.92  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.76/0.92  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 0.76/0.92  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.76/0.92  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.76/0.92  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.76/0.92  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.76/0.92  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.76/0.92  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.76/0.92  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.76/0.92  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_tops_2])).
% 0.76/0.92  fof(c_0_15, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))|k5_setfam_1(X25,X26)=k3_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.76/0.92  fof(c_0_16, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.76/0.92  cnf(c_0_17, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.76/0.92  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.76/0.92  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.76/0.92  cnf(c_0_20, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.76/0.92  cnf(c_0_21, negated_conjecture, (k5_setfam_1(u1_struct_0(esk1_0),esk3_0)=k3_tarski(esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.76/0.92  cnf(c_0_22, negated_conjecture, (k5_setfam_1(u1_struct_0(esk1_0),esk2_0)=k3_tarski(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 0.76/0.92  fof(c_0_23, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k7_subset_1(X22,X23,X24)=k4_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.76/0.92  fof(c_0_24, plain, ![X29, X30, X31]:(~l1_struct_0(X29)|(~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))|(~r1_tarski(X31,X30)|m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_tops_2])])])).
% 0.76/0.92  fof(c_0_25, plain, ![X10, X11, X12]:(~r1_tarski(X10,k2_xboole_0(X11,X12))|r1_tarski(k4_xboole_0(X10,X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.76/0.92  fof(c_0_26, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.76/0.92  fof(c_0_27, plain, ![X19, X20]:k3_tarski(k2_xboole_0(X19,X20))=k2_xboole_0(k3_tarski(X19),k3_tarski(X20)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 0.76/0.92  cnf(c_0_28, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.76/0.92  cnf(c_0_29, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.76/0.92  cnf(c_0_30, plain, (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.76/0.92  cnf(c_0_31, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.76/0.92  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.76/0.92  cnf(c_0_33, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.76/0.92  cnf(c_0_34, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.76/0.92  cnf(c_0_35, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])])).
% 0.76/0.92  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_31])])).
% 0.76/0.92  fof(c_0_37, plain, ![X6, X7]:r1_tarski(k4_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.76/0.92  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.76/0.92  cnf(c_0_39, plain, (k3_tarski(k3_tarski(k2_tarski(X1,X2)))=k3_tarski(k2_tarski(k3_tarski(X1),k3_tarski(X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_33]), c_0_33])).
% 0.76/0.92  fof(c_0_40, plain, ![X17, X18]:(~r1_tarski(X17,X18)|r1_tarski(k3_tarski(X17),k3_tarski(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.76/0.92  fof(c_0_41, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.76/0.92  fof(c_0_42, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.76/0.92  fof(c_0_43, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.76/0.92  cnf(c_0_44, negated_conjecture, (~m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 0.76/0.92  cnf(c_0_45, negated_conjecture, (k5_setfam_1(u1_struct_0(esk1_0),X1)=k3_tarski(X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_36])).
% 0.76/0.92  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.76/0.92  cnf(c_0_47, plain, (r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(X3))|~r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.76/0.92  cnf(c_0_48, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.76/0.92  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.76/0.92  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.76/0.92  cnf(c_0_51, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.76/0.92  cnf(c_0_52, negated_conjecture, (~m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k3_tarski(k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.76/0.92  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(k3_tarski(X1),k3_tarski(X2)),k3_tarski(X3))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.76/0.92  cnf(c_0_54, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_33]), c_0_33])).
% 0.76/0.92  cnf(c_0_55, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_33]), c_0_33])).
% 0.76/0.92  cnf(c_0_56, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_51, c_0_33])).
% 0.76/0.92  fof(c_0_57, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.76/0.92  fof(c_0_58, plain, ![X21]:k3_tarski(k1_zfmisc_1(X21))=X21, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.76/0.92  cnf(c_0_59, negated_conjecture, (~m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_56])])).
% 0.76/0.92  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.76/0.92  cnf(c_0_61, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.76/0.92  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.76/0.92  cnf(c_0_63, negated_conjecture, (~r1_tarski(k3_tarski(esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.76/0.92  cnf(c_0_64, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 0.76/0.92  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_62, c_0_19])).
% 0.76/0.92  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])]), ['proof']).
% 0.76/0.92  # SZS output end CNFRefutation
% 0.76/0.92  # Proof object total steps             : 67
% 0.76/0.92  # Proof object clause steps            : 38
% 0.76/0.92  # Proof object formula steps           : 29
% 0.76/0.92  # Proof object conjectures             : 19
% 0.76/0.92  # Proof object clause conjectures      : 16
% 0.76/0.92  # Proof object formula conjectures     : 3
% 0.76/0.92  # Proof object initial clauses used    : 18
% 0.76/0.92  # Proof object initial formulas used   : 14
% 0.76/0.92  # Proof object generating inferences   : 14
% 0.76/0.92  # Proof object simplifying inferences  : 22
% 0.76/0.92  # Training examples: 0 positive, 0 negative
% 0.76/0.92  # Parsed axioms                        : 14
% 0.76/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.76/0.92  # Initial clauses                      : 18
% 0.76/0.92  # Removed in clause preprocessing      : 1
% 0.76/0.92  # Initial clauses in saturation        : 17
% 0.76/0.92  # Processed clauses                    : 2992
% 0.76/0.92  # ...of these trivial                  : 289
% 0.76/0.92  # ...subsumed                          : 1086
% 0.76/0.92  # ...remaining for further processing  : 1617
% 0.76/0.92  # Other redundant clauses eliminated   : 0
% 0.76/0.92  # Clauses deleted for lack of memory   : 0
% 0.76/0.92  # Backward-subsumed                    : 37
% 0.76/0.92  # Backward-rewritten                   : 13
% 0.76/0.92  # Generated clauses                    : 45636
% 0.76/0.92  # ...of the previous two non-trivial   : 44355
% 0.76/0.92  # Contextual simplify-reflections      : 0
% 0.76/0.92  # Paramodulations                      : 45636
% 0.76/0.92  # Factorizations                       : 0
% 0.76/0.92  # Equation resolutions                 : 0
% 0.76/0.92  # Propositional unsat checks           : 0
% 0.76/0.92  #    Propositional check models        : 0
% 0.76/0.92  #    Propositional check unsatisfiable : 0
% 0.76/0.92  #    Propositional clauses             : 0
% 0.76/0.92  #    Propositional clauses after purity: 0
% 0.76/0.92  #    Propositional unsat core size     : 0
% 0.76/0.92  #    Propositional preprocessing time  : 0.000
% 0.76/0.92  #    Propositional encoding time       : 0.000
% 0.76/0.92  #    Propositional solver time         : 0.000
% 0.76/0.92  #    Success case prop preproc time    : 0.000
% 0.76/0.92  #    Success case prop encoding time   : 0.000
% 0.76/0.92  #    Success case prop solver time     : 0.000
% 0.76/0.92  # Current number of processed clauses  : 1550
% 0.76/0.92  #    Positive orientable unit clauses  : 220
% 0.76/0.92  #    Positive unorientable unit clauses: 5
% 0.76/0.92  #    Negative unit clauses             : 5
% 0.76/0.92  #    Non-unit-clauses                  : 1320
% 0.76/0.92  # Current number of unprocessed clauses: 41370
% 0.76/0.92  # ...number of literals in the above   : 80950
% 0.76/0.92  # Current number of archived formulas  : 0
% 0.76/0.92  # Current number of archived clauses   : 68
% 0.76/0.92  # Clause-clause subsumption calls (NU) : 110148
% 0.76/0.92  # Rec. Clause-clause subsumption calls : 106586
% 0.76/0.92  # Non-unit clause-clause subsumptions  : 1103
% 0.76/0.92  # Unit Clause-clause subsumption calls : 230
% 0.76/0.92  # Rewrite failures with RHS unbound    : 0
% 0.76/0.92  # BW rewrite match attempts            : 2296
% 0.76/0.92  # BW rewrite match successes           : 45
% 0.76/0.92  # Condensation attempts                : 0
% 0.76/0.92  # Condensation successes               : 0
% 0.76/0.92  # Termbank termtop insertions          : 1032391
% 0.76/0.93  
% 0.76/0.93  # -------------------------------------------------
% 0.76/0.93  # User time                : 0.546 s
% 0.76/0.93  # System time              : 0.032 s
% 0.76/0.93  # Total time               : 0.578 s
% 0.76/0.93  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
