%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:52 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 170 expanded)
%              Number of clauses        :   44 (  74 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 320 expanded)
%              Number of equality atoms :   23 (  76 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
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

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

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

fof(c_0_15,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k7_subset_1(X22,X23,X24) = k4_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_17,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_struct_0(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))
      | ~ r1_tarski(X31,X30)
      | m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_tops_2])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | k5_setfam_1(X25,X26) = k3_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,k2_xboole_0(X9,X10))
      | r1_tarski(k4_xboole_0(X8,X9),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_25,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_28,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_30,plain,(
    ! [X19,X20] : k3_tarski(k2_xboole_0(X19,X20)) = k2_xboole_0(k3_tarski(X19),k3_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_23])])).

fof(c_0_32,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X11,X12] : r1_tarski(X11,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_31]),c_0_23])])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_20])])).

cnf(c_0_44,plain,
    ( k3_tarski(k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k3_tarski(X1),k3_tarski(X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_34]),c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_tarski(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_19])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(X3))
    | ~ r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k3_tarski(k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_28])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(k4_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_42])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(k3_tarski(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55]),c_0_58])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_64,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(k3_tarski(X17),k3_tarski(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_65,plain,(
    ! [X21] : k3_tarski(k1_zfmisc_1(X21)) = X21 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_67,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_62])).

cnf(c_0_70,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:16:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.42/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.42/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.42/0.58  #
% 0.42/0.58  # Preprocessing time       : 0.027 s
% 0.42/0.58  # Presaturation interreduction done
% 0.42/0.58  
% 0.42/0.58  # Proof found!
% 0.42/0.58  # SZS status Theorem
% 0.42/0.58  # SZS output start CNFRefutation
% 0.42/0.58  fof(t6_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 0.42/0.58  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.42/0.58  fof(t3_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(r1_tarski(X3,X2)=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 0.42/0.58  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.42/0.58  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.42/0.58  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.42/0.58  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.42/0.58  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 0.42/0.58  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.42/0.58  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.42/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.42/0.58  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.42/0.58  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.42/0.58  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.42/0.58  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_tops_2])).
% 0.42/0.58  fof(c_0_15, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.42/0.58  fof(c_0_16, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k7_subset_1(X22,X23,X24)=k4_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.42/0.58  fof(c_0_17, plain, ![X29, X30, X31]:(~l1_struct_0(X29)|(~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))|(~r1_tarski(X31,X30)|m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_tops_2])])])).
% 0.42/0.58  cnf(c_0_18, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.58  cnf(c_0_19, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.58  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.58  fof(c_0_21, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))|k5_setfam_1(X25,X26)=k3_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.42/0.58  cnf(c_0_22, plain, (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.58  cnf(c_0_23, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.58  fof(c_0_24, plain, ![X8, X9, X10]:(~r1_tarski(X8,k2_xboole_0(X9,X10))|r1_tarski(k4_xboole_0(X8,X9),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.42/0.58  fof(c_0_25, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.42/0.58  fof(c_0_26, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.42/0.58  cnf(c_0_27, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.42/0.58  cnf(c_0_28, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.58  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.58  fof(c_0_30, plain, ![X19, X20]:k3_tarski(k2_xboole_0(X19,X20))=k2_xboole_0(k3_tarski(X19),k3_tarski(X20)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 0.42/0.58  cnf(c_0_31, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_23])])).
% 0.42/0.58  fof(c_0_32, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.42/0.58  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  cnf(c_0_34, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.58  cnf(c_0_35, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.42/0.58  cnf(c_0_36, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.42/0.58  cnf(c_0_37, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.42/0.58  fof(c_0_38, plain, ![X11, X12]:r1_tarski(X11,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.42/0.58  cnf(c_0_39, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_31]), c_0_23])])).
% 0.42/0.58  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.42/0.58  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.42/0.58  cnf(c_0_42, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_34]), c_0_34])).
% 0.42/0.58  cnf(c_0_43, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_20])])).
% 0.42/0.58  cnf(c_0_44, plain, (k3_tarski(k3_tarski(k2_tarski(X1,X2)))=k3_tarski(k2_tarski(k3_tarski(X1),k3_tarski(X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_34]), c_0_34])).
% 0.42/0.58  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.42/0.58  fof(c_0_46, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.42/0.58  cnf(c_0_47, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.42/0.58  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.42/0.58  fof(c_0_49, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_tarski(X14,X13), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.42/0.58  cnf(c_0_50, negated_conjecture, (~m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_43, c_0_19])).
% 0.42/0.58  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(X3))|~r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 0.42/0.58  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_45, c_0_34])).
% 0.42/0.58  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.42/0.58  cnf(c_0_54, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,esk2_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.42/0.58  cnf(c_0_55, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.42/0.58  cnf(c_0_56, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k3_tarski(k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_50, c_0_28])).
% 0.42/0.58  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(k4_xboole_0(X3,X2)))|~r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_51, c_0_42])).
% 0.42/0.58  cnf(c_0_58, plain, (r1_tarski(k3_tarski(X1),k3_tarski(k3_tarski(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_44])).
% 0.42/0.58  cnf(c_0_59, negated_conjecture, (r1_tarski(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,esk2_0)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.58  cnf(c_0_60, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_52, c_0_55])).
% 0.42/0.58  cnf(c_0_61, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_55]), c_0_58])])).
% 0.42/0.58  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.42/0.58  cnf(c_0_63, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.42/0.58  fof(c_0_64, plain, ![X17, X18]:(~r1_tarski(X17,X18)|r1_tarski(k3_tarski(X17),k3_tarski(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.42/0.58  fof(c_0_65, plain, ![X21]:k3_tarski(k1_zfmisc_1(X21))=X21, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.42/0.58  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.42/0.58  cnf(c_0_67, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.42/0.58  cnf(c_0_68, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.42/0.58  cnf(c_0_69, negated_conjecture, (~r1_tarski(k3_tarski(esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_66, c_0_62])).
% 0.42/0.58  cnf(c_0_70, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.42/0.58  cnf(c_0_71, negated_conjecture, (r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_53, c_0_20])).
% 0.42/0.58  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), ['proof']).
% 0.42/0.58  # SZS output end CNFRefutation
% 0.42/0.58  # Proof object total steps             : 73
% 0.42/0.58  # Proof object clause steps            : 44
% 0.42/0.58  # Proof object formula steps           : 29
% 0.42/0.58  # Proof object conjectures             : 23
% 0.42/0.58  # Proof object clause conjectures      : 20
% 0.42/0.58  # Proof object formula conjectures     : 3
% 0.42/0.58  # Proof object initial clauses used    : 18
% 0.42/0.58  # Proof object initial formulas used   : 14
% 0.42/0.58  # Proof object generating inferences   : 22
% 0.42/0.58  # Proof object simplifying inferences  : 23
% 0.42/0.58  # Training examples: 0 positive, 0 negative
% 0.42/0.58  # Parsed axioms                        : 14
% 0.42/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.58  # Initial clauses                      : 18
% 0.42/0.58  # Removed in clause preprocessing      : 1
% 0.42/0.58  # Initial clauses in saturation        : 17
% 0.42/0.58  # Processed clauses                    : 1539
% 0.42/0.58  # ...of these trivial                  : 111
% 0.42/0.58  # ...subsumed                          : 644
% 0.42/0.58  # ...remaining for further processing  : 784
% 0.42/0.58  # Other redundant clauses eliminated   : 0
% 0.42/0.58  # Clauses deleted for lack of memory   : 0
% 0.42/0.58  # Backward-subsumed                    : 20
% 0.42/0.58  # Backward-rewritten                   : 6
% 0.42/0.58  # Generated clauses                    : 13232
% 0.42/0.58  # ...of the previous two non-trivial   : 12573
% 0.42/0.58  # Contextual simplify-reflections      : 0
% 0.42/0.58  # Paramodulations                      : 13232
% 0.42/0.58  # Factorizations                       : 0
% 0.42/0.58  # Equation resolutions                 : 0
% 0.42/0.58  # Propositional unsat checks           : 0
% 0.42/0.58  #    Propositional check models        : 0
% 0.42/0.58  #    Propositional check unsatisfiable : 0
% 0.42/0.58  #    Propositional clauses             : 0
% 0.42/0.58  #    Propositional clauses after purity: 0
% 0.42/0.58  #    Propositional unsat core size     : 0
% 0.42/0.58  #    Propositional preprocessing time  : 0.000
% 0.42/0.58  #    Propositional encoding time       : 0.000
% 0.42/0.58  #    Propositional solver time         : 0.000
% 0.42/0.58  #    Success case prop preproc time    : 0.000
% 0.42/0.58  #    Success case prop encoding time   : 0.000
% 0.42/0.58  #    Success case prop solver time     : 0.000
% 0.42/0.58  # Current number of processed clauses  : 741
% 0.42/0.58  #    Positive orientable unit clauses  : 129
% 0.42/0.58  #    Positive unorientable unit clauses: 1
% 0.42/0.58  #    Negative unit clauses             : 10
% 0.42/0.58  #    Non-unit-clauses                  : 601
% 0.42/0.58  # Current number of unprocessed clauses: 11052
% 0.42/0.58  # ...number of literals in the above   : 20882
% 0.42/0.58  # Current number of archived formulas  : 0
% 0.42/0.58  # Current number of archived clauses   : 44
% 0.42/0.58  # Clause-clause subsumption calls (NU) : 64040
% 0.42/0.58  # Rec. Clause-clause subsumption calls : 59068
% 0.42/0.58  # Non-unit clause-clause subsumptions  : 659
% 0.42/0.58  # Unit Clause-clause subsumption calls : 180
% 0.42/0.58  # Rewrite failures with RHS unbound    : 0
% 0.42/0.58  # BW rewrite match attempts            : 1340
% 0.42/0.58  # BW rewrite match successes           : 8
% 0.42/0.58  # Condensation attempts                : 0
% 0.42/0.58  # Condensation successes               : 0
% 0.42/0.58  # Termbank termtop insertions          : 312499
% 0.42/0.58  
% 0.42/0.58  # -------------------------------------------------
% 0.42/0.58  # User time                : 0.235 s
% 0.42/0.58  # System time              : 0.015 s
% 0.42/0.58  # Total time               : 0.250 s
% 0.42/0.58  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
